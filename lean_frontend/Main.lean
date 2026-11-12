import CerberusImpl
import CerbMem
import CerbCtypeInstances
import CerbCabsInstances
import CabsImport
import CoreParser
import Cabs_to_ail
import Cn_desugaring
import Implementation
import GenTyping
import Translation
import Core_run_aux
import Driver
import CerbND
import CerbEscape
-- the `--call` mode's entry (CerbCall.driveCall): `drive` started at a
-- designated function with injected arguments — a port-side harness
-- entry over the generated driver (see CerbCall.lean's header)
import CerbCall
import CoreLeanSource
import RunLinked

set_option autoImplicit true

/-! ## Core stdlib loading -/

/-- Convert a CoreParser.CoreFile from std.core into the tuple the
    desugarer expects: (ailnames, stdlib_fun_map, impl).

    Mirrors `load_core_stdlib` (backend/common/pipeline.ml:32-44) returning
    `Rstd (ailnames, std_funs)` from the StdMode core parser
    (core_parser.mly:1076-1080): the ailnames map is C-name → proxy symbol,
    built EXCLUSIVELY from `[ailname = "..."]` attributes on proc
    declarations (`register_ailname`, core_parser.mly:157-159, invoked only
    at Proc_decl symbolification :1037-1041) — 46 entries for the shipped
    std.core. Declaration names must NOT be keys: translation looks up the
    C identifier (e.g. "malloc", "__builtin_ffs") in this map and
    substitutes the proxy symbol at the call site
    (translation.lem:244-251); keying by declaration name both misses
    every C name AND mis-binds "printf" to the `builtin printf`
    declaration (std.core:283) instead of `printf_proxy` (std.core:289).

    The fun_map keeps ALL declarations (fun + proc + builtin), matching
    symbolify_std (core_parser.mly:1010-1046: Fun/Proc/BuiltinDecl entries).
    CoreParser.mkSym assigns hash-based IDs per string, so all calls to the
    same-named function end up with the same symbol — no renumbering. -/
def loadCoreStdlib (stdFile : CoreParser.CoreFile) :
    Fmap String sym × fun_map Unit :=
  let allDecls := stdFile.funs ++ stdFile.procs ++ stdFile.builtins
  -- Duplicate-key divergence (arc-5 audit 2, F4, documented-deliberate):
  -- Lem_Map.fromList is a foldl of fmapAdd, so on duplicate ailnames the
  -- LAST-in-file entry wins; OCaml's foldrM registration
  -- (core_parser.mly:135-137 + register_ailname :157-159) makes the
  -- FIRST-in-file entry win. std.core is ailname-duplicate-free
  -- (verified), so this is unreachable today — see the capture-site note
  -- in CoreParser.pCoreFileGo.
  let ailnames : Fmap String sym := Lem_Map.fromList stdFile.ailnames
  let funMap : fun_map Unit := Lem_Map.fromList allDecls
  (ailnames, funMap)

/-- Convert impl declarations from a CoreParser.CoreFile into an impl map. -/
def loadCoreImpl (implFile : CoreParser.CoreFile) : impl :=
  implFile.impls.foldl
    (fun acc (name, d) =>
      -- the name was validated against Implementation.impl_map when the
      -- `def <name>` / `fun <name>` declaration was parsed (CoreParser.pDefDecl
      -- and pFunDecl call pImplConstant on the lexeme — the mirror of scan_impl,
      -- which validates every `<…>` lexeme at the lexer; Z2-CP-08, pre-merge
      -- audit F2), so the error arm is unreachable here
      let ic := match CoreParser.pImplConstant name with
        | .ok ic => ic
        | .error e => failwithI s!"Main.loadCoreImpl: {e}"
      fmapAddBy implementation_constant_compare ic d acc)
    fmapEmpty

/-! ## C-libc loading (`--libc`, arc-6 S1; the stitch reversed in zero-discrepancy Z3)

The oracle loads `runtime/libc/libc.co` — an OCaml-marshalled `core_dump`
record carrying main / calling_convention / tagDefs / globs / funs /
extern / funinfo (backend/common/pipeline.ml:621-630; reader
`read_core_object` :648-672) — as a LIBRARY, FIRST, before the user TUs
(backend/driver/main.ml:150-156: `core_libraries … @ files`, lib "c"
resolved at :54-77 to plain libc.co, i.e. Normal calling convention).

The Lean pipeline cannot read OCaml Marshal. Its libc artifact is split
in two (decision log D5; scripts/libc_prep.sh):

* BODIES (funs and globs, in file order) come from the PINNED text dump
  `tests/libc/libc.core` — the stock pretty-print of libc.co
  (`cerberus --nolibc --pp=core --pp_core_out=… libc.co`, S0 survey
  §a.1), i.e. the oracle's sequentialised+rewritten libc Core, parsed by
  CoreParser. This is ORACLE-PRODUCED INPUT in the cabs-json trust
  class: pinned and drift-checked fail-closed by libc_prep.sh.

* METADATA (extern, funinfo, tagDefs, calling convention) is NOT in the
  text dump: the stock pp omits extern/funinfo/main entirely
  (pp_extern_symmap and pp_funinfo are unreachable from the CLI,
  pp_core.ml:811-829 + pipeline.ml:536-549) and drops every tagDef whose
  definition site is an #include'd header (pp_cond, pp_core.ml:745-746,
  show_include=false — only `struct fl` survives in the dump). The
  metadata is reconstructed by frontending the SAME 12 libc source TUs
  (runtime/libc/dune:145-146, same order, same include flags) through
  our own desugar/typecheck/translate and linking them with the
  generated Core_linking — the very pipeline that produced libc.co's
  metadata on the OCaml side (extern: `translate_extern_map`,
  translation.lem:4505-4511; funinfo/tagDefs assembly:
  translation.lem:4521-4540; link merge: link_aux/link_extern,
  core_linking.lem:10-46,286-316). `--sequentialise --rewrite` (which
  the oracle's libc.co build additionally applies) are Core-to-Core BODY
  passes; they do not alter extern/funinfo/tagDefs, so the
  reconstruction is exact up to symbol identity.

* SYMBOL IDENTITY IS BEHAVIOUR (zero-discrepancy Z3, census row Z-28,
  detective RC-2): `Core_linking.merge_globs` (core_linking.lem:252-273)
  orders the linked globals by a topological sort whose tie-break is
  `Set_extra.choose` = `Pset.min_elt` (pset.ml:297) under
  `symbol_compare` — digest, then number (symbol.lem:157-160) — and
  `Driver.driver_globals` (driver.lem:1577-1584) allocates them in that
  order, so the (digest, number) of every libc global fixes every later
  address (`(long)&g` is a Defined value under PVI). The oracle's libc.co
  symbols carry the digest of their libc SOURCE file (`Cerb_fresh.set_digest`
  = `Digest.file`, pipeline.ml:181, at the dune build of libc.co) and the
  build's single-supply numbers. The metadata TUs here carry the same
  digests (their cabs-jsons record the oracle's `Digest.file` of the same
  sources — main.ml --cabs-json path) and numbers drawn by the same lem
  elaboration, i.e. order-isomorphic within a TU — so the METADATA
  symbols order exactly as the oracle's. CoreParser's dump symbols do not
  (name-interned: digest "", number = the name's hash — every libc global
  sorted before every program global, in hash order among themselves).

* THE STITCH therefore renames the DUMP onto the METADATA symbols
  (`CoreParser.renameFile`, two namespaces: ordinary identifiers and
  struct/union tags — `struct stat` and the function `stat` coexist):
  - tags by name (the headers' structs recur in every including TU: all
    same-name definitions must agree structurally, fail-closed, and the
    first in symbol order is the rename target — any structurally-equal
    one yields the same layout; every TU's own entry stays in tagDefs, as
    in libc.co);
  - functions by name (the DEFINITION's symbol where a name is declared
    in one TU and defined in another — __strtox/__strtoxd — because that
    is the symbol `link_extern` resolves calls to; checked against
    metaFile.extern's LK_normal/LK_tentative targets, fail-closed);
  - globals by POSITION: metaFile.globs is the metadata's own link order,
    the same `merge_globs` over the same keys and dependency edges as the
    oracle's libc.co link, so it must equal the dump's order (libc.co's
    globs, printed in order by pp_globs, pp_core.ml:832-841). Checked
    entry by entry — kind, ail ctype (tags by name), and name (named
    globals by name; the unnamed string-literal globals print as `a_<n>`
    with the oracle's number and have no name to join on, so position is
    their only join, which is why the whole-list agreement is
    load-bearing and any disagreement refuses the load).
  Unmapped names (locals, labels, std.core procs and proxies such as
  exit_proxy/vprintf_proxy — present in the metadata's funinfo because
  ailname substitution happens at elaboration, translation.lem:244-251)
  keep their CoreParser symbols, which ARE the std.core symbols.
  Same-named static functions in two TUs (`__procfdname`) are one
  name-interned body in the dump; the first metadata symbol in symbol
  order takes it (the other keeps its funinfo entry only).

Assembly mirrors `read_core_object` (pipeline.ml:655-663): stdlib/impl
come from the load context (:657-660), loop_attributes and
visible_objects_env are EMPTY (:661-663; empty visible_objects_env also
preserves safe_map_union's disjointness requirement at link,
core_linking.lem safe_map_union), and main = none — libc.co is a
main-less library; link_main tolerates it (core_linking.lem:50-57).
tagDefs/extern/funinfo are the linked metadata's own maps (the oracle's
libc.co carries exactly these, under exactly these symbols up to the
within-TU numbering offset).

Documented divergences from the oracle's in-memory libc file:
* ProcDecl return base types parse as BTy_unit (not printed by the pp,
  pp_core.ml:783-785) — unread for declaration-only symbols.
* Same-named static functions conflate to one body (name-hash
  interning); fail-closed structural checks make this observable-
  behavior-preserving for the pinned dump.
* Symbol NUMBERS are the Lean supply's, not libc.co's: equal up to a
  per-TU constant offset (the oracle's std.core parse and per-TU
  rewrite passes draw from the same counter), so every `symbol_compare`
  outcome agrees; the absolute number is printed only in `a_<n>` names
  of Illformed_program payloads (Z-04, EXC(a)).
-/

/-- symbolEqual (symbol.lem): digest+number, description ignored. -/
private def libcSymEq : sym → sym → Bool
  | Symbol d1 n1 _, Symbol d2 n2 _ => d1 == d2 && n1 == n2

/-- The name `--pp core` prints for a symbol (Pp_symbol.to_string_pretty,
    pp_symbol.ml:20-24: SD_Id, SD_ObjectAddress, SD_FunArgValue) — the name
    the dump's interning joins on; `none` for unnamed symbols (which print
    as `a_<n>` and are never name-joined). -/
private def libcSymNameOpt : sym → Option String
  | Symbol _ _ (SD_Id s) | Symbol _ _ (SD_ObjectAddress s) | Symbol _ _ (SD_FunArgValue s) => some s
  | _ => none

private def libcSymName : sym → String
  | Symbol _ n sd =>
    match sd with
    | .SD_Id s | .SD_ObjectAddress s | .SD_FunArgValue s => s
    | .SD_None => s!"<SD_None sym {n}>"
    | _ => s!"<unnamed sym {n}>"

/-- The dump prints an unnamed symbol as `a_<n>` (pp_symbol.ml:33-34). -/
private def libcIsUnnamedName (s : String) : Bool :=
  s.startsWith "a_" && s.length > 2 && (s.drop 2).all Char.isDigit

private def identName : identifier → String
  | Identifier _ s => s

/-- Tag positions rekeyed BY NAME onto CoreParser's interning — the
    comparison frame in which two TUs' copies of one header struct (each
    referencing its own TU's tag symbols) are structurally equal. -/
private def libcByNameCtx : CoreParser.RenameCtx :=
  { onSym := id
    onTag := fun s => match libcSymNameOpt s with
      | some n => CoreParser.internSym n
      | none => s }

/-- Structural agreement for same-name tag definitions from different TUs
    (same headers ⇒ identical layouts). Member names, qualifiers and
    ctypes (tags by name) are compared; attributes/alignment are not
    (no_attributes/none throughout the libc headers). -/
private def libcMemberEq
    (m1 m2 : identifier × (attributes × Option alignment × qualifiers × ctype)) : Bool :=
  identName m1.1 == identName m2.1 &&
  qualifiersEqual m1.2.2.2.1 m2.2.2.2.1 &&
  ctypeEqual (CoreParser.renameCtype libcByNameCtx m1.2.2.2.2)
    (CoreParser.renameCtype libcByNameCtx m2.2.2.2.2)

private def libcTagDefEq : tag_definition → tag_definition → Bool
  | StructDef xs1 f1, StructDef xs2 f2 =>
    xs1.length == xs2.length &&
    (List.zip xs1 xs2).all (fun (a, b) => libcMemberEq a b) &&
    (match f1, f2 with
     | none, none => true
     | some (FlexibleArrayMember _ i1 q1 t1), some (FlexibleArrayMember _ i2 q2 t2) =>
       identName i1 == identName i2 && qualifiersEqual q1 q2 &&
       ctypeEqual (CoreParser.renameCtype libcByNameCtx t1) (CoreParser.renameCtype libcByNameCtx t2)
     | _, _ => false)
  | UnionDef xs1, UnionDef xs2 =>
    xs1.length == xs2.length &&
    (List.zip xs1 xs2).all (fun (a, b) => libcMemberEq a b)
  | _, _ => false

/-- Comparators the generated lem code keys these maps with (arc-6 S3: the
    Fmap representation captures the comparator at build time). sym-keyed
    maps: `symbol_compare` (the Ord0 sym instance every generated
    `Map.lookup`/`insert` on syms inlines). -/
private def libcSymMapCmp : sym → sym → LemOrdering := symbol_compare

/-- `map_from_assoc` mirror — backend/common/pipeline.ml:653-654:
    `List.fold_left (fun acc (k, v) -> Pmap.add k v acc) (Pmap.empty compare)`
    — a LEFT fold of `Pmap.add`, so on a duplicate key the later binding
    wins, as in the OCaml. The one assoc list built below (`funs`) is
    duplicate-free by construction (the find?-dedup), so the fold
    direction is unobservable here and the OCaml direction is mirrored
    regardless. -/
private def libcMapFromAssoc {α β : Type} (cmp : α → α → LemOrdering)
    (l : List (α × β)) : Fmap α β :=
  l.foldl (fun acc (k, v) => fmapAddBy cmp k v acc) fmapEmpty

/-! ## Helpers -/

/-- Offset of the first byte that does not start a well-formed UTF-8
    sequence (RFC 3629 shapes: no overlong 2-byte leads, no surrogates, at
    most U+10FFFF), or `none`. Diagnostic only: the accept/refuse decision is
    `String.fromUTF8?`'s. -/
def firstInvalidUtf8 (b : ByteArray) : Option Nat := Id.run do
  let mut i := 0
  while i < b.size do
    let c := b[i]!.toNat
    let n :=
      if c < 0x80 then 1
      else if 0xC2 ≤ c && c ≤ 0xDF then 2
      else if 0xE0 ≤ c && c ≤ 0xEF then 3
      else if 0xF0 ≤ c && c ≤ 0xF4 then 4
      else 0
    if n == 0 || i + n > b.size then return some i
    let c1 := b[i + 1]!.toNat
    if n ≥ 2 && (c1 &&& 0xC0) != 0x80 then return some i
    if n == 3 && ((c == 0xE0 && c1 < 0xA0) || (c == 0xED && c1 ≥ 0xA0)) then return some i
    if n == 4 && ((c == 0xF0 && c1 < 0x90) || (c == 0xF4 && c1 ≥ 0x90)) then return some i
    if n ≥ 3 && (b[i + 2]!.toNat &&& 0xC0) != 0x80 then return some i
    if n == 4 && (b[i + 3]!.toNat &&& 0xC0) != 0x80 then return some i
    i := i + n
  return none

/-- Bug-hunt BUG-6 and K-5 (2026-09-29; record
    `docs/2026-09-29_bug-hunt-fixes-record.md` §S3): decode a Cabs JSON
    document read as BYTES, and REFUSE (exit 2, attributed) when it is not
    UTF-8. The oracle's `--cabs-json` exporter writes the bytes ≥ 0x80 of a
    file name (the real path, a `#line` or an `#include` name,
    `backend/lean_export/cabs_json.ml:30` `Cerb_position.file`), of a
    `Loc_other` string (`:44`) and of the text fields (attribute-argument
    strings `:599`/`:601`, magic comments `:657`) raw, so such a document is
    not UTF-8, while the oracle's own run proceeds. Lean strings are
    sequences of Unicode scalar values, so the bridge cannot carry those
    bytes; `IO.FS.readFile` used to throw an uncaught exception here ("Tried
    to read file … containing non UTF-8 data", rc 1), loud but not
    attributed. String-literal fragments and character-constant bodies are
    byte-carriers (one code point per byte, `json_of_bytes`) and never reach
    this refusal. A class (c) refusal (VALIDATION §3(c)); mover: a
    byte-carrier encoding for the file-name, `Loc_other` and text fields. -/
def decodeCabsJson (label : String) (bytes : ByteArray) : IO String := do
  match String.fromUTF8? bytes with
  | some s => return s
  | none =>
    let (off, ctx) := match firstInvalidUtf8 bytes with
      | some i =>
        let lo := if i ≥ 40 then i - 40 else 0
        (s!"{i}", CerbEscape.bytes (bytes.extract lo (min bytes.size (i + 40))))
      | none => ("unknown", "")
    IO.eprintln s!"cerberus-lean: refused — non-UTF-8 Cabs JSON: {label} is not valid UTF-8 (first invalid byte at offset {off}, context \"{ctx}\"). The oracle's --cabs-json exporter copies the bytes ≥ 0x80 of a file name (the real path, a #line or an #include name), of a Loc_other string and of attribute-argument or magic-comment text into the JSON raw (backend/lean_export/cabs_json.ml:30, :44, :599/:601, :657); this port's bridge cannot carry them, because Lean strings are sequences of Unicode scalar values (string-literal and character-constant bytes are byte-carriers and unaffected; see VALIDATION.md §3(c), bug hunt BUG-6/K-5)"
    IO.Process.exit 2

/-- Read a Cabs JSON file as bytes and decode it (`decodeCabsJson`). -/
def readCabsJsonFile (path : String) : IO String := do
  decodeCabsJson path (← IO.FS.readBinFile path)

/-- Read all input files' contents. Multi-TU: one cabs-json per
    translation unit, in command-line order — mirroring the OCaml
    driver's `files` list (backend/driver/main.ml:153-156, the per-file
    frontend fold). `--stdin` remains single-TU. -/
def readInputs (args : List String) : IO (List String) := do
  match args with
  | ["--stdin"] => do
    -- read BYTES (bug-hunt BUG-6: a non-UTF-8 document is refused by
    -- decodeCabsJson, not thrown by a text read)
    let stdin ← IO.getStdin
    let mut buf := ByteArray.empty
    let mut done_ := false
    while !done_ do
      let chunk ← stdin.read 65536
      if chunk.isEmpty then done_ := true
      else buf := buf ++ chunk
    return [← decodeCabsJson "<stdin>" buf]
  | [] => throw (IO.Error.userError "usage: cerberus-lean [--batch] [--stdin | FILE.json ...]")
  | files =>
    if files.contains "--stdin" then
      throw (IO.Error.userError "--stdin cannot be combined with file arguments")
    else
      files.mapM readCabsJsonFile

def countDecls : List external_declaration → Nat × Nat × Nat
  | [] => (0, 0, 0)
  | d :: ds =>
    let (funcs, decls, other) := countDecls ds
    match d with
    | .EDecl_func _ => (funcs + 1, decls, other)
    | .EDecl_decl _ => (funcs, decls + 1, other)
    | _ => (funcs, decls, other + 1)

def selfTest : IO Unit := do
  IO.println "cerberus-lean: loaded"
  match CerberusImpl.sizeof_ity (Signed Int_) with
  | some n => IO.println s!"  sizeof(int) = {n}"
  | none => IO.println "  sizeof(int) = unknown"
  -- the two readers (enum map, tag table): a literal non-enum type consults neither
  let maxInt := CerbMem.maxIval fmapEmpty fmapEmpty (Signed Int_)
  let (.IV _ maxN) := maxInt
  IO.println s!"  max(signed int) = {maxN}"
  let minInt := CerbMem.minIval fmapEmpty fmapEmpty (Signed Int_)
  let (.IV _ minN) := minInt
  IO.println s!"  min(signed int) = {minN}"
  let bytes := CerbMem.intToBytes true 42 4
  let byteStrs := bytes.map fun b => match b with
    | some v => toString v.toNat | none => "?"
  IO.println s!"  intToBytes(42, 4) = {byteStrs}"
  IO.println "  ready"

/-! ## Elaborated-Core signature dump (`--pp-core`, arc-4 S4)

LIMITATION — SIGNATURE-LEVEL ONLY, deliberately. The Lean pipeline has no
real Core EXPRESSION pretty-printer (arc-10 S3 gave CerbPP real
value/ctype/mem-value printer mirrors, but the expression/statement
printers remain among its 25 enumerated placeholders and the generated
Pp.lean is a stub), and building one is explicitly out of scope for this slice
(charter S4: stage differential at whatever granularity is available
WITHOUT building a printer). So `--pp-core` emits a canonical
SIGNATURE-level dump of the translated Core file:

  tagdef struct <name> members=<m1,m2,...>
  tagdef union <name> members=<...>
  glob <name>                      (GlobalDef only — OCaml pp skips GlobalDecl)
  fun <name> arity=<n>
  proc <name> arity=<n>
  procdecl <name> arity=<n>
  builtin <name> arity=<n>

`scripts/test_elab.sh` extracts the same facts from OCaml
`cerberus --nolibc --pp core` output and diffs the two through
`canonicalize_ids.py`. Function/glob BODIES are NOT compared — a
body-level Core differential needs a Lean Core pretty-printer (recorded
as a next-arc item in the S4b scoreboard doc). -/

/-- Mirror of OCaml `Pp_symbol.to_string_pretty` at debug level ≤ 4
    (ocaml_frontend/pprinters/pp_symbol.ml:12-35), which is what
    `--pp core` uses for every symbol we dump. -/
def ppSymbolPretty : sym → String
  | Symbol _ n sd =>
    match sd with
    | .SD_Id str | .SD_ObjectAddress str | .SD_FunArgValue str => str
    | .SD_unnamed_tag _ => s!"__cerbty_unnamed_tag_{n}"
    | .SD_CN_Id str => str
    | _ => s!"a_{n}"

/-- Signature-level dump of the translated Core file (see module note
    above). Mirrors WHAT OCaml `pp_core.pp_file` prints (incl. appending
    a flexible array member as an ordinary member,
    pp_core.ml:755-760, and skipping GlobalDecl, pp_core.ml:832-841) but
    at declaration granularity only. -/
def ppCoreSignature (coreFile : file Unit) : IO Unit := do
  let identName : identifier → String
    | Identifier _ s => s
  for (s, (_loc, td)) in fmapElements coreFile.tagDefs do
    match td with
    | StructDef membrs flexOpt =>
      let names := membrs.map (fun (i, _) => identName i)
      let names := match flexOpt with
        | some (FlexibleArrayMember _ i _ _) => names ++ [identName i]
        | none => names
      IO.println s!"tagdef struct {ppSymbolPretty s} members={String.intercalate "," names}"
    | UnionDef membrs =>
      let names := membrs.map (fun (i, _) => identName i)
      IO.println s!"tagdef union {ppSymbolPretty s} members={String.intercalate "," names}"
  for (s, g) in coreFile.globs do
    match g with
    | GlobalDef _ _ => IO.println s!"glob {ppSymbolPretty s}"
    | GlobalDecl _ => pure ()   -- OCaml pp_globs prints nothing for these
  for (s, d) in fmapElements coreFile.funs do
    match d with
    | Fun _ params _ => IO.println s!"fun {ppSymbolPretty s} arity={params.length}"
    | Proc _ _ _ params _ => IO.println s!"proc {ppSymbolPretty s} arity={params.length}"
    | ProcDecl _ _ tys => IO.println s!"procdecl {ppSymbolPretty s} arity={tys.length}"
    | BuiltinDecl _ _ tys => IO.println s!"builtin {ppSymbolPretty s} arity={tys.length}"

/-! ## Pipeline -/

/-- OCaml `Filename.concat` (Unix, `stdlib/filename.ml`): `dir ^ file` when
    `dir` is empty or ends with `/`, otherwise `dir ^ "/" ^ file`. The
    oracle builds every runtime path with it (`util/cerb_runtime.ml:9`), and
    the library-location test compares those paths as STRINGS
    (`util/cerb_location.ml:512-523`), so the port builds them the same way. -/
def filenameConcat (dir file : String) : String :=
  if dir.isEmpty || dir.endsWith "/" then dir ++ file else dir ++ "/" ++ file

/-- The runtime a `--runtime DIR` / `CERB_INSTALL_PREFIX` prefix denotes:
    `util/cerb_runtime.ml:47` `prefix / "lib" / pkg / "runtime"` with
    `pkg = "cerberus-lib"` (`:3`); `in_runtime` then appends the path
    (`:76-84`; the source-root arm applies only to the OPAM fallback, `:44-49`,
    which this port does not mirror — see `resolveRuntime`). -/
def runtimeOfPrefix (pfx : String) : String :=
  filenameConcat (filenameConcat (filenameConcat pfx "lib") "cerberus-lib") "runtime"

/-- REFUSE (exit 2, attributed) — the runtime-resolution boundary. -/
def refuseRuntime (what : String) : IO α := do
  IO.eprintln s!"cerberus-lean: refused — runtime: {what} (see VALIDATION.md, bug hunt BUG-2)"
  IO.Process.exit 2

/-- The runtime root `resolveRuntime` selects (before its existence check). -/
def resolveRuntimeRoot (cli : Option String) : IO String := do
  match cli with
  | some "" => refuseRuntime "--runtime was given an empty directory; the oracle would resolve `lib/cerberus-lib/runtime` against the working directory, which this port refuses to do"
  | some d => return runtimeOfPrefix d
  | none =>
    match ← IO.getEnv "CERB_INSTALL_PREFIX" with
    | some "" => refuseRuntime "CERB_INSTALL_PREFIX is set but empty; the oracle would resolve `lib/cerberus-lib/runtime` against the working directory, which this port refuses to do"
    | some d => return runtimeOfPrefix d
    | none =>
      refuseRuntime "no runtime given: pass --runtime DIR (runtime = DIR/lib/cerberus-lib/runtime, as the oracle's --runtime) or set CERB_INSTALL_PREFIX; the oracle's OPAM_SWITCH_PREFIX fallback is deliberately NOT mirrored (a shared switch's runtime can differ silently from the checkout's), and the working directory is never searched"

/-- Runtime resolution — mirror of `util/cerb_runtime.ml:38-56`
    `detect_runtime`, bug-hunt BUG-2 (2026-09-29; record
    `docs/2026-09-29_bug-hunt-fixes-record.md` §S2). The driver used to probe
    `runtime/libcore`, `../runtime/libcore` and `../../runtime/libcore`
    relative to the CURRENT DIRECTORY and load the first `std.core` found,
    unpinned: a different `std.core` in the working directory was used
    silently.
    - `--runtime DIR` (the oracle's `-r` / `--runtime DIR`, `backend/driver/main.ml:436-438`,
      stored in `Cerb_runtime.specified_runtime` at `:106`) has the highest
      priority: the `SPECIFIED` arm, runtime = `DIR/lib/cerberus-lib/runtime`.
    - otherwise the `CERB_INSTALL_PREFIX` environment variable: the `ENV_VAR`
      arm, the same construction.
    - DELIBERATE DIVERGENCE ([AGENT] choice in bug-hunt fixes S2, made under the
      operator's authorization to fix BUG-2, [USER 2026-09-29] "Agree on
      everything, yes on the fixes"): the oracle's last arm, `OPAM` — the
      runtime of the switch in `OPAM_SWITCH_PREFIX`, or the build-tree source
      root found through `PATH` (`:21-30`) — is NOT mirrored. The run is
      REFUSED instead: a shared switch's runtime can differ silently from the
      runtime the oracle of a given checkout uses, which is the BUG-2 shape
      again.
    - DELIBERATE DIVERGENCE ([AGENT], same authorization, fail-closed): an EMPTY value (either
      source) is refused. The oracle would build the relative
      `lib/cerberus-lib/runtime`, i.e. resolve the runtime against the
      working directory, which is the lookup BUG-2 removed.
    Every harness passes the oracle's runtime: `scripts/common.sh` exports
    `CERB_INSTALL_PREFIX` = the prefix of its `--runtime=` oracle argument. -/
def resolveRuntime (cli : Option String) : IO String := do
  let rt ← resolveRuntimeRoot cli
  -- pipeline.ml:36-37 (the oracle's own existence check at stdlib load):
  -- checked here, before any input is read, so a wrong runtime is named as such
  let stdCore := filenameConcat (filenameConcat rt "libcore") "std.core"
  unless ← System.FilePath.pathExists stdCore do
    refuseRuntime s!"couldn't find the Core standard library file (looked at: `{stdCore}'); the runtime was resolved from {if cli.isSome then "--runtime" else "CERB_INSTALL_PREFIX"} as DIR/lib/cerberus-lib/runtime"
  return rt

/-- The runtime's three library directories, exactly as the oracle's
    `is_library_location` builds them (`util/cerb_location.ml:514-517`:
    `Cerb_runtime.in_runtime "libc/include"`, `"libcore"`, `"libcore/impls"`). -/
def runtimeLibraryDirs (runtime : String) : List String :=
  ["libc/include", "libcore", "libcore/impls"].map (filenameConcat runtime)

/-- Bug-hunt BUG-3 (2026-09-29): the import-time half of the library-location
    mirror (see `CerbLocation.isLibraryLocation`). A file path of the imported
    Cabs locations that passes the port's SUFFIX test but not the oracle's
    EXACT test (`Filename.dirname path` ∈ `runtimeLibraryDirs runtime`) would
    be library-classified by Lean only, and the UB location would differ: the
    run is REFUSED (exit 2, attributed). Afterwards the suffix test equals the
    exact test on every file the run can carry. -/
def refuseLibraryLocations (runtime : String) (source : String) (files : Array String) : IO Unit := do
  let exact := runtimeLibraryDirs runtime
  for f in files do
    if CerbLocation.isLibraryPathSuffix f && !exact.contains (CerbLocation.dirname f) then
      IO.eprintln s!"cerberus-lean: refused — library-location classification: {source} carries a source location in `{f}`, whose directory ends in one of {CerbLocation.libraryDirs} but is not one of this run's runtime library directories {exact}; the oracle classifies a location as library code by EXACT directory equality with its runtime (util/cerb_location.ml:512-523), this port's pure CerbLocation.isLibraryLocation by the directory suffix, so answering could serve a different UB location (see VALIDATION.md, bug hunt BUG-3)"
      IO.Process.exit 2

/-- Per-TU frontend: desugar → typecheck → translate, under the TU's own
    digest (set by the caller). Mirror of the OCaml per-file frontend
    (`c_frontend` pipeline.ml:180-247 + `c_frontend_and_elaboration`
    pipeline.ml:249-260), factored out of `runPipeline` for the multi-TU
    loop (arc-5 S2). Returns `.error exitCode` on a stage failure (the
    historical exit-code behavior of each failure branch is preserved:
    batch mode 1, human mode 0).

    EVALUATION ORDER: every pure stage call goes through
    `CerberusFresh.forceIO` — the stages read the per-TU digest global
    internally (Symbol.fresh → `digest ()`), and a plain pure `let` here
    would be let-SUNK past the NEXT TU's `setDigestIO`, stamping this
    TU's symbols with the wrong digest (see CerberusFresh.forceIO and
    test/Unit/FreshIntTest.lean testDigestGlobal). This is frontend-only:
    the run receives `runDigest tunits` as data and never reads the global. -/
def frontendTU [LemFuel] [CerbGlobal.Switches] (quiet : Bool) (supply : Nat) (addressSpaceTop : Int)
    (coreEvalStuff : Fmap String sym × fun_map Unit × impl)
    (ailnames : Fmap String sym) (stdFunMap : fun_map Unit) (coreImpl : impl)
    (tunit : translation_unit) : IO (Except UInt8 (file Unit × Nat)) := do
  let say (s : String) : IO Unit := unless quiet do IO.println s
  -- Desugar Cabs → AIL
  say "  desugaring Cabs → AIL..."
  let cnInit := empty_init
  -- Effect-retirement C1: `supply` is the pipeline's SINGLE fresh-symbol
  -- stream (S1 ruling) — threaded through desugar (incl. its const-expr
  -- mini-runs), elaboration, and back out to the caller.
  -- desugar/translate are reader-lifted since C1 (the reader_consumer
  -- mem-ops in their cones, mem.lem): the reader argument is the
  -- PHASE-APPROPRIATE tag table — EMPTY during desugar/typing/
  -- elaboration, mirroring the oracle's empty Tags global there
  -- (pipeline.ml:253 resets before translate; the union-arm asymmetry
  -- mirror, charter section 4.2 — the offsetof-union-member crash pair
  -- pins this). The mini-run's own extent still sees the translated
  -- definitions via the reader_seed run_const_expr_driver.
  -- Program-data parameters E-A (2026-09-20): `enum_definitions` is the
  -- FIRST reader (sorted order: enum_definitions, tagDefs). At the desugar
  -- entry the map is EMPTY — every desugar-time read of it is seeded from
  -- the desugar state at its site (record §1, D3), exactly as the oracle's
  -- registry is filled as enums are registered; a miss here would be a
  -- seeding gap (loud: `Ocaml_implementation.typeof_enum: … was not registered`).
  let desugRes ← (CerberusFresh.forceIO
    (fun () => desugar fmapEmpty fmapEmpty supply addressSpaceTop coreEvalStuff cnInit "main" tunit) : BaseIO _)
  match desugRes with
  | .Result (_, (mainSym, ailProg), supplyAfterDesugar) =>
    say s!"  desugaring succeeded!"
    say s!"    main symbol: {match mainSym with | some _ => "found" | none => "not found"}"
    say s!"    declarations: {List.length ailProg.declarations}"
    say s!"    function defs: {List.length ailProg.function_definitions}"
    say s!"    tag defs: {List.length ailProg.tag_definitions}"
    say s!"    enum defs: {List.length ailProg.enum_definitions}"
    -- The COMPLETE per-TU enum map from the sigma (D3): typing and
    -- elaboration receive what the oracle's registry holds after this TU's
    -- desugaring — the same GCC-rule decisions, as data.
    let enumDefs : Fmap sym integerType := Lem_Map.fromList ailProg.enum_definitions

    -- Step 2: Typecheck AIL (mirrors pipeline.ml:217-219); reader-lifted since
    -- E-A (its layout reads normalise through the enum map)
    say "  typechecking AIL..."
    let ailInput := (mainSym, ailProg)
    let tyRes ← (CerberusFresh.forceIO (fun () =>
      to_exception (fun (p : CerbLocation.Loc × typing_error) => (p.1, AIL_TYPING p.2))
        (annotate_program enumDefs fmapEmpty ailInput)) : BaseIO _)
    match tyRes with
    | .Exception (loc, cause) =>
      if quiet then
        -- OCaml parity: typing-level UB gets a batch Undefined line (main.ml runM)
        match cause with
        | .AIL_TYPING (.TError_UndefinedBehaviour ub) =>
          -- main.ml:173-177: `Undefined { ub; stderr= ""; loc }` through string_of_batch_output
          printUndefinedLine (stringFromUndefined_behaviour ub) "" (CerbLocation.simpleLocation loc)
        | _ =>
          IO.println s!"Error \{msg: \"typechecking failed at {CerbLocation.stringFromLocation loc}\"}"
        return .error 1
      else
        IO.println s!"  typechecking failed!"
        IO.println s!"    at: {CerbLocation.stringFromLocation loc}"
        return .error 0
    | .Result (typedProg, _annots) =>
      say s!"  typechecking succeeded!"

      -- Step 3: Translate AIL → Core
      say "  translating AIL → Core..."
      -- C1: the per-TU CerbTags reset (pipeline.ml:253 mirror) is GONE —
      -- there is no global to reset; translate's reader argument below is
      -- the empty table, which IS the oracle's reset-then-elaborate state
      -- (documented divergence from the driver-level bookkeeping, mirror
      -- doctrine; the value-passing replaces the write scaffold).
      let callconv := Normal_callconv
      let (coreFile, supplyAfterTranslate) ← (CerberusFresh.forceIO (fun () =>
        translate enumDefs fmapEmpty supplyAfterDesugar (ailnames, stdFunMap) callconv coreImpl typedProg) : BaseIO _)
      say s!"  translation succeeded!"
      say s!"    main: {match coreFile.main with | some _ => "found" | none => "not found"}"
      say s!"    funs: {List.length (fmapElements coreFile.funs)}"
      say s!"    globs: {List.length coreFile.globs}"
      return .ok (coreFile, supplyAfterTranslate)
  | .Exception (loc, cause) =>
    if quiet then
      -- OCaml parity (main.ml runM): desugar-level UB gets a batch Undefined line
      match cause with
      | .DESUGAR (.Desugar_UndefinedBehaviour ub) =>
        -- main.ml:166-170: `Undefined { ub; stderr= ""; loc }` through string_of_batch_output
        printUndefinedLine (stringFromUndefined_behaviour ub) "" (CerbLocation.simpleLocation loc)
      | _ =>
        IO.println s!"Error \{msg: \"desugaring failed at {CerbLocation.stringFromLocation loc}\"}"
      return .error 1
    else
      IO.println s!"  desugaring failed!"
      IO.println s!"    at: {CerbLocation.stringFromLocation loc}"
      -- Print cause details
      match cause with
      | .DESUGAR (.Desugar_ConstraintViolation v) => IO.println s!"    cause: DESUGAR ConstraintViolation"
      | .DESUGAR (.Desugar_UndefinedBehaviour ub) =>
        IO.println s!"    cause: DESUGAR UndefinedBehaviour: {stringFromUndefined_behaviour ub}"
      | .DESUGAR (.Desugar_MiscViolation _) => IO.println s!"    cause: DESUGAR MiscViolation"
      | .DESUGAR (.Desugar_NotYetSupported s) => IO.println s!"    cause: DESUGAR NotYetSupported: {s}"
      | .DESUGAR (.Desugar_NeverSupported s) => IO.println s!"    cause: DESUGAR NeverSupported: {s}"
      | .DESUGAR (.Desugar_agnosticFailure s) => IO.println s!"    cause: DESUGAR agnosticFailure: {s}"
      | .DESUGAR .Desugar_illtypedIntegerConstant => IO.println s!"    cause: DESUGAR illtypedIntegerConstant"
      | .DESUGAR (.Desugar_TODO s) => IO.println s!"    cause: DESUGAR TODO: {s}"
      | .DESUGAR _ => IO.println s!"    cause: DESUGAR (other)"
      | .AIL_TYPING _ => IO.println s!"    cause: AIL_TYPING"
      | .CPP _ => IO.println s!"    cause: CPP"
      | _ => IO.println s!"    cause: (other)"
      return .error 0

/-- Load and assemble the libc library Core file (see the module note at
    "C-libc loading" above). -/
def loadLibc [LemFuel] [CerbGlobal.Switches] (runtime : String) (quiet : Bool) (supply0 : Nat) (addressSpaceTop : Int)
    (coreEvalStuff : Fmap String sym × fun_map Unit × impl)
    (ailnames : Fmap String sym) (stdFunMap : fun_map Unit) (coreImpl : impl)
    (libcCorePath : String) (libcTuJsons : List String) :
    IO (Except UInt8 (file Unit × Nat)) := do
  let say (s : String) : IO Unit := unless quiet do IO.println s
  let bail (msg : String) : IO (Except UInt8 (file Unit × Nat)) := do
    if quiet then IO.println s!"Error \{msg: \"libc load failed: {CerbEscape.text msg}\"}"
    else IO.println s!"  libc load failed: {msg}"
    return .error 1
  -- 1. Parse the pinned dump (bodies). The TU digest is the real MD5 of
  --    the pinned file (arc-5 per-TU digest machinery; CoreParser's
  --    interning is digest-independent, so this is provenance-recording).
  say s!"  loading libc bodies from {libcCorePath}..."
  let dumpContent ← IO.FS.readFile ⟨libcCorePath⟩
  let _ ← (CerberusFresh.setDigestIO (CerberusFresh.md5Hex dumpContent) : BaseIO Unit)
  let parsed ← match CoreParser.parseFile dumpContent with
    | .ok f => pure f
    | .error e => return (← bail s!"parsing {libcCorePath}: {e}")
  say s!"    {parsed.procs.length} proc, {parsed.funs.length} fun, {parsed.globs.length} glob"
  -- 2. Frontend the 12 metadata TUs (same order as runtime/libc/dune's
  --    libc.co link; reverse-consed accumulator exactly as the OCaml
  --    driver fold, main.ml:153-156) and link them. Zero-discrepancy Z3
  --    (Z-28): each TU runs under the digest its cabs-json carries — the
  --    oracle's `Digest.file` of the libc SOURCE (main.ml --cabs-json path
  --    = pipeline.ml:181 c_frontend), i.e. the digest the same source's
  --    symbols carry inside libc.co (runtime/libc/dune:145-146 builds it
  --    from these sources through the same c_frontend).
  say s!"  loading libc metadata from {libcTuJsons.length} TUs..."
  let mut metaFiles : List (file Unit) := []
  let mut supply := supply0
  for j in libcTuJsons do
    let content ← readCabsJsonFile j
    let (digest, tunit) ← match CabsImport.parseJsonWithFiles content with
      | .ok (d, t, files) => do
        refuseLibraryLocations runtime s!"the libc metadata TU {j}" files
        pure (d, t)
      | .error e => return (← bail s!"cabs-json parse error in {j}: {e}")
    let _ ← (CerberusFresh.setDigestIO digest : BaseIO Unit)
    match ← frontendTU true supply addressSpaceTop coreEvalStuff ailnames stdFunMap coreImpl tunit with
    | .error _ => return (← bail s!"frontend failed for libc metadata TU {j}")
    | .ok (f, supply') => metaFiles := f :: metaFiles; supply := supply'
  let metaFile ← match link metaFiles with
    | .Result f => pure f
    | .Exception (_, _) => return (← bail "linking the libc metadata TUs failed")
  -- 3. THE STITCH (module note): rename the dump onto the metadata
  --    symbols — tags by name, functions by name, globals by position —
  --    every join fail-closed.
  let stitched : Except String (CoreParser.CoreFile × List (sym × generic_globs Unit Unit)
      × Fmap sym (CerbLocation.Loc × tag_definition)
      × Fmap sym (CerbLocation.Loc × attributes × ctype × List (Option sym × ctype) × Bool × Bool)) := do
    -- (a) tags
    let mut tagMap : Std.HashMap String sym := {}
    let mut tagDefByName : Std.HashMap String tag_definition := {}
    for (s, (_, td)) in fmapElements metaFile.tagDefs do
      let name ← match libcSymNameOpt s with
        | some n => pure n
        | none => throw s!"libc metadata tag symbol without a printable name: {libcSymName s} (cannot name-join)"
      match tagDefByName[name]? with
      | none =>
        tagMap := tagMap.insert name s
        tagDefByName := tagDefByName.insert name td
      | some td' =>
        unless libcTagDefEq td' td do
          throw s!"libc metadata name-join collision with disagreeing content: tagDef '{name}'"
    -- (a') ONE tag symbol per name, on BOTH halves. The run-time
    --     compatibility check (`AilTypesAux.are_compatible`,
    --     ailTypesAux.lem:830-837, reached from every elaborated call through
    --     `PEare_compatible`, core_eval.lem:1090-1099) requires struct/union
    --     tag SYMBOLS to be equal; the oracle satisfies it because a call
    --     site is checked against the CALLER TU's own declaration entry of the
    --     callee (`cfunction` reads funinfo on the pointer's symbol,
    --     core_eval.lem:906, before the extern remap) — both sides carry that
    --     TU's tags. The dump's bodies cannot say which TU they came from, so
    --     their tag references join onto one representative per name; the
    --     metadata's funinfo ctypes, tagDefs (keys and members) and decl-globs
    --     ctypes are moved onto the SAME representative here, so the frame is
    --     consistent — the one-tag-per-name frame of the pre-Z3 loader, now
    --     under a real (digest, number) symbol. Same-name definitions were
    --     checked structurally equal in (a), so every collapsed tagDef is the
    --     same layout. Program↔libc calls are unaffected (the program's own
    --     declaration entry carries its own tags on both sides).
    let metaTagCtx : CoreParser.RenameCtx :=
      { onSym := id
        onTag := fun s => match libcSymNameOpt s with
          | some n => (tagMap[n]?).getD s
          | none => s }
    let mut tagDefs : List (sym × (CerbLocation.Loc × tag_definition)) := []
    for (s, (loc, td)) in fmapElements metaFile.tagDefs do
      let k := metaTagCtx.onTag s
      unless tagDefs.any (fun kv => libcSymEq kv.1 k) do
        tagDefs := tagDefs ++ [(k, (loc, CoreParser.renameTagDef metaTagCtx td))]
    let funinfo := (fmapElements metaFile.funinfo).map fun (s, (loc, attrs, ret, params, v, pr)) =>
      (s, (loc, attrs, CoreParser.renameCtype metaTagCtx ret,
        params.map (fun (n, t) => (n, CoreParser.renameCtype metaTagCtx t)), v, pr))
    -- (b) functions: the definition's symbol wins over declaration-only
    --     entries; among definitions the first in symbol order
    let mut funMap : Std.HashMap String (sym × Bool) := {}
    for (s, d) in fmapElements metaFile.funs do
      let name ← match libcSymNameOpt s with
        | some n => pure n
        | none => throw s!"libc metadata function symbol without a printable name: {libcSymName s} (cannot name-join)"
      let isDef := match d with
        | Proc _ _ _ _ _ | Fun _ _ _ => true
        | ProcDecl _ _ _ | BuiltinDecl _ _ _ => false
      match funMap[name]? with
      | none => funMap := funMap.insert name (s, isDef)
      | some (_, true) => pure ()
      | some (_, false) => if isDef then funMap := funMap.insert name (s, true)
    -- (c) globals, by position over the DEFINITIONS: the dump prints only
    --     GlobalDef entries (pp_globs skips GlobalDecl, pp_core.ml:840-841)
    --     while libc.co — and the linked metadata — also carry the
    --     declaration-only globals, which the driver skips at allocation
    --     (driver.lem:1581) but merge_globs still sorts. The metadata's list
    --     is therefore the libc file's globs (decls included, as in libc.co)
    --     and its GlobalDef subsequence must equal the dump's list.
    let metaDefs := metaFile.globs.filter fun (_, g) => match g with
      | GlobalDef _ _ => true
      | GlobalDecl _ => false
    unless parsed.globs.length == metaDefs.length do
      throw s!"libc stitch: the dump has {parsed.globs.length} global definitions but the linked metadata has {metaDefs.length} (of {metaFile.globs.length} entries) — the two link orders cannot be joined"
    let mut globMap : Std.HashMap String sym := {}
    for (ms, _) in metaFile.globs.filter (fun (_, g) => match g with | GlobalDecl _ => true | _ => false) do
      -- declaration-only entries: one per TU that declares a header
      -- extern (`extern FILE *const __stdout;` in every stdio.h includer),
      -- never in the dump. Bodies that mention the name join onto the
      -- DEFINITION's symbol when libc defines it (below, the definition
      -- overwrites); a name libc only declares joins onto the first
      -- declaration in symbol order — the oracle resolves it through the
      -- extern map to the same target either way.
      match libcSymNameOpt ms with
      | some n => unless globMap.contains n do globMap := globMap.insert n ms
      | none => throw s!"libc stitch: unnamed declaration-only global {libcSymName ms}"
    let mut defNames : Std.HashMap String Unit := {}
    let mut i := 0
    for ((ds, dg), (ms, mg)) in List.zip parsed.globs metaDefs do
      let dname := libcSymName ds
      let dcty := match dg with
        | GlobalDef (_, ct) _ => some ct
        | GlobalDecl _ => none
      let mcty := match mg with
        | GlobalDef (_, ct) _ => some ct
        | GlobalDecl _ => none
      match dcty, mcty with
      | some dct, some mct =>
        unless ctypeEqual (CoreParser.renameCtype libcByNameCtx dct)
            (CoreParser.renameCtype libcByNameCtx mct) do
          throw s!"libc stitch: global definition #{i} '{dname}': the dump's ail ctype differs from the metadata's"
      | _, _ => throw s!"libc stitch: global #{i} '{dname}' is a declaration in the dump (the pp never prints one)"
      match ms with
      | Symbol _ _ (SD_ObjectAddress n) | Symbol _ _ (SD_Id n) =>
        unless n == dname do
          throw s!"libc stitch: global definition #{i} is '{dname}' in the dump but '{n}' in the metadata — the two link orders disagree (the metadata's merge_globs order must equal libc.co's)"
      | Symbol _ n SD_None =>
        unless libcIsUnnamedName dname do
          throw s!"libc stitch: global definition #{i} is '{dname}' in the dump but the unnamed a_{n} in the metadata — the two link orders disagree"
      | _ => throw s!"libc stitch: global definition #{i} '{dname}': unexpected metadata symbol description {libcSymName ms}"
      if defNames.contains dname then
        throw s!"libc stitch: global '{dname}' is defined twice (a static in two TUs) — name-interning cannot keep the two apart"
      defNames := defNames.insert dname ()
      globMap := globMap.insert dname ms   -- a definition wins over its declarations
      i := i + 1
    -- (d) the linker's own resolution must agree with the joins
    for (ident, (_, lk)) in fmapElements metaFile.extern do
      let target := match lk with
        | LK_normal d | LK_tentative d => some d
        | LK_none => none
      match target with
      | none => pure ()
      | some d =>
        let name ← match libcSymNameOpt d with
          | some n => pure n
          | none => throw s!"libc stitch: extern '{identName ident}' resolves to an unnamed symbol"
        let joined := match globMap[name]? with
          | some s => some s
          | none => funMap[name]?.map Prod.fst
        match joined with
        | some s =>
          unless libcSymEq s d do
            throw s!"libc stitch: extern '{identName ident}' resolves to a symbol other than the stitched '{name}'"
        | none =>
          throw s!"libc stitch: extern '{identName ident}' resolves to '{name}', which the dump does not define"
    -- (e) rename
    let ctx : CoreParser.RenameCtx :=
      { onSym := fun s => match libcSymNameOpt s with
          | some n => match globMap[n]? with
            | some s' => s'
            | none => match funMap[n]? with
              | some (s', _) => s'
              | none => s
          | none => s
        onTag := fun s => match libcSymNameOpt s with
          | some n => (tagMap[n]?).getD s
          | none => s }
    let renamed := CoreParser.renameFile ctx parsed
    -- (f) the dump's surviving tagDefs (struct fl) must agree with the
    --     metadata's — fail-closed consistency between the two halves
    for (s, (_, td)) in renamed.tagDefs do
      match tagDefs.find? (fun kv => libcSymEq kv.1 s) with
      | none => throw s!"dump tagDef '{libcSymName s}' missing from metadata"
      | some (_, (_, td')) =>
        unless libcTagDefEq td td' do
          throw s!"dump tagDef '{libcSymName s}' disagrees with metadata"
    -- (g) the libc globs: the metadata's list (libc.co's order, decls
    --     included), each definition's body taken from the renamed dump
    --     under the now-shared symbol
    let mut globs : List (sym × generic_globs Unit Unit) := []
    for (ms, mg) in metaFile.globs do
      match mg with
      | GlobalDecl (bty, ct) => globs := globs ++ [(ms, GlobalDecl (bty, CoreParser.renameCtype metaTagCtx ct))]
      | GlobalDef _ _ =>
        match renamed.globs.find? (fun kv => libcSymEq kv.1 ms) with
        | some (_, g) => globs := globs ++ [(ms, g)]
        | none => throw s!"libc stitch: no dump body for global definition '{libcSymName ms}' after renaming"
    pure (renamed, globs, libcMapFromAssoc libcSymMapCmp tagDefs, libcMapFromAssoc libcSymMapCmp funinfo)
  let (renamed, globs, tagDefs, funinfo) ← match stitched with
    | .ok f => pure f
    | .error e => return (← bail e)
  -- 4. Fun map from the renamed dump. Proc definitions win over ProcDecl
  --    entries for the same symbol (the pp emits both for names declared
  --    in one TU and defined in another — __strtox/__strtoxd; only a
  --    Proc body satisfies call_proc, core_run.lem:46-51). Duplicate
  --    Proc definitions (static __procfdname in two TUs) keep the first.
  let mut funs : List (sym × generic_fun_map_decl Unit Unit) := []
  for (s, d) in renamed.funs ++ renamed.procs ++ renamed.builtins do
    match funs.find? (fun kv => libcSymEq kv.1 s) with
    | none => funs := funs ++ [(s, d)]
    | some (_, existing) =>
      match existing, d with
      | ProcDecl _ _ _, Proc _ _ _ _ _ =>
        funs := funs.map (fun kv => if libcSymEq kv.1 s then (kv.1, d) else kv)
      | _, _ => pure ()
  say s!"    metadata: {(fmapElements tagDefs).length} tagDefs, {(fmapElements metaFile.extern).length} extern, {(fmapElements funinfo).length} funinfo"
  -- 5. Assemble (read_core_object mirror, pipeline.ml:655-663).
  return .ok ({
    main := none
    calling_convention0 := metaFile.calling_convention0
    tagDefs := tagDefs
    -- program-data parameters E-A: the read_core_object mirror carries NO enum
    -- map (pipeline.ml:666 fills no registry for a .co input; record W2). The
    -- metadata TUs' own enum decisions are inert here: the dump's enum tags
    -- are library (`""`-digest) symbols the stitch never renames.
    enumDefs := fmapEmpty
    stdlib := stdFunMap
    impl0 := coreImpl
    globs := globs
    funs := libcMapFromAssoc libcSymMapCmp funs
    extern := metaFile.extern
    funinfo := funinfo
    loop_attributes1 := fmapEmpty
    visible_objects_env0 := fmapEmpty
  }, supply)


/-- Run the pipeline over one or more translation units (multi-TU, arc-5
    S2). `tunits` carries (source digest, parsed Cabs) per TU in
    command-line order — the digest is the oracle's `Digest.file` the
    cabs-json carries (CabsImport.parseJson; zero-discrepancy Z3). Per TU: set the TU digest, then
    desugar→typecheck→translate (`frontendTU`); the resulting Core files
    are linked with the generated `Core_linking.link` exactly as the
    OCaml driver does (backend/driver/main.ml:278-281), tag definitions
    are taken from the LINKED file (main.ml:284-285), and execution
    proceeds as before. Single-TU behavior is byte-identical: the chatter
    order is preserved and `link [f]` folds over the empty tail,
    returning `f` unchanged (core_linking.lem:309-316).

    `batch` selects machine-parseable output (see above); `ppCore` stops
    after linking and dumps the signature-level Core summary (see
    `ppCoreSignature`); the default human-readable mode is unchanged (and
    keeps its historical exit-code behavior: 0 even on semantic stage
    failures). -/
def runPipeline [LemFuel] [CerbGlobal.Switches] (runtime : String) (batch : Bool) (ppCore : Bool)
    (firstTrace : Bool)
    -- the address-space top (address-space-bound slice, 2026-09-17): ONE value for
    -- both entry points — the desugarer's const-expr mini-run (via frontendTU →
    -- desugar) and the execution driver (initial_driver_state) — from `--address-space-top`
    (addressSpaceTop : Int)
    (callFn : Option (String × List Int)) (traceNodes : Bool)
    (libc : Option (String × List String))
    (progArgs : List String)
    (exportLean : Option String) (exportKeep : List String) (exportPrune : Bool)
    (exportPrefix : String) (exportSource : Option String)
    (tunits : List (String × translation_unit)) : IO UInt8 := do
  -- Progress chatter: human mode only (batch and pp-core keep stdout clean)
  let quiet := batch || ppCore
  let say (s : String) : IO Unit := unless quiet do IO.println s
  -- Per-TU parse summary — kept ABOVE the stdlib load so single-TU chatter
  -- stays byte-identical to the pre-multi-TU driver
  for (_, tunit) in tunits do
    let (TUnit decls) := tunit
    let (funcs, declCount, other) := countDecls decls
    say s!"cerberus-lean: parsed {List.length decls} external declarations"
    say s!"  functions: {funcs}, declarations: {declCount}, other: {other}"

  -- Load core stdlib (once, before any TU digest is set — std.core symbols
  -- are interned with digest "" by CoreParser.mkSym, matching OCaml where
  -- the prelude parse happens before any Cerb_fresh.set_digest)
  say "  loading core stdlib..."
  -- Z-01: the library file is stamped with its path so that
  -- CerbLocation.isLibraryLocation holds for its nodes (pipeline.ml:29-35
  -- loads `Filename.concat (in_runtime "libcore") "std.core"`;
  -- core_parser.mly:1571 regions). Bug-hunt BUG-2 (2026-09-29): the path is
  -- built from the resolved runtime exactly as the oracle builds it, so the
  -- stamp is also the oracle's string (the exact library test holds).
  let stdCorePath := filenameConcat (filenameConcat runtime "libcore") "std.core"
  -- pipeline.ml:36-37: the oracle reports a missing stdlib as an error
  unless ← System.FilePath.pathExists stdCorePath do
    refuseRuntime s!"couldn't find the Core standard library file (looked at: `{stdCorePath}'); the runtime was resolved from --runtime / CERB_INSTALL_PREFIX (DIR/lib/cerberus-lib/runtime)"
  let stdContent ← IO.FS.readFile stdCorePath
  let stdFile ← match CoreParser.parseLibraryFile stdCorePath stdContent with
    | .ok f => pure f
    | .error e => throw (IO.Error.userError s!"failed to parse std.core: {e}")
  let allStdDecls := stdFile.funs ++ stdFile.procs ++ stdFile.builtins
  say s!"    raw: {stdFile.funs.length} fun, {stdFile.procs.length} proc, {stdFile.builtins.length} builtin = {allStdDecls.length} total"
  let allStd := stdFile.funs ++ stdFile.procs ++ stdFile.builtins
  let (ailnames, stdFunMap) := loadCoreStdlib stdFile
  say s!"    ailnames: {List.length (fmapElements ailnames)} entries"
  say s!"    stdlib funs: {List.length (fmapElements stdFunMap)} entries"

  -- Load implementation file
  say "  loading implementation..."
  -- pipeline.ml:47 `Filename.concat (core_stdlib_path ()) ("impls/" ^ impl_name ^ ".impl")`
  -- under the same runtime tree (Z-01; BUG-2 as above)
  let implPath := filenameConcat (filenameConcat runtime "libcore") "impls/gcc_4.9.0_x86_64-apple-darwin10.8.0.impl"
  -- pipeline.ml:48-49: missing impl file is an error on the oracle too
  unless ← System.FilePath.pathExists implPath do
    refuseRuntime s!"couldn't find the implementation file (looked at: `{implPath}')"
  let implContent ← IO.FS.readFile implPath
  let implFile ← match CoreParser.parseLibraryFile implPath implContent with
    | .ok f => pure f
    | .error e => throw (IO.Error.userError s!"failed to parse impl file: {e}")
  let coreImpl := loadCoreImpl implFile
  say s!"    impl constants: {List.length (fmapElements coreImpl)} entries"

  -- Build the implementation
  say "  building implementation..."
  let coreEvalStuff : Fmap String sym × fun_map Unit × impl :=
    (ailnames, stdFunMap, coreImpl)

  -- Per-TU frontend fold — mirror of backend/driver/main.ml:153-156:
  --   except_foldlM (fun core_files (is_lib, file) ->
  --     frontend ... file core_std >>= fun core_file ->
  --     return (core_file::core_files)) [] ... files
  -- The accumulator is REVERSE-consed (first file ends up LAST) and is
  -- handed to Core_linking.link as-is — mirrored exactly here. Failures
  -- short-circuit in file order, like except_foldlM.
  --
  -- --libc: the libc library file is processed FIRST, before the user
  -- TUs, exactly as the OCaml driver folds `core_libraries … @ files`
  -- (main.ml:150-156) — so it ends up LAST in the reverse-consed list
  -- handed to Core_linking.link, mirroring the oracle's link order.
  let mut coreFiles : List (file Unit) := []
  -- Effect-retirement C1 (S1 ruling [USER 2026-08-31]): the ONE
  -- fresh-symbol stream, seeded here and threaded through every phase
  -- (per-TU desugar + const-expr mini-runs + elaboration) and into the
  -- run-init seed below — collisions impossible by construction; the
  -- former 2^20 desugar/ambient stratification is gone.
  let mut supply : Nat := 0
  match libc with
  | some (libcCore, libcTus) =>
    match ← loadLibc runtime quiet supply addressSpaceTop coreEvalStuff ailnames stdFunMap coreImpl libcCore libcTus with
    | .error code => return code
    | .ok (libcFile, supply') => coreFiles := [libcFile]; supply := supply'
  | none => pure ()
  for (digest, tunit) in tunits do
    -- Frontend-only per-TU digest; execution receives `runDigest tunits`.
    -- Before the TU's frontend stages — mirror of
    -- `Cerb_fresh.set_digest filename` at the top of the OCaml c_frontend
    -- (backend/common/pipeline.ml:181; ref cell util/cerb_fresh.ml:7-10).
    -- The digest is the ORACLE'S: `Digest.file` of the C source, carried
    -- by the cabs-json (main.ml --cabs-json path; CabsImport.parseJson,
    -- fail-closed) — zero-discrepancy Z3 (Z-28): symbol digests order the
    -- linked globals (merge_globs), so the value itself is behaviour in
    -- libc mode. (Until Z3 this hashed the cabs-json text, a different
    -- value under which every program global sorted after the libc's.)
    -- Placement note: OCaml sets the digest before its C PARSE; our Cabs
    -- deserialization already happened in main — harmless, Cabs carries
    -- no Symbol.sym, so no symbol is created before the set.
    -- BaseIO variant: a discarded pure call is dead-code-eliminated
    -- (CerbTags set/reset pattern, arc-4 S3b).
    let _ ← (CerberusFresh.setDigestIO digest : BaseIO Unit)
    match ← frontendTU quiet supply addressSpaceTop coreEvalStuff ailnames stdFunMap coreImpl tunit with
    | .error code => return code
    | .ok (coreFile, supply') => coreFiles := coreFile :: coreFiles; supply := supply'

  -- Link the translated Core files — main.ml:278-281:
  --   prelude >>= main >>= begin function
  --     | [] -> assert false | f::fs -> Core_linking.link (f::fs) end
  -- link = List.foldl (link_aux) over the reverse-consed list
  -- (core_linking.lem:309-316; extern-map merge by identifier with
  -- tentative-definition resolution, link_extern core_linking.lem:10-46).
  -- The run-time cross-TU call remap `core_extern =
  -- Core_linking.create_extern_symmap file` (core_linking.lem:319-328) is
  -- already live in the generated driver (driver.lem:1512).
  match link coreFiles with
  | .Exception (loc, cause) =>
    let msg := match cause with
      | CORE_LINKING (DuplicateExternalName (Identifier _ str)) =>
        s!"linking failed: duplicate external name: {str}"
      | CORE_LINKING DuplicateMain => "linking failed: duplicate main"
      | CORE_LINKING IncompatibleCallingConvention =>
        "linking failed: incompatible calling convention"
      | _ => "linking failed"
    if quiet then
      -- deviation note (as for other frontend failures): OCaml prints
      -- linking errors via Pp_errors on stderr only (main.ml runM
      -- Exception branch); we emit a batch Error line on stdout —
      -- fail-closed either way, exit 1 both sides
      IO.println s!"Error \{msg: \"{msg} at {CerbLocation.stringFromLocation loc}\"}"
      return 1
    else
      IO.println s!"  linking failed!"
      IO.println s!"    at: {CerbLocation.stringFromLocation loc}"
      IO.println s!"    cause: {msg}"
      return 0
  | .Result coreFile =>
    -- chatter only for a real multi-TU link: single-file human-mode
    -- output stays byte-identical to the pre-multi-TU driver
    if tunits.length != 1 then
      say s!"  linking succeeded! ({tunits.length} translation units)"
    -- C1: the driver-level tag bookkeeping (main.ml:284-285
    -- reset+set from the LINKED file) is GONE — the load→seed loop is
    -- closed: the value in hand (runFile.tagDefs below) seeds the
    -- execution directly (documented divergence from the OCaml driver's
    -- global writes, mirror doctrine).

    -- --pp-core: signature-level dump of the (linked) Core, then stop
    -- (no execution). See the ppCoreSignature module note for the
    -- granularity limitation.
    if ppCore then
      ppCoreSignature coreFile
      return 0

    -- --export-lean DIR: write the linked Core, with the values execution
    -- starts from, as Lean modules following the C files (CoreLeanSource),
    -- then stop.
    if let some path := exportLean then
      -- A position is kept when its file name starts with one of the
      -- `exportKeep` prefixes (kept as is), or contains `/PREFIX` (an
      -- absolute path; rebased to start at PREFIX). Every other location
      -- becomes unknown.
      let keepFile (file : String) : Option String :=
        exportKeep.findSome? fun dir =>
          if file.startsWith dir then some file else
          match file.splitOn ("/" ++ dir) with
          | [_, rest] => some (dir ++ rest)
          | _ => none
      -- PATH is a directory; module `A.B.C` goes to `PATH/A/B/C.lean`.
      let dir : System.FilePath := path
      -- the kept C files, so the doc comments can quote each declaration
      let mut texts : Std.HashMap String String := {}
      if let some root := exportSource then
        for (_, kept) in CoreLeanSource.sourceFiles coreFile keepFile do
          let path : System.FilePath := (root : System.FilePath) / kept
          unless ← path.pathExists do
            IO.eprintln s!"cerberus-lean: --export-source: no {path}"
            return 2
          texts := texts.insert kept (← IO.FS.readFile path)
      match CoreLeanSource.moduleSources coreFile supply (runDigest tunits) keepFile exportPrune
          exportPrefix texts.get? with
      | .error msg =>
        IO.eprintln s!"cerberus-lean: --export-lean refused: {msg}"
        return 2
      | .ok (mods, st) =>
        for (name, text) in mods do
          let file := (name.splitOn ".").foldl (fun (p : System.FilePath) (c : String) => p / c) dir
          if let some parent := file.parent then IO.FS.createDirAll parent
          IO.FS.writeFile (file.toString ++ ".lean") text
        IO.eprintln s!"export: funs {st.funs}, stdlib {st.stdlib}, globs {st.globs}, tagDefs {st.tagDefs}, types {st.types}, modules {st.modules}, bytes {st.bytes}"
        return 0

    runLinked batch firstTrace addressSpaceTop callFn traceNodes progArgs
      supply (runDigest tunits) coreFile

/-! ## Entry point -/

/-- THE HARNESS DEFAULT FUEL (`--fuel N`, fuel-parameter arc 2026-09-04).
    Fuel is a PARAMETER of the semantics — the LemLib `[LemFuel]` instance
    every fuel'd function reads — instantiated exactly once, here, at the
    executable's entry ([USER 2026-09-03]: fuel "is an execution parameter
    that 'doesn't matter' … a parameter which can be chosen as 10^8 or any
    other value when calling the interpreter"; "Defaults that are chosen
    eg. in test suites are fine"). This is THE ONLY PLACE a fuel numeral
    may live in this repository: no generated module, seam, test or
    speclab file may carry one (`scripts/check_no_fuel_numerals.sh`, which
    allowlists exactly the definition line below and the `letI` that
    builds the instance in `main`). 10^8 is the former budget of the
    driver family (docs/2026-09-02_fuel-arc-design.md §4 sizing: past
    every gate lane's timeout, reachable only by measure.sh-scale probes);
    it is a harness choice, overridable per run, and no theorem depends
    on it. -/
def defaultFuel : Nat := 100000000  -- FUEL-DEFAULT (the one allowed fuel numeral)

/-- The default top of the address space — the concrete allocator's initial cursor
    (`CerbMem.initialMemState`, `MemState.lastAddress`), a PARAMETER of the semantics since
    the address-space-bound slice (2026-09-17; [USER 2026-09-16] "the semantics should be
    quantified over such bounds"). Upstream's value (`memory/concrete/impl_mem.ml:508` before
    the slice; now `Driver_ocaml.address_space_top_default`), so matched mode is unchanged;
    overridable per run by `--address-space-top N`; the ONE address-space numeral the Lean
    text may carry (`scripts/check_no_fuel_numerals.sh`, the A-shapes). It enters the run at
    its TWO entry points — the desugarer (the const-expr mini-run's driver state) and the
    execution driver — from this one value. -/
def defaultAddressSpaceTop : Int := 0xFFFFFFFFFFFF  -- ADDRESS-SPACE-DEFAULT (the one allowed address-space numeral)

/-- The address-space top's DOMAIN (C4, pre-merge audit + the consumer's review, 2026-09-18): an
    address must fit an LP64 pointer, so `0 < top < 2^(8 · sizeof_pointer)` = `2^64` — derived from
    `CerberusImpl.sizeof_pointer = some 8` (ocaml_implementation.ml `DefaultImpl.sizeof_pointer =
    Some 8`, the fork oracle's converter derives the same bound), not a numeral of its own; a missing
    pointer size (`none`) makes the domain EMPTY — every top is refused (fail-closed). The consumer's
    invariant `MemWF.la_wf` needs `lastAddress ≤ 2^64` and `la_pos` positivity; consumer theorems
    quantify `∀ top` under this domain. -/
def addressSpaceLimit : Nat := match CerberusImpl.sizeof_pointer with
  | some bytes => 2 ^ (8 * bytes)
  | none => 0

/-- Zero-discrepancy Z-24/Z-25 (charter §2.3; [USER 2026-09-03] Q7: REFUSE,
    do not plumb): every `--`-prefixed token the positional parser does not
    accept is REFUSED — loud (exit 2) and feature-ATTRIBUTED (exception class
    (c): "a LOUD, feature-attributed refusal where the oracle answers is
    allowed; a different answer, or a silent absorption, never is"). It used
    to become a FILE NAME (`uncaught exception: no such file or directory …
    file: --switches=PNVI`, rc 1 — loud but not attributed; the same for
    `--concurrency` and for a KNOWN flag out of its canonical position,
    e.g. `--batch x.json --first`). -/
def refuseFlag (flag : String) : IO Unit := do
  let feature :=
    if flag == "--iso" then
      "the ISO switch set (switches.ml:144-151 `set_iso_switches`: strict_pointer_arith, strict_reads, zap_dead_pointers, strict_pointer_equality, strict_pointer_relationals, PNVI_ae_udi) is not supported — each of its switches is refused under --switches, and the oracle's rm_unspecs Core pass it enables (backend/common/pipeline.ml:579) has no Lean counterpart"
    else if flag == "--concurrency" then
      "concurrency is not supported by this port (the oracle's own --concurrency mode is non-functional at b9aeedcb4: `internal error: CONCURRENCY IS BROKEN`); matched mode runs atomics sequentially on both engines"
    else if flag == "--batch" || flag == "--pp-core" || flag == "--parse-core" || flag == "--first" then
      "known flag out of its canonical position (`--batch`, `--pp-core` or `--parse-core` must be argv[0]; `--first` must immediately follow `--batch`/`--pp-core`)"
    else
      "unknown flag; this port accepts only --batch | --pp-core | --parse-core (argv[0]), --first, --stdin, --libc <core> --libc-tu <json>, --call <f> [--call-args <ints>], --args <str>, --trace-nodes, --fuel <N>, --address-space-top <N>, --runtime <DIR>, --switches PNVI_ae_udi (every other switch set is refused)"
  IO.eprintln s!"cerberus-lean: refused — {flag}: {feature} (see VALIDATION.md, zero-discrepancy Z-24)"
  IO.Process.exit 2

/-- The refusal reason for ONE element of a REFUSED `--switches` value (PNVI arc S1,
    2026-10-05; S4, 2026-10-07; design docs/2026-10-04_pnvi-ae-udi-design.md §B.4.2, §D.3,
    §F.3, §F.4, §F.13). The names are the oracle's (`ocaml_frontend/switches.ml:60-102`
    `read_switch`). Since S4 exactly ONE switch set is supported — `--switches=PNVI_ae_udi`
    alone (`judgeSwitches`), validated against the oracle under the same switch by
    `scripts/test_pnvi.sh`; every other value is refused, each element with its own reason.
    The oracle is FAIL-OPEN on an unknown name (switches.ml:140-141: "failed to parse
    switch '…' --> ignoring." and the run proceeds without it); this port refuses
    (exception class (c), §F.4). -/
def switchRefusalReason (name : String) : String :=
  match name with
  | "PNVI_ae_udi" =>
    "PNVI-ae-udi (switches.ml:82-83, SW_PNVI `AE_UDI) is supported alone or with permissive_pointer_arith; this list is not a supported combination"
  | "PNVI" | "PNVI_ae" =>
    "the PNVI-plain / PNVI-ae provenance variants (switches.ml:78-81) are not validated by any lane (their shared impl_mem.ml arms are mirrored, design §F.3, but only PNVI_ae_udi has a differential lane)"
  | "permissive_pointer_arith" =>
    "the permissive pointer-arithmetic mode is supported only together with PNVI_ae_udi"
  | "strict_pointer_arith" =>
    "the pointer-arithmetic mode switch (switches.ml:62-65, SW_pointer_arith) is not supported: its impl_mem.ml arms are loud kills in CerbMem (seam-hygiene H2)"
  | "strict_reads" =>
    "strict reads (switches.ml:66-67) are not supported: CerbMem's arm is a loud kill, and the oracle's rm_unspecs Core pass (backend/common/pipeline.ml:579) has no Lean counterpart"
  | "forbid_nullptr_free" | "zap_dead_pointers" | "strict_pointer_equality" | "strict_pointer_relationals" | "zero_initialised" =>
    "this impl_mem.ml switch is not supported: its arm is a loud kill in CerbMem (seam-hygiene H2)"
  | "inner_arg_temps" =>
    "the inner-argument-temporaries elaboration (switches.ml:84-85) is not supported: it needs the alternative runtime std_inner_arg_temps.core (backend/common/pipeline.ml:34), which this port does not load"
  | "permissive_printf" =>
    "permissive printf (switches.ml:86-87) is not validated by any lane"
  | "CHERI" =>
    "CHERI is the memory model of the separate cerberus-cheri executable (backend/driver/main.ml:134-137); this port has the concrete model only, and CerbGlobal.is_CHERI is a build constant"
  | "revoke_dead_pointers" | "cornucopia" | "at_magic_comments" | "magic_comment_char_dollar" | "copy_prop" =>
    "this upstream switch (switches.ml:92-101) has no counterpart in this port's lem model"
  | _ =>
    "unknown switch name — the oracle prints `failed to parse switch '…' --> ignoring.` and runs on without it (switches.ml:140-141, fail-open: alone, that is the DEFAULT semantics); this port refuses (design §G R20, R-PNVI-12)"

/-- The override class of a switch name (switches.ml:104-132 `pred`): two names of one
    class in one list make the oracle DROP the later one ("switch '…' would override a
    previous switch --> ignoring.", switches.ml:136-139, fail-open). -/
def switchClass (name : String) : String :=
  match name with
  | "strict_pointer_arith" | "permissive_pointer_arith" => "pointer_arith"
  | "PNVI" | "PNVI_ae" | "PNVI_ae_udi" => "PNVI"
  | "revoke_dead_pointers" | "cornucopia" => "revocation"
  | other => other

/-- The oracle's switch-name domain: the names `read_switch` maps to `Some _`
    (switches.ml:61-102). Any other name is "failed to parse" there (:140-141) — it never
    enters the list, so it can never be overridden nor override (PNVI arc S4 Part 1: a
    repeated UNKNOWN name used to be labelled "override" here; S1 review L5 item 2). -/
def knownSwitch (name : String) : Bool :=
  name ∈ ["strict_pointer_arith", "permissive_pointer_arith", "strict_reads",
    "forbid_nullptr_free", "zap_dead_pointers", "strict_pointer_equality",
    "strict_pointer_relationals", "PNVI", "PNVI_ae", "PNVI_ae_udi", "inner_arg_temps",
    "permissive_printf", "zero_initialised", "CHERI", "revoke_dead_pointers", "cornucopia",
    "at_magic_comments", "magic_comment_char_dollar", "copy_prop"]

/-- REFUSE a `--switches` value (`flag` is the argv text: `--switches=V` or
    `--switches V`): one line per element, each naming the element and its reason, then
    exit 2. Called for every value but the one supported set (`judgeSwitches`); an empty
    value too (cmdliner's `opt (list string)`, backend/driver/main.ml:589-591). The override class is recorded
    only for a KNOWN name, as the oracle's `set` does (switches.ml:134-141: an unknown name
    is "failed to parse" every time, never "would override"). -/
def refuseSwitches (flag value : String) : IO Unit := do
  let names := value.splitOn ","
  let mut seen : List String := []
  for n in names do
    let reason :=
      if n.isEmpty then "an empty switch name"
      else if knownSwitch n && seen.contains (switchClass n) then
        s!"{switchRefusalReason n}; ALSO it would override a previous switch of the same class in this list (the oracle prints `switch '…' would override a previous switch --> ignoring.` and drops it, switches.ml:136-139, fail-open; design §G R20, R-PNVI-11)"
      else switchRefusalReason n
    IO.eprintln s!"cerberus-lean: refused — {flag}: this semantics switch set is not supported (supported sets: `PNVI_ae_udi`, optionally with `permissive_pointer_arith`) — `{n}`: {reason} (see CONTRACT.md §2/§3 and VALIDATION.md, semantics switches)"
    if knownSwitch n then seen := seen ++ [switchClass n]
  IO.Process.exit 2

/-- Accept PNVI-ae-udi alone or with permissive pointer arithmetic, in either
    order. Other combinations, duplicates and unknown names still fail closed.
    Focused arithmetic evidence: scripts/test_permissive_pointer_arith.py. -/
def judgeSwitches (flag value : String) : IO (List CerbGlobal.CerbSwitch) := do
  if value == "PNVI_ae_udi" then return [.PNVI .AE_UDI]
  if value == "PNVI_ae_udi,permissive_pointer_arith" ||
     value == "permissive_pointer_arith,PNVI_ae_udi" then
    return [.PNVI .AE_UDI, .pointer_arith .PERMISSIVE]
  refuseSwitches flag value
  -- refuseSwitches exits 2; falling through would be an internal error (fail-closed)
  IO.eprintln "cerberus-lean: internal error: refuseSwitches returned"
  IO.Process.exit 2

/-- `--switches` given to `--parse-core` (S1 review L5 item 1): the value is judged by
    the switch parser itself (its own per-element refusal), never the generic
    "unknown flag" text; the supported set is refused HERE because the Core text parser
    runs no semantics, so a switch set would be silently ignored. `tok` is the
    `--switches…` token, `next?` the following argv word (the value of the space form). -/
def refuseSwitchesParseCore (tok : String) (next? : Option String) : IO Unit := do
  let (flag, value) ← if tok.startsWith "--switches=" then
      pure (tok, (tok.drop "--switches=".length).toString)
    else match next? with
      | some v => pure (s!"--switches {v}", v)
      | none => do
        IO.eprintln "cerberus-lean: --switches requires an argument"
        IO.Process.exit 1
  let _ ← judgeSwitches flag value
  IO.eprintln s!"cerberus-lean: refused — {flag}: --parse-core runs only the Core text parser, which reads no switch set; the switch would be silently ignored (see CONTRACT.md §2)"
  IO.Process.exit 2

def main (args : List String) : IO Unit := do
  -- Zero-discrepancy Z2-FL-03 (Z2 audit @ 9e86fe67c; fail-closed hygiene):
  -- a Lean `panic!` — this port's fail-stop mirror of every OCaml
  -- failwith/assert/uncaught exception (CerbFloat.truncToInt, CerbMem.killM
  -- and casePtrval, CerbUtils builtins, CerbDecode, LemLib.failwithI) —
  -- PRINTS and CONTINUES with `default` unless the runtime aborts: without
  -- LEAN_ABORT_ON_PANIC, `(int)NaN` printed `Defined {value: "Specified(0)",
  -- …}` exit 0 where the oracle is an uncaught Z.Overflow, exit 125 — a
  -- crash-to-VALUE conversion, the banned fail-open shape. The runtime tests
  -- PRESENCE of the variable (measured: "1", "0" and "" all abort; unset
  -- continues). Every harness sets it (scripts/common.sh run_cerberus_lean;
  -- LEAN_ABORT_ON_PANIC=1 at each direct invocation) — refuse otherwise.
  match ← IO.getEnv "LEAN_ABORT_ON_PANIC" with
  | some _ => pure ()
  | none =>
    IO.eprintln "cerberus-lean: refused — LEAN_ABORT_ON_PANIC is not set: a Lean panic! (this port's fail-stop mirror of every OCaml failwith/assert/uncaught exception) would print and then CONTINUE with a default value, converting a crash into a verdict; set LEAN_ABORT_ON_PANIC=1 (every harness does: scripts/common.sh run_cerberus_lean; see VALIDATION.md, zero-discrepancy Z2-FL-03)"
    IO.Process.exit 2
  -- CLI ORDER CONTRACT (sem:N7, arc-14 S1 F6; zero-discrepancy Z-24): this
  -- is a POSITIONAL flag parser (not cmdliner like the oracle). The
  -- contract: `--batch` or `--pp-core` must be argv[0]; `--first` must
  -- immediately follow it; `--parse-core` is matched against the raw args
  -- head. Any other `--`-prefixed token — an unknown flag, an oracle flag
  -- this port does not support, or a KNOWN flag out of position — is
  -- REFUSED by `refuseFlag` (loud, attributed, exit 2); it used to be
  -- silently treated as a filename. `--stdin` is the one `--` positional.
  -- --batch: machine-parseable output for the differential harness
  -- --pp-core: signature-level elaborated-Core dump (test_elab.sh)
  let batchMode := args.head? == some "--batch"
  let ppCoreMode := args.head? == some "--pp-core"
  let parseCoreMode := args.head? == some "--parse-core"
  let rest0 := if batchMode || ppCoreMode then args.drop 1 else args
  -- --first (optional, after --batch/--pp-core): single-trace execution —
  -- the Lean-side analogue of OCaml `--mode=random` (one trace instead of
  -- the exhaustive set). See CerbND.runND1 (arc-5 S3 seam).
  -- audit F3: a bare leading `--first` (no `--batch`/`--pp-core`) is NOT
  -- the single-trace switch — it stays in the scan and is refused
  let firstTrace := (batchMode || ppCoreMode) && rest0.head? == some "--first"
  let rest1 := if firstTrace then rest0.drop 1 else rest0
  -- --libc <pinned.core> --libc-tu <json> … (arc-6 S1): additive libc
  -- mode — load the pinned libc Core text dump plus the 12 metadata TU
  -- cabs-jsons (scripts/libc_prep.sh --jsons) and link the resulting
  -- library file BEFORE the user TUs (see loadLibc / runPipeline).
  -- [AGENT:S1] explicit flags (not an auto-load convention): libc-enabled
  -- runs are NEW harness modes per the arc-6 charter; standing corpora
  -- must be byte-for-byte unaffected, which an auto-load could silently
  -- break.
  -- --call <fname> [--call-args <int,int,…>]: the function-call harness
  -- mode — execute the designated function on the given integer
  -- arguments (injected as Core values via CerbCall.driveCall) instead
  -- of drive's main-startup path. --trace-nodes additionally
  -- prints the branch-0 ND-node labels (Step-coverage evidence; works in
  -- the main-startup mode too).
  let mut libcCore : Option String := none
  let mut libcTus : List String := []
  let mut callName : Option String := none
  let mut callArgsStr : Option String := none
  let mut progArgsStr : Option String := none
  let mut traceNodes : Bool := false
  -- --export-lean DIR: write the linked Core as Lean modules, then stop
  let mut exportLean : Option String := none
  -- --export-keep DIR (repeatable): keep source positions in files under DIR
  let mut exportKeep : List String := []
  -- --export-all-procs: do not remove procedures unreachable from main
  let mut exportPrune : Bool := true
  -- --export-prefix NAME: module prefix for the files whose positions are kept
  let mut exportPrefix : String := "Kept"
  -- --export-source ROOT: the kept files (as exported, relative to ROOT), whose
  -- declarations the doc comments quote
  let mut exportSource : Option String := none
  -- --fuel <N> (fuel-parameter arc): the run's fuel, a positive integer;
  -- absent = `defaultFuel`. Accepted anywhere after the mode flag (the
  -- same canonical position as --libc/--call/--args); zero or a
  -- non-numeral is REFUSED (exit 2): a run at fuel 0 kills at the first
  -- bind — never a verdict — and a silent fallback to the default would
  -- be the fail-open shape the working practices ban.
  let mut fuelStr : Option String := none
  -- --address-space-top <N> (address-space-bound slice, 2026-09-17): the run's
  -- address-space top, a positive integer; absent = `defaultAddressSpaceTop`
  -- (upstream's value); zero or a non-numeral is REFUSED (exit 2), exactly like
  -- --fuel — a silent fallback would be the fail-open shape the practices ban.
  let mut addressSpaceTopStr : Option String := none
  -- --runtime DIR / --runtime=DIR (bug-hunt BUG-2, 2026-09-29): the oracle's
  -- flag of the same name (backend/driver/main.ml:436-438); see resolveRuntime
  let mut runtimeArg : Option String := none
  -- --switches <list> / --switches=<list> (PNVI arc S1, 2026-10-05): the oracle's
  -- cmdliner option (backend/driver/main.ml:589-591, `opt (list string)`, both forms;
  -- design §F.13). PARSED here, JUDGED below (`judgeSwitches`: `PNVI_ae_udi` alone is
  -- accepted, every other value refused); a repeated option is refused as cmdliner
  -- does. (flag text as given, value)
  let mut switchesArg : Option (String × String) := none
  let mut restArgs : List String := []
  -- --parse-core consumes its file list itself (below); nothing to scan
  let mut pending := if parseCoreMode then [] else rest1
  while true do
    match pending with
    | [] => break
    | "--libc" :: v :: rest => libcCore := some v; pending := rest
    | "--libc-tu" :: v :: rest => libcTus := libcTus ++ [v]; pending := rest
    | "--call" :: v :: rest => callName := some v; pending := rest
    | "--call-args" :: v :: rest => callArgsStr := some v; pending := rest
    | "--args" :: v :: rest =>
      -- the oracle's cmdliner rejects a repeated option ("option --args cannot be
      -- repeated", exit 124); taking the last value silently was a divergence
      -- (bug-hunt fixes pre-merge audit L3)
      if progArgsStr.isSome then
        IO.eprintln "cerberus-lean: option --args cannot be repeated (as the oracle's command line)"
        IO.Process.exit 2
      progArgsStr := some v; pending := rest
    | "--trace-nodes" :: rest => traceNodes := true; pending := rest
    | "--export-lean" :: v :: rest => exportLean := some v; pending := rest
    | "--export-keep" :: v :: rest => exportKeep := exportKeep ++ [v]; pending := rest
    | "--export-all-procs" :: rest => exportPrune := false; pending := rest
    | "--export-prefix" :: v :: rest => exportPrefix := v; pending := rest
    | "--export-source" :: v :: rest => exportSource := some v; pending := rest
    | "--fuel" :: v :: rest => fuelStr := some v; pending := rest
    | "--address-space-top" :: v :: rest => addressSpaceTopStr := some v; pending := rest
    | "--runtime" :: v :: rest =>
      if runtimeArg.isSome then refuseRuntime "option --runtime cannot be repeated (the oracle's cmdliner rejects it, exit 124; pre-merge audit L3)"
      runtimeArg := some v; pending := rest
    | "--switches" :: v :: rest =>
      if switchesArg.isSome then
        IO.eprintln "cerberus-lean: option --switches cannot be repeated (as the oracle's command line)"
        IO.Process.exit 2
      switchesArg := some (s!"--switches {v}", v); pending := rest
    | ["--libc"] | ["--libc-tu"] | ["--call"] | ["--call-args"]
    | ["--args"] | ["--fuel"] | ["--address-space-top"] | ["--runtime"] | ["--switches"] =>
      IO.eprintln "cerberus-lean: --libc/--libc-tu/--call/--call-args/\
        --args/--fuel/--address-space-top/--runtime/--switches require an argument"
      IO.Process.exit 1
    | a :: rest =>
      if a.startsWith "--runtime=" then
        if runtimeArg.isSome then refuseRuntime "option --runtime cannot be repeated (the oracle's cmdliner rejects it, exit 124; pre-merge audit L3)"
        runtimeArg := some (a.drop "--runtime=".length).toString; pending := rest; continue
      if a.startsWith "--switches=" then
        if switchesArg.isSome then
          IO.eprintln "cerberus-lean: option --switches cannot be repeated (as the oracle's command line)"
          IO.Process.exit 2
        switchesArg := some (a, (a.drop "--switches=".length).toString); pending := rest; continue
      -- Z-24: a `--` token here is not a file name (except `--stdin`). A `--switches`
      -- value already scanned is judged FIRST, so `--switches=V --batch …` reports V's
      -- own verdict before the position refusal (S1 review L5 item 1)
      if a.startsWith "--" && a != "--stdin" then
        if let some (flag, value) := switchesArg then
          let _ ← judgeSwitches flag value
        refuseFlag a
      restArgs := restArgs ++ [a]; pending := rest
  -- --switches (PNVI arc S4): the run's switch set — `CerbGlobal.defaultSwitches` (= `[]`,
  -- switches.ml:47-48) without the option, `[.PNVI .AE_UDI]` for `--switches=PNVI_ae_udi`;
  -- every other value is refused here (`judgeSwitches`). Supplied below beside the fuel.
  let switchSet : List CerbGlobal.CerbSwitch ← match switchesArg with
    | none => pure CerbGlobal.defaultSwitches
    | some (flag, value) => judgeSwitches flag value
  -- --args "ARG1 ARG2 ..." — the oracle's flag of the same name
  -- (backend/driver/main.ml:512-514): one string, split on whitespace
  -- runs (main.ml:111-113, Str.split "[ \t]+" — empty pieces dropped,
  -- leading/trailing whitespace ignored). Extra argv entries for the
  -- executed program's main; "cmdname" is always prepended at the
  -- drive call (pipeline.ml:598,602 mirror in runPipeline).
  let progArgs : List String := match progArgsStr with
    | none => []
    | some s => ((s.replace "\t" " ").splitOn " ").filter (· ≠ "")
  let fuel : Nat ← match fuelStr with
    | none => pure defaultFuel
    | some s => match s.toNat? with
      | some n =>
        if n == 0 then do
          IO.eprintln s!"cerberus-lean: refused — --fuel {s}: the fuel must be a positive integer (fuel 0 kills at the first bind: never a verdict; see VALIDATION.md, fuel)"
          IO.Process.exit 2
        else pure n
      | none => do
        IO.eprintln s!"cerberus-lean: refused — --fuel {s}: not a decimal numeral (the fuel is a positive integer; default {defaultFuel}; see VALIDATION.md, fuel)"
        IO.Process.exit 2
  -- The SHARED GRAMMAR (C5, re-review R1; [AGENT orchestrator], mirror doctrine): "nonempty ASCII
  -- decimal digits, 0 < value < 2^64" on BOTH engines. `String.toNat?` alone also accepts single
  -- underscore separators (`6_4` = 64), which the fork's digit-only converter refuses — so the
  -- string is validated as digits FIRST; `--fuel` (Lean-only, no mirror) keeps its parser.
  let addressSpaceTop : Int ← match addressSpaceTopStr with
    | none => pure defaultAddressSpaceTop
    | some s => match (if !s.isEmpty && s.all Char.isDigit then s.toNat? else none) with
      | some n =>
        -- the DOMAIN 0 < top < 2^64 (addressSpaceLimit; the fork oracle's converter refuses with the
        -- SAME sentence — mirror doctrine; only its exit code is cmdliner's)
        if n == 0 || n ≥ addressSpaceLimit then do
          IO.eprintln s!"cerberus-lean: refused — --address-space-top {s}: the address-space top must fit an LP64 pointer: 0 < top < 2^64 (CerberusImpl.sizeof_pointer = some 8; the allocator's initial cursor; default {defaultAddressSpaceTop}; see VALIDATION.md, address-space top)"
          IO.Process.exit 2
        else pure (n : Int)
      | none => do
        IO.eprintln s!"cerberus-lean: refused — --address-space-top {s}: not a decimal numeral (the address-space top is a decimal positive integer, 0 < top < 2^64; default {defaultAddressSpaceTop}; see VALIDATION.md, address-space top)"
        IO.Process.exit 2
  let callFn : Option (String × List Int) ← match callName, callArgsStr with
    | none, none => pure none
    | none, some _ => do
      IO.eprintln "cerberus-lean: --call-args without --call"
      IO.Process.exit 1
    | some n, argStr => do
      let parts := match argStr with
        | none => []
        | some "" => []
        | some s => s.splitOn ","
      let mut vals : List Int := []
      for p in parts do
        match p.trim.toInt? with
        | some v => vals := vals ++ [v]
        | none => do
          IO.eprintln s!"cerberus-lean: --call-args: not an integer: {p}"
          IO.Process.exit 1
      pure (some (n, vals))
  let libc : Option (String × List String) ← match libcCore, libcTus with
    | some c, tus =>
      if tus.isEmpty then do
        IO.eprintln "cerberus-lean: --libc requires at least one --libc-tu (metadata TU cabs-json)"
        IO.Process.exit 1
      else pure (some (c, tus))
    | none, [] => pure none
    | none, _ :: _ => do
      IO.eprintln "cerberus-lean: --libc-tu without --libc"
      IO.Process.exit 1
  -- Effect-retirement C1 (charter section 5): the debug-level global is
  -- DELETED — the model returns values, the driver prints; the former
  -- human-mode level-2 write here was already vestigial (its only
  -- reader, the dbg_trace print_debug, was referenced by nothing).
  -- Also gone (charter sections 3.4/7.1): the ambient fresh counter and
  -- its 2^20 floor probe — the fresh-symbol supply is a SINGLE stream
  -- threaded explicitly from runPipeline (S1 ruling); collisions are
  -- impossible by construction, so there is no stratification invariant
  -- left to probe.
  if args.length == 0 then
    selfTest
    return

  -- --parse-core: test the Core text parser
  if args.head? == some "--parse-core" then
    let files := args.drop 1
    -- audit F2 (Z-24 contract): this branch consumed every token as a file
    -- name; a `--` token here is refused like everywhere else
    let mut rest := files
    while true do
      match rest with
      | [] => break
      | a :: more =>
        if a == "--switches" || a.startsWith "--switches=" then refuseSwitchesParseCore a more.head?
        if a.startsWith "--" && a != "--stdin" then refuseFlag a
        rest := more
    let mut failures := 0
    for file in files do
      let input ← if file == "--stdin" then do
          let mut buf := ""
          let mut done_ := false
          while !done_ do
            let line ← (← IO.getStdin).getLine
            if line.isEmpty then done_ := true
            else buf := buf ++ line
          pure buf
        else IO.FS.readFile file
      let label := if file == "--stdin" then "<stdin>" else file
      match CoreParser.parseFile input with
      | .ok cf =>
        let total := cf.funs.length + cf.procs.length + cf.impls.length +
                     cf.tagDefs.length + cf.globs.length + cf.builtins.length
        if total == 0 && input.trim.length > 0 then
          IO.eprintln s!"{label}: ERROR: parser returned .ok but 0 declarations from {input.trim.length} non-whitespace chars"
          IO.eprintln s!"{label}: first 120 chars of input: {input.take 120}"
          failures := failures + 1
        else
          IO.println s!"{label}: Core file: {cf.funs.length} fun, {cf.procs.length} proc, {cf.impls.length} def/impl, {cf.tagDefs.length} struct/union, {cf.globs.length} glob, {cf.builtins.length} builtin"
      | .error e =>
        IO.eprintln s!"{label}: ERROR: {e}"
        failures := failures + 1
    if failures > 0 then
      IO.Process.exit 1
    return

  if (batchMode || ppCoreMode) && restArgs.isEmpty then
    IO.eprintln "usage: cerberus-lean [--batch|--pp-core] [--first] FILE.json [FILE2.json ...]"
    IO.Process.exit 1

  -- Default: parse Cabs JSON (one per translation unit) and run pipeline.
  -- All cabs-jsons are deserialized up front (fail-fast on any parse
  -- error); the OCaml driver's per-file C PARSE is interleaved with its
  -- frontend fold (main.ml:153-156), but our deserialization is the
  -- Lean-side half of the --cabs-json bridge, not the C parse — its
  -- placement is an artifact of the split and carries no symbol state
  -- (Cabs has no Symbol.sym). Per-TU digests are set inside
  -- runPipeline's frontend loop (pipeline.ml:181 mirror).
  -- bug-hunt BUG-2: the runtime is resolved like the oracle's (resolveRuntime),
  -- never searched for relative to the working directory
  let runtimeDir ← resolveRuntime runtimeArg
  let contents ← readInputs restArgs
  let mut tunits : List (String × translation_unit) := []
  let mut idx := 0
  for content in contents do
    idx := idx + 1
    match CabsImport.parseJsonWithFiles content with
    | .error e =>
      if batchMode then
        IO.println s!"Error \{msg: \"cabs-json parse error: {CerbEscape.text e}\"}"
      IO.eprintln s!"cerberus-lean: parse error: {e}"
      IO.Process.exit 1
    | .ok (digest, tunit, files) =>
      -- bug-hunt BUG-3: suffix-library ⇒ exact-library, or refuse
      let name := restArgs.getD (idx - 1) "<input>"
      refuseLibraryLocations runtimeDir s!"the input {name}" files
      tunits := tunits ++ [(digest, tunit)]
  -- The ONE instantiation of the ambient fuel (fuel-parameter arc): every
  -- fuel'd function below `runPipeline` reads this instance; nothing else
  -- in the repository builds one (`scripts/check_no_fuel_numerals.sh`).
  -- Beside it, the ONE instance of the switch set (PNVI arc S1, 2026-10-05; S4,
  -- 2026-10-07): `⟨switchSet⟩` — the default `CerbGlobal.defaultSwitches` (= `[]`,
  -- switches.ml:47-48) unless `--switches=PNVI_ae_udi` was given (judged above); one
  -- general path, the set only selects the arms (no PNVI-only entry point). No other
  -- instance of `CerbGlobal.Switches` exists in this repository
  -- (speedbump: `scripts/check_no_fuel_numerals.sh` rule W1).
  let code ← (letI : LemFuel := ⟨fuel⟩; letI : CerbGlobal.Switches := ⟨switchSet⟩; runPipeline runtimeDir batchMode ppCoreMode firstTrace
    addressSpaceTop callFn traceNodes libc progArgs exportLean exportKeep exportPrune exportPrefix exportSource tunits)
  if code != 0 then
    IO.Process.exit code
