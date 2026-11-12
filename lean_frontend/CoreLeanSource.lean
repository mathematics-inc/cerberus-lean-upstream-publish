import CoreLeanSourceGen
import CoreSymsGen

/-! The Lean modules for a linked Core file (`cerberus-lean --export-lean`).

The modules follow the C source: each file whose positions are kept
(`keepFile`) and whose functions the program reaches has a module with one
definition per function, named as in C, in source order, holding the
function's Core procedure: `PREFIX.Noise` for `noise.c` (`PREFIX.NoiseH` for
its header). Every other procedure (library, environment, Cerberus runtime)
is defined in namespace `Support`, written as parts `Support.PartNN` of at
most `partBytes` each.
`Program.Helpers` holds the helpers the definitions use,
`Program.Types` the named C types, and `Program` defines, under
`namespace LinkedCore`:
* `file : file Unit`, the linked Core file (tags, globals, and the procedure
  maps, which refer to the definitions above),
* `supply : Nat`, the fresh-symbol supply after elaboration,
* `digest : String`, the run digest, and
* `coreDigest : String`, the MD5 of `file`'s canonical text (`canonicalDigest`),
which are the values `runPipeline` passes to `runLinked`. A runner that
imports `Program` and calls `runLinked` with them executes the program
as `cerberus-lean` does on the C input, and can check `coreDigest`.

Before rendering, procedures and tags that execution cannot reach are removed
(`prune`), and source locations outside the selected directories are
replaced by the unknown location (`Builder.keepFile`). -/

namespace CoreLeanSource

def symsOf {α : Type} (c : α → Syms) (x : α) : Array sym := ((c x).run #[]).2

abbrev SymSet := Fmap sym Unit

def SymSet.mem (s : SymSet) (x : sym) : Bool := (fmapLookupBy symbol_compare x s).isSome

def SymSet.add (s : SymSet) (x : sym) : SymSet := fmapAddBy symbol_compare x () s

/-- Keep the entries of a map whose key satisfies `p`, inserting in key
order with `cmp`, the map's key comparator. -/
def fmapRestrict {β : Type} (cmp : sym → sym → LemOrdering) (p : sym → Bool)
    (m : Fmap sym β) : Fmap sym β :=
  (fmapElements m).foldl (fun acc (k, v) => if p k then fmapAddBy cmp k v acc else acc) fmapEmpty

def stdlibByName (f : file Unit) (name : String) : List sym :=
  (fmapElements f.stdlib).filterMap fun (s, _) =>
    match s with
    | .Symbol _ _ (.SD_Id n) => if n == name then some s else none
    | _ => none

/-- The procedures (`funs`, `stdlib`) reachable from `main`, the globals,
the implementation constants, the object environment and the procedures
the driver calls by name, following every symbol a reached definition
mentions, its `funinfo`, its extern group and its tag definition. -/
def reachable (f : file Unit) : SymSet := Id.run do
  let colDecl := col_generic_fun_map_decl colNone colNone
  let colInfo := colProd colNone (colProd colNone (colProd col_ctype
    (colProd (colList (colProd (colOption colSym) col_ctype)) colNone)))
  let mut roots : Array sym := #[]
  if let some m := f.main then roots := roots.push m
  roots := roots ++ symsOf (colList (colProd colSym (col_generic_globs colNone colNone))) f.globs
  roots := roots ++ symsOf (colFmap colNone (col_generic_impl_decl colNone)) f.impl0
  roots := roots ++ symsOf (colFmap colNone (colList (colProd colSym col_ctype))) f.visible_objects_env0
  roots := roots ++ (stdlibByName f "conv_loaded_int").toArray
  -- extern groups: every symbol of an external name stands for the others
  let mut groups : Fmap sym (List sym) := fmapEmpty
  for (_, (ss, _)) in fmapElements f.extern do
    for s in ss do groups := fmapAddBy symbol_compare s ss groups
  let mut seen : SymSet := fmapEmpty
  let mut todo := roots.toList
  -- each symbol is expanded once, so the loop ends after at most |symbols| rounds
  for _ in [0:(symsOf (col_generic_file colNone colNone) f).size + roots.size + 1] do
    match todo with
    | [] => break
    | s :: rest =>
      todo := rest
      if seen.mem s then continue
      seen := seen.add s
      let decl := (fmapLookupBy symbol_compare s f.funs).orElse fun _ =>
        fmapLookupBy symbol_compare s f.stdlib
      if let some d := decl then todo := (symsOf colDecl d).toList ++ todo
      if let some i := fmapLookupBy symbol_compare s f.funinfo then
        todo := (symsOf colInfo i).toList ++ todo
      if let some g := fmapLookupBy symbol_compare s groups then todo := g ++ todo
      if let some t := fmapLookupBy symbol_compare s f.tagDefs then
        todo := (symsOf (colProd colNone col_tag_definition) t).toList ++ todo
  return seen

/-- `f` without unreachable `funs`, `stdlib`, `funinfo` and `tagDefs`
entries (a tag is reached through a symbol of a reached definition, type or
tag definition). Globals are all kept: their allocation order is observable. -/
def prune (f : file Unit) : file Unit :=
  let r := reachable f
  let cmp := @Lem_Map.mapKeyCompare sym _
  { f with funs := fmapRestrict cmp r.mem f.funs,
           stdlib := fmapRestrict cmp r.mem f.stdlib,
           funinfo := fmapRestrict cmp r.mem f.funinfo,
           tagDefs := fmapRestrict cmp r.mem f.tagDefs }

/-- Every symbol of the file has one description per (digest, number), so
the key-type comparator of a symbol map (which also compares descriptions)
agrees with `symbol_compare` on every symbol the program uses. -/
def checkSymbols (f : file Unit) : Except String Unit := do
  let all := symsOf (col_generic_file colNone colNone) f
  let mut seen : Fmap sym symbol_description := fmapEmpty
  for s in all do
    let .Symbol dg n d := s
    match fmapLookupBy symbol_compare s seen with
    | none => seen := fmapAddBy symbol_compare s d seen
    | some d' => if d' != d then throw s!"symbol {dg}/{n} has two descriptions"
  return ()

structure Stats where
  funs : Nat
  stdlib : Nat
  globs : Nat
  tagDefs : Nat
  types : Nat
  modules : Nat
  bytes : Nat

/-- The MD5 of the canonical text of `f` under the location policy `keepFile`
(procedures enter as the MD5 of their own canonical text). Two files with
the same digest are equal values, up to MD5 collisions. -/
def canonicalDigest (f : file Unit) (keepFile : String → Option String) : String :=
  let ((), b) := ((src_generic_file srcUnit srcUnit) f).run { keepFile, canonical := true }
  CerberusFresh.md5Hex (flatAll (if h : b.acc.size = 1 then b.acc[0] else .app "" b.acc))

/-- The largest `Support` part, in bytes (bounds elaboration memory). -/
def partBytes : Nat := 6000000

def zeroPad (w : Nat) (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Lean keywords that are also C identifiers; such names are quoted `«»`. -/
def leanKeywords : Std.HashSet String := Std.HashSet.ofList [
  "abbrev", "at", "axiom", "break", "by", "calc", "catch", "class", "continue", "def",
  "deriving", "do", "else", "end", "example", "exists", "export", "extends", "finally",
  "for", "forall", "from", "fun", "have", "if", "import", "in", "include", "inductive",
  "infix", "infixl", "infixr", "instance", "lemma", "let", "local", "macro", "match",
  "mut", "mutual", "namespace", "noncomputable", "nofun", "nomatch", "notation",
  "omit", "opaque", "open", "partial", "postfix", "prefix", "private", "protected",
  "rec", "return", "scoped", "section", "set_option", "show", "sorry", "structure",
  "suffices", "syntax", "then", "theorem", "this", "try", "universe", "unless",
  "unsafe", "using", "variable", "where", "with", "Prop", "Sort", "Type"]

def leanIdent (s : String) : String :=
  let ok := !s.isEmpty && s != "_" && s.all (fun c => c.isAlphanum || c == '_')
    && !(s.get 0).isDigit
  if ok && !leanKeywords.contains s then s else "«" ++ s ++ "»"

/-- `wgt_time` ↦ `WgtTime`, `curve25519-fiat32` ↦ `Curve25519Fiat32`. -/
def camel (s : String) : String :=
  let parts := (s.splitOn "_").flatMap (·.splitOn "-") |>.flatMap (·.splitOn ".")
    |>.filter (!·.isEmpty)
  let r := String.join (parts.map String.capitalize)
  if r.isEmpty then "X" else if (r.get 0).isDigit then "N" ++ r else r

def stemOf (path : String) : String :=
  let base := (path.splitOn "/").getLast!
  match base.splitOn "." with
  | [b] => b
  | parts => ".".intercalate parts.dropLast

def dirsOf (path : String) : List String := (path.splitOn "/").dropLast

/-- The module for a procedure whose (exported) file is `f`: kept files get
a module each, `prefix.<Stem>`; every other procedure is in `Support`. -/
def moduleOfFile (pfx : String) (f : String) : String :=
  if f.isEmpty then "Support" else pfx ++ "." ++ camel (stemOf f)

/-- One procedure to define. -/
structure ProcItem where
  key : sym
  decl : generic_fun_map_decl Unit Unit
  file : String
  line : Nat
  name : String
  stdlib : Bool

def declLoc? : generic_fun_map_decl Unit Unit → Option CerbLocation.Loc
  | .Proc l _ _ _ _ | .ProcDecl l _ _ | .BuiltinDecl l _ _ => some l
  | .Fun _ _ _ => none

/-- Module names for the kept files, distinct per file: a header colliding
with a `.c` file gets `H`; other collisions get the parent directory. -/
def moduleNames (pfx : String) (files : List String) : Std.HashMap String String := Id.run do
  let mut byName : Std.HashMap String (List String) := {}
  for f in files.eraseDups do
    let m := moduleOfFile pfx f
    byName := byName.insert m (f :: byName.getD m [])
  let mut out : Std.HashMap String String := {}
  for (m, fs) in byName.toList do
    for f in fs do
      let headers := fs.filter (·.endsWith ".h")
      let others := fs.filter (!·.endsWith ".h")
      let m' := if fs.length == 1 then m
        else if f.endsWith ".h" then (if headers.length == 1 then m ++ "H"
                                      else m ++ "H" ++ camel ((dirsOf f).getLastD ""))
        else if others.length == 1 then m
        else m ++ camel ((dirsOf f).getLastD "")
      out := out.insert f m'
  return out

def moduleDoc (m : String) (file : String) : String :=
  if m == "Support" then
    "Part of `Support`: the procedures the program uses outside the files with their own " ++
    "modules (library, environment and Cerberus runtime), one definition per function, " ++
    "named as in C."
  else
    s!"The C functions of `{file}` that the program uses, in source " ++
    "order: one definition per function, named as in C, holding its Core procedure."

def header (imports : List String) (doc : String) : String :=
  String.join (imports.map (s!"import {·}\n")) ++ s!"\n/-! {doc} -/\n\n"
    ++ "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"

/-- The files with kept positions that hold procedure definitions:
`(file as found in the Core, file as exported)`. The caller reads them so that
doc comments can quote each function's C declaration (`moduleSources`). -/
def sourceFiles (coreFile : file Unit) (keepFile : String → Option String) :
    List (String × String) :=
  ((fmapElements coreFile.funs).filterMap fun (_, d) => do
    let raw ← locFile? ((declLoc? d).getD .unknown)
    let kept ← keepFile raw
    return (raw, kept)).eraseDups

/-- The C text of the declaration that starts on line `line` (1-based) of
`text`: from that line up to the function body's opening brace. -/
def declText (text : String) (line : Nat) : Option String := do
  let lines := (text.splitOn "\n").drop (line - 1)
  guard (line > 0 && !lines.isEmpty)
  let mut out : Array String := #[]
  for l in lines do
    match l.splitOn "{" with
    | before :: _ :: _ =>
      let b := before.trimRight
      if !b.isEmpty then out := out.push b
      return "\n".intercalate out.toList
    | _ => out := out.push l.trimRight
    if out.size > 40 then none
  none

/-- The modules for a linked Core file: `(module name, source)`. -/
def moduleSources (coreFile : file Unit) (supply : Nat) (digest : String)
    (keepFile : String → Option String) (doPrune : Bool) (pfx : String)
    (source : String → Option String) :
    Except String (List (String × String) × Stats) := do
  checkSymbols coreFile
  let f := if doPrune then prune coreFile else coreFile
  let tuDigest := match f.main with
    | some (.Symbol dg _ _) => dg
    | none => ""
  -- the procedures, by module
  let mut items : Array ProcItem := #[]
  for (stdlib, m) in [(false, f.funs), (true, f.stdlib)] do
    for (k, d) in fmapElements m do
      let loc := (declLoc? d).getD .unknown
      let some name := symName? k | throw s!"procedure without a C name: {symKey k}"
      -- the file as the export shows it (positions outside the kept
      -- directories are unknown), so the layout is a function of the value
      let file := ((locFile? loc).bind keepFile).getD ""
      items := items.push ⟨k, d, file, if file.isEmpty then 0 else locLine loc, name, stdlib⟩
  let files := ((items.filter (!·.stdlib)).toList.map (·.file)).filter (!·.isEmpty)
  let names := moduleNames pfx files
  let moduleOf (it : ProcItem) : String :=
    if it.stdlib then "Support" else names.getD it.file "Support"
  let mut byModule : Std.HashMap String (Array ProcItem) := {}
  for it in items do
    let m := moduleOf it
    byModule := byModule.insert m ((byModule.getD m #[]).push it)
  let moduleList := (byModule.toList.map (·.1)).toArray.qsort (· < ·)
  -- kept files: their `Src` constants
  let kept := files.eraseDups
  let base (p : String) := (p.splitOn "/").getLast!
  let mut fileNames : Std.HashMap String String := {}
  for p in kept do
    let short := if (kept.filter (base · == base p)).length == 1 then base p else p
    fileNames := fileNames.insert p ("«" ++ short ++ "»")
  -- procedure references for the program module
  let mut procRefs : Std.HashMap String String := {}
  for m in moduleList do
    let mut seen : Std.HashSet String := {}
    for it in byModule.getD m #[] do
      if seen.contains it.name then throw s!"two procedures named {it.name} in {m}"
      seen := seen.insert it.name
      procRefs := procRefs.insert (symKey it.key) (m ++ "." ++ leanIdent it.name)
  let pv := P.mk (ty_src_generic_fun_map_decl srcUnit srcUnit) (src_generic_fun_map_decl srcUnit srcUnit)
  let filePr := src_generic_file srcUnit srcUnit
  let b0 : Builder := { keepFile, tuDigest, fileNames }
  -- counting pass: how often each nameable C type occurs
  let mut bc : Builder := { b0 with counting := true }
  for it in items do
    bc := ((pv.pr it.decl).run bc).2 |> fun b => { b with acc := #[] }
  bc := ((filePr f).run { bc with procRefs }).2
  let mut ctypeNames : Std.HashMap String String := {}
  let mut used : Std.HashSet String := {}
  let cands := bc.ctypeCount.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  for (key, n) in cands do
    let name := bc.ctypeCand.getD key ""
    if n ≥ 3 && !name.isEmpty && !used.contains name then
      ctypeNames := ctypeNames.insert key name
      used := used.insert name
  -- the procedure modules
  let mut b : Builder := { b0 with ctypeNames }
  let mut mods : Array (String × String) := #[]
  -- `Support` is written as parts of at most `partBytes`, in one namespace
  let mut partMods : Array String := #[]
  for m in moduleList do
    -- `Support` in the order the program declares its procedures (symbol
    -- numbers; Cerberus runtime procedures last)
    let symNum (it : ProcItem) : Nat := match it.key with | .Symbol _ n _ => n
    let its := if m == "Support" then
        (byModule.getD m #[]).qsort (fun x y =>
          (!x.stdlib && y.stdlib) || (x.stdlib == y.stdlib &&
            (symNum x < symNum y || (symNum x == symNum y && x.name < y.name))))
      else (byModule.getD m #[]).qsort (fun x y => x.line < y.line || (x.line == y.line && x.name < y.name))
    let mut defs : Array String := #[]
    for it in its do
      let (d, b') := (capture (pv.pr it.decl)).run b
      b := b'
      let proto := match fmapLookupBy symbol_compare it.key f.funinfo with
        | some (_, _, ret, params, variadic, _) =>
          let procNames : List String := match it.decl with
            | .Proc _ _ _ ps _ => ps.map fun (p : sym × core_base_type) => match p.1 with
              | .Symbol _ _ (.SD_ObjectAddress x) | .Symbol _ _ (.SD_Id x) => x
              | _ => ""
            | _ => []
          let named := params.zipIdx.map fun ((p : Option sym × ctype), i) =>
            ((p.1.bind symName?).getD (procNames.getD i ""), p.2)
          let args := named.map fun (n, t) => cDecl t n
          let args := if variadic then args ++ ["..."] else args
          some (cDecl ret (it.name ++ "(" ++ (if args.isEmpty then "void" else ", ".intercalate args) ++ ")"))
        | none => none
      let place := match keepFile it.file with
        | some p => if it.line > 0 then s!"\n\n`{p}:{it.line}`" else ""
        | none => ""
      -- the C declaration as written, when the file's text is supplied
      let quoted := (source it.file).bind (declText · it.line)
      let doc := match quoted, proto with
        | some q, _ => s!"/--\n```c\n{q}\n```{place} -/\n"
        | none, some p => s!"/-- `{p}`{place} -/\n"
        | none, none => if place.isEmpty then "" else s!"/--{place.drop 2} -/\n"
      defs := defs.push (doc ++ s!"def {leanIdent it.name} : Procedure :=\n  " ++ layout d 2 ++ "\n\n")
    let chunks : Array (Array String) := if m != "Support" then #[defs] else Id.run do
      let mut cs : Array (Array String) := #[]
      let mut cur : Array String := #[]
      let mut size := 0
      for d in defs do
        if size + d.utf8ByteSize > partBytes && !cur.isEmpty then
          cs := cs.push cur; cur := #[]; size := 0
        cur := cur.push d; size := size + d.utf8ByteSize
      return if cur.isEmpty then cs else cs.push cur
    for h : i in [:chunks.size] do
      let name := if m == "Support" then s!"Support.Part{zeroPad 2 (i + 1)}" else m
      partMods := partMods.push name
      let text := header ["Program.Types"] (moduleDoc m ((its[0]?.map (·.file)).getD ""))
        ++ "open Src\n\n" ++ s!"namespace {m}\n\n" ++ String.join chunks[i].toList ++ s!"end {m}\n"
      mods := mods.push (name, text)
  -- the program module
  let (fd, b') := (capture (filePr f)).run { b with procRefs }
  b := b'
  let program := header ("Program.Types" :: partMods.toList)
      "The linked program: its tags, globals and procedure maps (the procedures are the definitions of the modules above)."
    ++ "open Src\n\nnamespace LinkedCore\n\n"
    ++ "def file : file Unit :=\n  " ++ layout fd 2 ++ "\n\n"
    ++ s!"def supply : Nat := {supply}\n\n"
    ++ s!"def digest : String := {stringLiteral digest}\n\n"
    ++ "/-- The MD5 of `file`'s canonical text (`linked-run --check`). -/\n"
    ++ s!"def coreDigest : String := {stringLiteral (canonicalDigest f keepFile)}\n\nend LinkedCore\n"
  -- the helpers and the named types
  let srcDefs := String.join ((fileNames.toList.toArray.qsort (·.2 < ·.2)).toList.map fun (p, n) =>
    s!"def {n} : String := {stringLiteral p}\n")
  let helpers := header ["Driver"]
      "Helpers for the program's definitions. Each denotes the Core value it abbreviates."
    ++ "namespace Src\n\n/-- The digest of the program's translation unit, part of its symbols. -/\n"
    ++ s!"def digest : String := {stringLiteral tuDigest}\n\n" ++ srcDefs ++ "\nend Src\n\n"
    ++ s!"/-- The type of a procedure definition. -/\nabbrev Procedure : Type := {pv.ty}\n\n"
    ++ "/-- The program's identifier `x`, symbol number `n`. -/\n"
    ++ "def c! (x : String) (n : Nat) : sym := .Symbol Src.digest n (.SD_Id x)\n\n"
    ++ "/-- The Cerberus runtime's identifier `x`, symbol number `n`. -/\n"
    ++ "def rt! (x : String) (n : Nat) : sym := .Symbol \"\" n (.SD_Id x)\n\n"
    ++ "/-- The address of the program's object `x`, symbol number `n`. -/\n"
    ++ "def addr! (x : String) (n : Nat) : sym := .Symbol Src.digest n (.SD_ObjectAddress x)\n\n"
    ++ "/-- The program's unnamed symbol number `n` (`a_n` in Core's notation). -/\n"
    ++ "def a! (n : Nat) : sym := .Symbol Src.digest n .SD_None\n\n"
    ++ "/-- Line `l`, column `c` of file `f`. -/\n"
    ++ "def pt! (f : String) (l c : Nat) : CerbLocation.Loc := .point ⟨f, l, c⟩\n\n"
    ++ "/-- From line `l`, column `c` to line `l'`, column `c'` of file `f`. -/\n"
    ++ "def rg! (f : String) (l c l' c' : Nat) : CerbLocation.Loc :=\n  .region ⟨f, l, c⟩ ⟨f, l', c'⟩ .noCursor\n\n"
    ++ "/-- As `rg!`, with the cursor at line `lc`, column `cc`. -/\n"
    ++ "def rgc! (f : String) (l c l' c' lc cc : Nat) : CerbLocation.Loc :=\n"
    ++ "  .region ⟨f, l, c⟩ ⟨f, l', c'⟩ (.pointCursor ⟨f, lc, cc⟩)\n\n"
    ++ "/-- As `rg!`, with the cursor from line `l₁`, column `c₁` to line `l₂`, column `c₂`. -/\n"
    ++ "def rgr! (f : String) (l c l' c' l₁ c₁ l₂ c₂ : Nat) : CerbLocation.Loc :=\n"
    ++ "  .region ⟨f, l, c⟩ ⟨f, l', c'⟩ (.regionCursor ⟨f, l₁, c₁⟩ ⟨f, l₂, c₂⟩)\n"
  let types := header ["Program.Helpers"]
      "C types used often by the program, named after their C spelling (`ptr_` for a pointer to, `array_N_` for an array of)."
    ++ "namespace Ty\n\n"
    ++ String.join (b.typeDefs.toList.map fun (n, d) => s!"def {n} : ctype :=\n  {layout d 2}\n\n")
    ++ "end Ty\n"
  let all := [("Program.Helpers", helpers), ("Program.Types", types)] ++ mods.toList
    ++ [("Program", program)]
  let n {β : Type} (m : Fmap sym β) := (fmapElements m).length
  return (all, ⟨n f.funs, n f.stdlib, f.globs.length, n f.tagDefs, b.typeDefs.size,
                all.length, all.foldl (fun a (_, t) => a + t.utf8ByteSize) 0⟩)

end CoreLeanSource
