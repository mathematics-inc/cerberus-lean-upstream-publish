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

set_option autoImplicit true

/-! Execution of a linked Core file, shared by `cerberus-lean` (Main) and by
runners of exported Core modules (`--export-lean`). Moved unchanged from
Main.lean. -/

/-! ## Batch output (differential harness support)

Machine-parseable output mode matching the OCaml driver's `--batch` format
(`backend/common/driver_ocaml.ml`, `string_of_batch_output`), which is also
the format the prototype's `test_interp.sh` parses:

  Defined {value: "Specified(42)", stdout: "", stderr: "", blocked: "false"}
  Undefined {ub: "UB045a_division_by_zero", stderr: "", loc: "..."}
  Error {msg: "..."}

Multiple executions get `EXECUTION i:` header lines, like OCaml.
The `loc:` field is `CerbLocation.simpleLocation` (= `Cerb_location.
simple_location`, driver_ocaml.ml:113/127), the `stderr:` field of an
Undefined line is the KILLED state's accumulated stderr (batch_drive,
driver_ocaml.ml:173-181) and the stdout/stderr fields are `String.escaped`
(batchEscape) — all byte-for-byte with the oracle since the zero-discrepancy
arc (Z-03, Z-72, Z2-P-01; UB location is behaviour [USER 2026-09-03]).
Deviations from OCaml (hand-written latitude, documented):
  - Unspecified/OtherValue payloads print via the arc-10 S3 REAL mirrors of
    String_core.string_of_value (CerbPP.stringFromCore_value; residual
    divergences are enumerated in CerbPP.lean and stay "<...>"-bracketed)
  - the oracle also prints `Time spent: %f seconds` on the TOOL's stderr
    (main.ml:159-160) — not behaviour, not mirrored (zero-discrepancy
    Z2-P-08; every lane filters `^Time spent`)
  - non-UB frontend failures emit an `Error {msg: ...}` line on stdout
    (OCaml puts them on stderr only); fail-closed either way
  - runND returning zero executions emits `Error {msg: "cerberus-lean:
    runND returned no executions"}` + exit 1 where OCaml prints nothing and
    exits 0. DECLARED loud boundary — zero-discrepancy Z-73, RULED
    [USER 2026-09-03] Q8 = A ("Agree re Q2-10"): keep the fail-closed
    refusal (a silent exit 0 with no verdict is the fail-open shape the
    working practices ban); the oracle's silent success is an upstream
    question (tray candidate). The fuel arc's `runNDFuel` exhaustion leaf
    has the same shape and inherits this classification. Also declared in
    VALIDATION.md ("Known, LOUD limits of the Lean driver"). -/

/-- OCaml `String.escaped` = `Bytes.unsafe_escape` (the switch's
    `lib/ocaml/bytes.ml:170-212`), by BYTE class: `"` `\\` `\n` `\t` `\r` `\b`
    → the two-character short form; `' ' .. '~'` (32..126) verbatim; every
    other byte → `\ddd`, three DECIMAL digits (`48 + a/100`, `48 + (a/10)
    mod 10`, `48 + a mod 10`). The driver's io strings hold one Char per
    program BYTE (0..255), so the char code IS the byte; the result is pure
    ASCII, hence no UTF-8 re-encoding of bytes >= 0x80 can occur. Zero-
    discrepancy Z2-P-01: the previous subset passed control bytes raw,
    dropped `\b`, and re-encoded 0xC3 0xA9 as four UTF-8 bytes
    (tests/immaculate/libc/zd-z2p01-{stdout,stderr}_escape.c). -/
def batchEscape (s : String) : String :=
  CerbEscape.byteChars s

/-- Batch rendering of the final core value — mirrors OCaml's exit
    selection in batch_drive (driver_ocaml.ml:162-171) composed with
    string_of_batch_exit (driver_ocaml.ml:42-52), which re-wraps the exit
    and prints it with String_core.string_of_value (= Pp_core.pp_value):
    * Specified-integer: case_integer_value → `Specified n` →
      re-wrapped via Impl_mem.integer_ival n (provenance ERASED) →
      pp "Specified(<n>)" — hence the explicit branch here (a direct
      pp of the original value would leak provenance at debug ≥ 3).
    * everything else round-trips to pp_value of the value itself
      (Unspecified included: "Unspecified('<ctype>')", pp_core.ml:304-308). -/
def batchExitValue (v : value) : String :=
  match v with
  | Vloaded (LVspecified (OVinteger ival)) =>
    match eval_integer_value ival with
    | some n => s!"Specified({n})"
    | none => CerbPP.stringFromCore_value v  -- OtherValue arm (driver_ocaml.ml:167)
  | v => CerbPP.stringFromCore_value v

/-- Batch rendering of a driver error — mirrors driver_ocaml.ml:22-30
    (string_of_driver_error). The DErr_memory arm uses the lem-generated
    Show instance for mem_error (driver_ocaml.ml:25-26 calls
    `Mem_common.instance_Show_Show_Mem_common_mem_error_dict.show_method`;
    `Lem_Show.show0` is the same generated method here) so `Error {msg:}`
    lines agree textually with the oracle (arc-14 S1 F1: the previous
    hand-rolled "memory error" summaries were an undocumented divergence,
    visible on the G1 relational kill-paths).
    The DErr_core_run arm mirrors `Pp_errors.string_of_core_run_cause`
    (pp_errors.ml:499-509) text for text (zero-discrepancy Z2-P-05; the
    previous local `Illformed_program: …` renderings were an EXC(a)
    divergence, closed): the four constant strings, and `Unresolved_symbol`
    as `"unresolved symbol: " ^ Pp_ail.pp_id sym ^ " at " ^
    Cerb_location.location_to_string loc` — `pp_id` is
    `Pp_symbol.to_string_pretty` (pp_ail.ml:96; `CerbMem.ppSymbol` is its
    mirror) and `location_to_string` is `CerbLocation.stringFromLocation`.
    The embedded symbol NUMBER inside an Illformed_program payload differs
    by construction (the two supplies' absolute numbering — Z-04/tray 17,
    EXC(a) text). -/
def driverErrorBatchMsg : driver_error → String
  | .DErr_core_run cause =>
    match cause with
    | .Illformed_program s => s!"ill-formed program: `{s}'"        -- pp_errors.ml:500-501
    | .Found_empty_stack s => s!"found an empty stack: `{s}'"      -- :502-503
    | .Reached_end_of_proc => "reached the end of a procedure"     -- :504-505
    | .Unknown_impl => "unknown implementation constant"           -- :506-507
    | .Unresolved_symbol loc sym =>
      s!"unresolved symbol: {CerbMem.ppSymbol sym} at {CerbLocation.stringFromLocation loc}"  -- :508-509
  | .DErr_memory merr => Lem_Show.show0 merr    -- driver_ocaml.ml:25-26
  | .DErr_concurrency s => s!"Concurrency error: {s}"
  | .DErr_other s => s

/-- Bug-hunt BUG-4 (2026-09-29; record `docs/2026-09-29_bug-hunt-fixes-record.md`
    §S4): print a batch `Undefined` line with the `ub:` payload as BYTES. The
    oracle prints the field with `%s` and no escaping
    (`backend/common/driver_ocaml.ml:134-138`, `Printf.bprintf buf "Undefined
    {ub: \"%s\", stderr: \"%s\", loc: \"%s\"}"
    (Undefined.stringFromUndefined_behaviour ub) (String.escaped stderr)
    (Cerb_location.simple_location loc)`), so an `Invalid_format` payload — the
    only UB constructor carrying program data (`undefined.lem:530`, rendered
    `"Invalid_format[" ^ str ^ "]"` at `:1103` from the format string's bytes,
    `formatted.lem:845/859/874`) — reaches stdout as the format's raw bytes. In
    Lean those bytes are byte-carrier Chars (one per C byte, CabsImport
    `getByteStr`); `IO.println` UTF-8-encoded each carrier ≥ 0x80 as two bytes.
    Here every payload Char is written as the one byte it carries. The other
    fields are unchanged: `stderr` is already the `String.escaped` mirror
    (`CerbEscape.byteChars`, callers) and `loc` is the ASCII
    `simple_location` mirror. A payload Char above U+00FF has no OCaml
    counterpart (the producer's byte-domain invariant is broken): refused,
    exit 2, never re-encoded. -/
def printUndefinedLine (ub : String) (stderr : String) (loc : String) : IO Unit := do
  let mut payload := ByteArray.empty
  for c in ub.toList do
    if c.toNat < 256 then payload := payload.push c.toNat.toUInt8
    else
      IO.eprintln s!"cerberus-lean: refused — batch UB payload: the undefined-behaviour text holds U+{(Nat.toDigits 16 c.toNat).asString}, outside the byte domain the oracle's byte string can hold (driver_ocaml.ml:134-138 prints the payload's bytes); the byte-carrier invariant of the model's strings is broken (see VALIDATION.md, bug hunt BUG-4)"
      IO.Process.exit 2
  let out ← IO.getStdout
  out.write ("Undefined {ub: \"".toUTF8 ++ payload ++ s!"\", stderr: \"{stderr}\", loc: \"{loc}\"}\n".toUTF8)

/-- Execute a linked Core file: the part of `runPipeline` after linking.
    `supply` is the fresh-symbol supply after elaboration and `digest` the
    run digest (`runDigest` of the translation units). -/
def runLinked [LemFuel] [CerbGlobal.Switches] (batch : Bool) (firstTrace : Bool)
    (addressSpaceTop : Int) (callFn : Option (String × List Int)) (traceNodes : Bool)
    (progArgs : List String) (supply : Nat) (digest : String) (coreFile : file Unit) :
    IO UInt8 := do
    let say (s : String) : IO Unit := unless batch do IO.println s
    -- Step 4: Prepare for execution (mirrors driver_ocaml.ml)
    say "  preparing for execution..."
    let runFile := convert_file coreFile
    -- C1: CerbMem's struct/union layout reads receive runFile.tagDefs by
    -- VALUE (reader_consumer, mem.lem) — no global set is needed or
    -- possible.
    let fsState := CerbFS.fs_initial_state
    -- Entry shape (b), charter section 1.3: the supply-parameterized
    -- pure constructor — one draw (the run-init seed) from the stream.
    -- The address-space top is the run's parameter (the same value the
    -- desugarer was seeded with above).
    let (drSt, _supplyFinal) := initial_driver_state supply addressSpaceTop (digest) runFile fsState
    say s!"  executing Core..."
    -- Reader seed: execution-slice entry — the linked table, passed as
    -- the value in hand (the load→seed loop is closed).
    -- --call: run the designated function on the injected argument
    -- values via CerbCall.driveCall (drive with the startup symbol
    -- resolved by name + the caller protocol for the parameters)
    -- instead of drive's main-startup path.
    -- argv — pipeline.ml:598,602: ("cmdname" :: args) both batch and
    -- non-batch; progArgs is the parsed --args list (empty without the
    -- flag, so the historical ["cmdname"] argv is byte-unchanged).
    let driverAction := match callFn with
      | none => drive runFile.enumDefs runFile.tagDefs false runFile ("cmdname" :: progArgs)
      | some (fname, argInts) =>
        CerbCall.driveCall runFile.enumDefs runFile.tagDefs (digest) runFile fname
          (argInts.map CerbCall.intValue)
    -- --first (arc-5 S3): single-trace runner for programs whose exhaustive
    -- trace set is combinatorially large (libxml2-scale differentials);
    -- see CerbND.runND1 for the OCaml counterpart + divergence record.
    -- --trace-nodes (arc-7 S3): branch-0 single trace + ND-node labels on
    -- stdout (Step-coverage evidence instrument; see CerbND.runND1Trace).
    let (nodeLabels, execs) :=
      if traceNodes then
        CerbND.runND1Trace (fun (k : step_kind) => Lem_Show.show0 k)
          driverAction drSt
      else
        ([], if firstTrace then CerbND.runND1 driverAction drSt
             else CerbND.runND driverAction drSt)
    for l in nodeLabels do
      IO.println s!"NODE {l}"
    if batch then
      if execs.length == 0 then
        IO.println "Error {msg: \"cerberus-lean: runND returned no executions\"}"
        return 1
      let multiple := execs.length > 1
      let mut idx := 0
      for (status, _trace, _finalSt) in execs do
        if multiple then IO.println s!"EXECUTION {idx}:"
        match status with
        | .Active result =>
          IO.println s!"Defined \{value: \"{batchExitValue result.dres_core_value}\", stdout: \"{batchEscape result.dres_stdout}\", stderr: \"{batchEscape result.dres_stderr}\", blocked: \"{if result.dres_blocked then "true" else "false"}\"}"
        | .Killed st reason =>
          -- batch_drive (driver_ocaml.ml:173-181): every Killed arm carries
          -- `String.concat "" (Dlist.toList dr_st.core_state.io.stderr)` —
          -- the KILLED state's accumulated stderr; the plain batch printer
          -- renders it on the Undefined line only (:127 `String.escaped
          -- stderr`; the Error line :138 prints msg alone). Zero-discrepancy
          -- Z-72: this printed `stderr: ""` literally.
          let killedStderr := batchEscape
            (lemListFoldr String.append "" (toList st.core_state0.io.stderr))
          match reason with
          | .Undef0 _loc [] =>
            -- OCaml batch_drive parity: empty UB list is an Error
            IO.println "Error {msg: \"[empty UB, probably a cerberus BUG]\"}"
          | .Undef0 loc (ub :: _) =>
            -- OCaml batch_drive parity: first UB only; loc via simple_location (Z-03)
            printUndefinedLine (stringFromUndefined_behaviour ub) killedStderr (CerbLocation.simpleLocation loc)
          | .Error0 loc msg =>
            if loc == CerbFail.modelFailStopLoc then
              IO.println (CerbFail.batchRecord msg)
            else IO.println s!"Error \{msg: \"{msg}\"}"
          | .Other err =>
            IO.println s!"Error \{msg: \"{driverErrorBatchMsg err}\"}"
        idx := idx + 1
      -- Exit code per OCaml main.ml runM: single Defined → 0,
      -- single Undefined/Error → 1, multiple executions → 0.
      match execs with
      | [(.Active _, _, _)] => return 0
      | [(.Killed _ _, _, _)] => return 1
      | _ => return 0
    else
      IO.println s!"  executions: {execs.length}"
      for (status, _trace, _finalSt) in execs do
        match status with
        | .Active result =>
          IO.println s!"  result: Active"
          match result.dres_core_value with
          | Vloaded (LVspecified (OVinteger ival)) =>
            match eval_integer_value ival with
            | some n => IO.println s!"  return value: {n}"
            | none => IO.println s!"  return value: (could not evaluate)"
          | v => IO.println s!"  return value: (non-integer)"
        | .Killed _st reason =>
          match reason with
          | .Undef0 loc ubs =>
            IO.println s!"  result: Killed (undefined behaviour)"
            IO.println s!"    at: {CerbLocation.stringFromLocation loc}"
            for ub in ubs do
              IO.println s!"    ub: {stringFromUndefined_behaviour ub}"
          | .Error0 loc msg =>
            IO.println s!"  result: Killed ({if loc == CerbFail.modelFailStopLoc then "model fail-stop" else "error"}: {msg})"
            IO.println s!"    at: {CerbLocation.stringFromLocation loc}"
          | .Other err =>
            match err with
            | .DErr_core_run cause =>
              let causeStr := match cause with
                | .Illformed_program s => s!"Illformed_program: {s}"
                | .Found_empty_stack s => s!"Found_empty_stack: {s}"
                | .Reached_end_of_proc => "Reached_end_of_proc"
                | .Unknown_impl => "Unknown_impl"
                | .Unresolved_symbol loc (Symbol _ n _) =>
                  s!"Unresolved_symbol: Symbol(_, {n}, _) at {CerbLocation.stringFromLocation loc}"
              IO.println s!"  result: Killed (core_run error: {causeStr})"
            | .DErr_memory merr =>
              match merr with
              | .MerrInternal s => IO.println s!"  result: Killed (memory internal: {s})"
              | .MerrOther s => IO.println s!"  result: Killed (memory other: {s})"
              | .MerrOutsideLifetime s => IO.println s!"  result: Killed (outside lifetime: {s})"
              | .MerrAccess _ _ => IO.println s!"  result: Killed (memory access error)"
              | _ => IO.println s!"  result: Killed (memory error)"
            | .DErr_concurrency s => IO.println s!"  result: Killed (concurrency: {s})"
            | .DErr_other s => IO.println s!"  result: Killed (other: {s})"
      return 0

