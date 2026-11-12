# The cerberus-lean contract

Status: **adopted 2026-09-29**; the operator decisions are in §5. Author: the orchestrator [AGENT], on [USER 2026-09-28]:
"Really the correct fix here is to much more explicitly define the contract that Cerberus Lean is trying to establish
and then for the features that are well-built, make sure that they're supported. For the ones that are not very
well-built, make sure that they're appropriately rejected." Occasion: the CerbFS path defect
(`docs/2026-09-28_cerbfs-path-hotfix-record.md`), a SERVED wrong answer in a surface the project never tried to
clone, with no discrepancy found in the core semantics.

## 1. What cerberus-lean promises

cerberus-lean is a Lean 4 artifact that is meant to mean **what the Cerberus OCaml implementation means**, for a
declared set of C programs and a declared configuration. Concretely, for every input, an execution ends in exactly one of:

1. **The same observable verdict as the oracle** — value, stdout, stderr, the UB it reports — under the documented
   observation comparison (VALIDATION §4); or
2. **A loud refusal** — a nonzero exit and a message that names the unsupported feature and the boundary it belongs to;
   or
3. **A resource outcome** — fuel exhaustion or a declared resource limit, never counted as agreement (class (b)); or
4. **A registered deviation** — one of the few [USER]-ruled ISO fixes (class (d)), a [USER]-ruled named deviation where
   the mismatch cannot easily be resolved (class (e), VALIDATION §2b), or a failure whose message text alone differs
   (class (a)).

There is no fifth outcome. **A different answer, or a silent absorption (a default, an errno, a zero, a success no-op),
where the oracle answers, is a defect by definition** — wherever in the tree it occurs, supported area or not. The
pathleak bug was a fifth outcome.

What the contract does NOT promise: ISO C conformance beyond the oracle's; agreement outside the declared configuration;
correctness of the oracle itself (the upstream tray records where we believe it is wrong); a proof of correspondence.
The evidence is differential testing on documented corpora plus kernel-checked local properties of the Lean artifact
(totality, axiom cone, fuel contracts); **testing samples behaviour and does not prove equivalence** (VALIDATION §9) —
which is exactly why every unmodelled surface must refuse rather than guess.

## 2. The declared configuration

Matched (default-switch) mode of the oracle at the fork merge-base `b9aeedcb4`; sequential execution; the concrete
memory model; LP64; `--nolibc` and libc modes as exercised by the lanes; explicit `--fuel` and address-space parameters.
**Semantics switches: PNVI_ae_udi, optionally with permissive_pointer_arith.**
The combination permits temporary out-of-allocation pointers and subtraction of concrete
addresses regardless of provenance. It does not permit null-pointer arithmetic or
out-of-bounds loads. `scripts/test_permissive_pointer_arith.py` compares eight focused
programs with OCaml under both configurations; this does not establish broad conformance. The switch set is a parameter of the semantics (`[CerbGlobal.Switches]`, PNVI arc S1, 2026-10-05). The binary
supplies the default `[]` unless `--switches=PNVI_ae_udi` is given (PNVI arc S4, 2026-10-07): then `[PNVI_ae_udi]`, and §1
applies with the oracle run under the SAME switch (`scripts/test_pnvi.sh`, LADDER Tier A row 14).
Adding `permissive_pointer_arith` in either order supplies both switches. Every other
`--switches` value — another switch name, plain `PNVI`/`PNVI_ae`, another mixed list, an override (R-PNVI-11), an unknown name
(R-PNVI-12) — and `--iso` is refused at the CLI (`Main.lean` `judgeSwitches`/`refuseSwitches`, per element; `refuseFlag`),
including where the oracle silently ignores the name. Inside the PNVI-ae-udi semantics, the upstream arms that crash,
print debug output or call themselves wrong are refused (§3, the R-PNVI rows); the default set is unchanged by all of
this.

**The address-space top: the default is the promise; other values are a proof-use parameter.** `--address-space-top N`
is a DELIBERATE lift of upstream's constant for proof use — [USER 2026-10-03] "we specifically want to lift the
address-space-top restriction for the sake of treating cerberus as a proof artifact. Agree on your recommendations with
that framing (we shouldn't revert work that allows the iris reasoning to work properly)". Its default mirrors upstream
exactly (`memory/concrete/impl_mem.ml` `last_address= Z.of_int 0xFFFFFFFFFFFF; (* TODO: this is a random impl-def
choice *)`, `Main.lean` `defaultAddressSpaceTop`), and §1 is promised at that default only. A NON-DEFAULT value is
outside the mirroring promise: pristine upstream has no such parameter, so there is nothing to mirror; the fork oracle's
own fork-only flag is an instrument (the tiny-top lane, LADDER A12), not the referent; and at very large tops (≥ 2^62)
objects become allocatable whose sizes OCaml's `Z.to_int` cannot represent, where the fork oracle would raise and Lean
computes (`docs/2026-10-03_total-arith-and-bookkeeping-record.md` §2.3 O-1). The fork's other memory models accept the
fork-only flag and IGNORE it (`memory/symbolic/impl_mem.ml` `initial_mem_state (_address_space_top: Z.t)`,
`memory/cheri-coq/impl_mem.ml` likewise) — those models exist on the fork oracle only (separate executables:
`cerberus-cheri`; the symbolic driver is commented out of `backend/driver/dune`); cerberus-lean has the concrete model
alone, and any model-selecting flag is an unknown flag, refused (exit 2, zero-discrepancy Z-24).

**Exhaustive mode is the promise; `--first` is outside it.** In the default (exhaustive) mode Lean explores every
nondeterministic branch, as the oracle's `--mode=exhaustive` does, and §1 applies to the whole verdict set. `--first`
follows only the first branch (`CerbND.runND1Fuel`), where the oracle's `--mode=random` draws branches from a
time-seeded generator: the two can serve different members of the same exhaustive set on a program whose result
depends on evaluation order. `--first` is a harness convenience (the libc_exec and libxml2 lanes use it, and are sound
only for programs whose result does not depend on the trace), not part of the §1 promise.

## 3. Feature areas and their states

Three states only: **SUPPORTED** (differentially validated; any disagreement is a bug), **REFUSED** (loud,
feature-attributed; each refusal has a witness), **OUT OF SCOPE** (not an input the artifact accepts at all).

| Area | State | Evidence / refusal witness | Open questions |
|---|---|---|---|
| C frontend (parse → Cabs → Ail → Core) | SUPPORTED | shared OCaml parser; Lean desugar/typing/elaboration differentially tested (row 1 parser tests, all Tier A/B lanes) | frontend is `partial` (not kernel-evaluable) — a stated limit, not a discrepancy |
| Inline assembly (GNU `asm`/`__asm__`: basic, extended, `asm goto`, asm labels on declarators) | **REFUSED** (D9) in both engines, where upstream silently erases it: an asm statement fails desugaring in the shared `.lem` (`feature not yet supported: inline assembly (asm statement) is unsupported`; Lean `--batch` reports `desugaring failed at` the asm location), an asm label on a declarator fails in the shared parser (`unimplemented keyword 'asm (inline assembly label on a declarator is unsupported)'`), so no Cabs reaches the Lean engine | `scripts/check_asm_refusal.sh` (row 1): 4 statement + 3 label witnesses, 2 controls, 3 plants | file-scope `asm(...)` is not in the grammar: a syntax error (loud, not attributed); `__asm` (no trailing underscores) is an ordinary identifier |
| Core dynamics (driver, reduction, pure eval) | SUPPORTED | Tier A/B lanes, pristine 835/28/7/2, gcc oracle, csmith corpus | none known; this is where the report found nothing |
| Concrete memory model | SUPPORTED | CerbMem mirror with cites; immaculate lane; allocator soundness theorem | the SC receipt buffer is disabled by default (WP0) |
| Function pointers | SUPPORTED, including round trips through integers and `void*` (libc's `atexit` uses one); their numeric value — through an integer conversion, their bytes or `%p` — is named deviation N1 | `zd-funptr-*` rows, libc_exec `040`/`041` | none |
| Integer/float/layout implementation choices | SUPPORTED (LP64); printing a NaN with `%f` REFUSED (its text depends on the NaN's sign bit, which Lean cannot read); a NaN's sign and payload bits in memory are named deviation N2; float constants in the libc Lean loads are rounded to 12 digits in one place (named deviation N3) | CerberusImpl, CerbFloat, float/bytes lanes | other ABIs OUT OF SCOPE (D6) |
| libc (the oracle's libc.co, loaded) | functions written in C (`runtime/libc/src/*.c`): SUPPORTED — they run through the same Core semantics as user code — but thinly tested (§3.2); the 36 **builtins** of `runtime/libcore/std.core` (hand-implemented in each engine): one state each, §3.1 (D4) | libc_exec lane, libxml2 lanes | a UB raised inside a libc C body is reported at `<unknown location>` by Lean and at the libc source location by the oracle (VALIDATION §3, Z1-A1: an open bug with a named mover) |
| Filesystem (CerbFS) | **REFUSED** (D2) — every filesystem operation, including `read` on any fd; `write`/`vprintf` on fds 1/2 are served (the driver routes them to the stdout/stderr records, never reaching CerbFS) | `zd-fs-*`, `zd-f1-truncate-negative-length`, `zd-z2f01-lseek-whence` pinned refusals | none |
| Standard input / environment / argv | stdin REFUSED (every read reaches CerbFS, D2; the oracle models an empty stdin); `getenv` served by libc C code; argv SUPPORTED | `zd-fs-stdin-read` pinned refusal; argv lane (5 programs) | UTF-8 `--args` unmeasured |
| Concurrency (threads, atomics, Epar, C11 model) | REFUSED at the CLI flag; default-mode atomics and `{-{ ||| }-}` SUPPORTED as the oracle's sequential reading | `refuseFlag`; served-surface audit: 15 default-mode probes agree, `statically_satisfied` has no generated caller | none |
| Semantics switch `PNVI_ae_udi` (`--switches=PNVI_ae_udi`) | SUPPORTED (2026-10-07), matched against the oracle under the same switch | `scripts/test_pnvi.sh` (Tier A row 14): upstream's 44 PNVI litmus files exhaustive, `tests/minimal` under the switch, the pKVM census drivers; `check_cli_refusals.sh` (acceptance + one agreement witness) | the pKVM allocator drivers are compared in `--first` only (their exhaustive sets exceed the 4G cap on the oracle: outside §1, §2); the refused arms below |
| PNVI-ae-udi arms upstream itself leaves as crashes, debug prints or self-declared wrong code | **REFUSED** (class (c), [USER 2026-10-05]): `PNVI_ae_udi refusal (unsupported upstream arm): R-PNVI-nn: …`, exit 134. R-PNVI-01 `combine_prov` on a symbolic byte (impl_mem.ml:390-394; -01b `provs_of_bytes`, shadowed), -02 `find_overlaping`'s `assert false`, -03 its dropped third candidate, -04 `lookup_iota`'s `Not_found`, -05 `abst`'s "This is wrong" arm, -06 pure `array_shift_ptrval` on a symbolic pointer, -07 `case_ptrval` on a symbolic pointer, -08 `diff_ptrval`'s invariant failure, -10 the stdout-printing arm of `eff_array_shift_ptrval` | lane witnesses (`test_pnvi.sh`, each a registered `REFUSAL` row, never agreement): -01 by 4 upstream litmus files where the oracle crashes; -05 (`tests/pnvi_refusals/r05-…`, the oracle answers through the flagged arm), -06 (`r06-memcpy-symbolic-source.c`), -07 (`r07-call-through-symbolic-pointer.c`) where the oracle crashes; -01b, -02, -03, -04, -08, -10 by compile-time pins (`test/Unit/PnviArmsTest.lean`) — no C witness found. Reach: -01b, -02, -04 unreachable by invariant and -03 UNKNOWN (reviewed rows of `scripts/failure_reach_register.txt`); -08 and -10 are MONADIC sites (`pnviRefuseM` inside an `ND` body) outside that pure-site census, so their reach is UNREVIEWED (no register row; -10's arm is never taken on any litmus or pKVM trace, MEASURED, design §G R16 — a measurement, not a reach argument) | R-PNVI-09 (`eff_array_shift_ptrval`'s `PVfunction` arm) is a DEFAULT-path site and stays a mirrored fail-stop with the other default-path look-alikes (design §H.1), pending the queued default-path consistency review |
| Non-default memory models (symbolic, VIP, CHERI), every other switch (plain PNVI, PNVI_ae, strict reads, strict pointer arithmetic, …) and `--iso` | REFUSED at the CLI | `judgeSwitches` / `refuseSwitches` / `refuseFlag` (`check_cli_refusals.sh`), incl. R-PNVI-11 (an override in one list) and R-PNVI-12 (an unknown name), where the oracle ignores the name and runs on | none |
| Debug/pretty-print seams (CerbDebug, CerbPP) | OUT OF SCOPE for verdicts | no-op stubs; served-surface audit: no verdict path reads them | none |
| Core text (CoreParser) | SUPPORTED for the runtime's own Core files (`std.core`, the implementation file, the libc dump), which every run parses; no mode executes user-written Core text (`--parse-core` and `--pp-core` are diagnostics) | core-parser tests (292 checks); verify lane | none |

### 3.1 The builtin boundary (D4)

`runtime/libcore/std.core` declares 36 `builtin` procedures. Unlike libc's C functions, each is implemented by hand in
both engines, so each has its own state. The live stepper's fallback arm fails any builtin not handled here, in both
engines, so a builtin added upstream fails closed until it is reviewed and listed.

| Builtin(s) | State | Where / evidence |
|---|---|---|
| `printf`, `vprintf`, `vsnprintf` | SUPPORTED (`vprintf` to fds 1/2; other fds reach CerbFS and refuse) | generated `Formatted`; immaculate programs that print (measured: 11 files call printf), libc_exec, libxml2 |
| `exit` | SUPPORTED | generated `Core_reduction`; every lane's exit path |
| `errno` | SUPPORTED | generated `Core_reduction`; libc_exec |
| `generic_ffs`, `ctz`, `bswap16`, `bswap32`, `bswap64` | SUPPORTED | `CerbUtils` line mirrors of `ocaml_gcc_builtins.ml`; immaculate `g4-*` rows |
| `write` | SUPPORTED on fds 1/2; fd 0 fails in both engines; other fds REFUSED (CerbFS) | `driver.lem` routing |
| `read` | REFUSED (CerbFS, every fd) | D2 |
| `any_bounded_int` | NOT SERVED by either engine: both fail it (`core_reduction.lem:1012-1013`) | `zd-any-bounded-int-crash` pinned MATCH / both crash |
| `open`, `close`, `pread`, `pwrite`, `lseek`, `truncate`, `link`, `readlink`, `symlink`, `unlink`, `rename`, `rmdir`, `mkdir`, `stat`, `lstat`, `umask`, `chmod`, `chdir`, `chown`, `opendir`, `readdir`, `rewinddir`, `closedir` | REFUSED (D2) | `CerbFS` refusals; `zd-fs-*` rows |

### 3.2 How deeply each part is tested

SUPPORTED means "differentially tested, and any disagreement is a bug". It does not mean every part is tested equally.
The measurement behind this section is `docs/2026-09-28_test-depth-map.md` (static counts of the gated lane programs
that exercise each part; there is no coverage instrumentation, so the counts are proxies), re-counted after the
edge-case tests of `docs/2026-09-28_thin-surface-tests-record.md` and the four rows added with the fixes that followed
them. The gating lanes hold 972 programs that agree with the oracle (measured by the map's census script on the
range head; the two `%f`-of-a-NaN rows are refusal pins, not agreement).

**Deeply tested:** the C frontend and Core dynamics (generated from the same Lem source as the oracle), load/store and
allocation, integer and floating-point arithmetic (also checked against gcc as a second oracle), the exhaustive runner
and the batch output format. Every program exercises these.

**Less deeply tested — treat results here with more suspicion.** These are served, and a disagreement is still a bug,
but fewer gated programs exercise them, and most are hand-written Lean rather than shared generated code. Counts are
gated agreement programs, before → after the 2026-09-28 edge-case tests:

| Part | Programs | Depth now | Why it matters |
|---|---|---|---|
| libc breadth | 11 → 62 of the 188 libc functions called directly; libc mode 32 single-trace → 61 single-trace + 2 exhaustive | THIN | most libc functions are still called by no test, and libc mode is mostly compared single-trace |
| `printf("%f")` | 0 → 13 | MODERATE | `CerbFloat.formatFixed` is an independent reimplementation of glibc's `%f` |
| printf width, precision, flags; `%c`/`%x`/`%X`/`%o` | 0 → 22; 0/1/0/0 → 6/8/2/3 | MODERATE | formatting is shared code, `%c` goes through hand-written escaping |
| `realloc`, `memcpy`, `memcmp`, `memset` | 4/5/2/1 → 16/15/7/5 | MODERATE (`memcmp`, `memset` thin) | hand-written `CerbMem` routines |
| `snprintf`/`vsnprintf`, `errno`, `exit`, `atexit` | 2/1/1/0 → 6/5/4/2 | THIN | return values and status codes |
| argv | 5 | THIN | non-ASCII arguments fail in both engines (with different messages) |
| programs of several translation units | 8 → 14 | MODERATE | linking and cross-TU identity |
| default-mode atomics and `{-{ ||| }-}` | 1 | THIN | shared code, lower risk |
| `--first` mode | not checked to be one of the exhaustive results | outside §1 | outside the §1 promise (§2) |
| non-batch CLI output | never compared (only `--batch` output is the compared interface) | outside §1 | human-readable format, exits 0 for every outcome, as the oracle's does |

The **refused** parts (filesystem, stdin, concurrency and switch flags, the PNVI-ae-udi refusals, `%f` of a NaN, inline assembly) are pinned by
witnesses and are not "thinly tested": they do not answer.

## 4. How the contract is enforced

1. **Every REFUSED area has at least one witness in a lane that pins the refusal**, so a return to a silent answer turns
   a gate red: the filesystem and stdin (`zd-fs-*`, `zd-f1-*`, `zd-z2f01-*` immaculate rows), `any_bounded_int` (`zd-any-bounded-int-crash`), `%f` of a NaN (`fmt-007*.unsupported.c`), the CLI flags (`scripts/check_cli_refusals.sh`,
   row 1), the PNVI-ae-udi refusals reachable from C (`scripts/test_pnvi.sh`'s `REFUSAL` rows, Tier A row 14, which
   assert the refusal id and the oracle side) and inline assembly (`scripts/check_asm_refusal.sh`, row 1, which asserts the message too).
   Limit: the immaculate and coverage witnesses pin the crash CLASS (`L=CRASH`, `UNSUPPORTED`), not the refusal
   message, under those lanes' coarse crash policy (VALIDATION §1(a)); the message is fixed in the refusing code, and
   `check_cli_refusals.sh` asserts it for the CLI flags.
2. **A served-surface audit (the lesson of pathleak).** Every hand-written seam that can answer where it has no model —
   default arms, stub bodies, `Inhabited` defaults, lookups keyed on unnormalised data — is enumerated and classified:
   mirrors the oracle (with a cite), refuses (with a witness), or is unreachable (with the reason). The failure-reach
   register already does this for FAILURE sites; the audit extends the question to SUCCESS paths that answer without a
   model. Proposed as a fresh-reviewer pass with a finding ledger, before the contract is adopted.
3. **Adversarial inputs per area**, written from the contract rather than from the corpora: path spellings, fd reuse,
   environment and argv shapes, concurrency constructs in default mode. The corpora are upstream's tests and never
   exercised these.
4. `CONTRACT.md` becomes the front-page statement; `SUPPORTED.md` becomes its dated evidence table; VALIDATION keeps the
   mechanics. The announcement text points at `CONTRACT.md`.

## 5. Decisions

- **D1 — adopted** ([USER 2026-09-28] "D1 agree"): the outcome promise in §1 is the normative statement.
- **D2 — refuse the filesystem for now** ([USER 2026-09-28] "D2 refuse FS for now, this seems safer"). Implemented:
  every CerbFS operation refuses with a feature-attributed message; `write` to fds 1/2 stays served (driver-routed,
  never CerbFS). Three immaculate rows moved from MATCH to pinned refusals; the full ladder passed
  (`docs/2026-09-28_cerbfs-refuse-all-record.md`).
- **D3 — adopted** ([USER 2026-09-28] "D3 agree"): the served-surface audit (§4.2) ran
  (`docs/2026-09-28_served-surface-audit.md`). Its P1 finding (function-pointer numbers) is named deviation N1 ([USER 2026-09-28] "agree with (1)"),
  covering the integer conversion too after refusing it broke `atexit` ([USER 2026-09-28] "agree on atexit as you
  propose").
- **D4 — adopted, option 1** ([USER 2026-09-28] "Yeah, (1) is fine"): libc is supported by mechanism. Functions written
  in C inherit the core semantics' state; the 36 builtins are a named list with one state each (§3.1). `any_bounded_int`
  is listed as not served by either engine (the audit found it fails in both); its dead Lean seam, which returned `lo`,
  now fails loudly (`docs/2026-09-28_contract-enforcement-builtins-record.md`).
- **D5 — adopted, amended** ([USER 2026-09-28] "D5 - amended, yes, link from top level README.md"): this document is the
  public statement, linked from the top-level README.
- **D6 — LP64 only** ([USER 2026-09-28] "Agreed re the ABI"): LP64 (the x86-64 Linux data model) is the one supported
  ABI, the only one the lanes test; every other ABI is out of scope.
- **D7 — a NaN's bits are named deviation N2** ([USER 2026-09-29] "agree on all 3", on the recommendation to register
  the pre-merge audit's F2 rather than refuse storing NaNs): Lean's float store canonicalizes NaNs, so their bytes
  differ from the oracle's (VALIDATION §2b).
- **D8 — the libc dump's float rounding is named deviation N3** ([USER 2026-09-30] "Right, I think (3) is the right answer
  for now, and (1) or (2) might be work for later."), with a float-literal inventory check. Standing rule [USER 2026-09-30]:
  "we should not fix deviations with special 'magic mode' paths that work exclusively in one situation."
- **D9 — inline assembly is refused** ([USER 2026-10-05] "Re inline asm, this should be a loud refusal"). Upstream erases
  it (an asm statement desugars to a skip; an asm label is dropped by the parser), so a program whose meaning lives in its
  asm ran as if the asm were absent (real-C census §4.5: both engines `Specified(1)` where gcc gives 5). The refusal is on
  the general path of the shared model and parser, so the oracle and Lean refuse identically and no asm semantics is
  invented; a deliberate fork-vs-pristine difference, manifested in the fork-drift gate. No gated lane row moved
  (`docs/2026-10-05_asm-refusal-record.md`).
- **Agent-called dispositions under these rulings** [AGENT 2026-09-28]: `%f` of a NaN is refused rather than
  registered (it can be refused cheaply and precisely; Lean cannot read a NaN's sign), and the other disagreements that
  record found (its D3–D6, a separate numbering from this section's) are dispositioned in `docs/2026-09-28_thin-surface-tests-record.md` (addendum).