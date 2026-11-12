# VALIDATION — why you should trust this semantics

**Documentation check, 2026-09-25:** implementation `bb487dda7c56981e76d67f53ae16e874cfe5ed61`;
Lem `67ec5de70e02e280bb348a4ba826696b76116732` (the Lem pin has since moved to `2d3a492758cb23dc4e417f2961983d25b36ce130` by functional re-pins (via `77ad4fa` and `4e70bb5`, both merged; the current pin `2d3a492` itself is PROVISIONAL — the head of the unmerged lem-lean branch `arc/pnvi-switches`, not yet on `mdd/lean-backend`), generated OCaml byte-identical at each: [re-pin record](docs/2026-10-04_lem-repin-4e70bb5-record.md), [PNVI S1 record](docs/2026-10-05_pnvi-s1-switch-parameter-record.md)). Current follow-up gates and remaining
publication checks are in [the follow-up record](docs/2026-09-25_public-readiness-followup.md);
earlier baseline inventories are in [the remediation record](docs/2026-09-24_public-readiness-remediation.md).
Older dated measurements below remain historical evidence. Original evidence
archives removed from the tracked tree remain recoverable from history;
[the dated inventory](docs/2026-09-24_evidence-archive-untracking.md) records
identities and recovery instructions.

An executable semantics is trusted for what it has been *checked*
against, and this document is the honest inventory: the rule the port is
held to, the exceptions and how each is tested, the register of
deliberate deviations, every known difference and its class, then what
is compared against what, how often, and what the gates guarantee. There
is no delivered proof that the Lean port equals the compiled OCaml
implementation. That compiler/runtime correspondence remains an external
reference boundary, so the validation story is (a) **structural**: both
implementations are generated from one Lem model, and the hand-written residue mirrors its
OCaml counterpart line-by-line; and (b) **empirical**: an industrialized
differential-testing surface with pinned, fail-closed baselines. A green
build is never the signal; the differential baselines are.

The current [supported profile](SUPPORTED.md)
separates shared-source, logical-definition, native-execution and consumer
claims. Validation-foundations adds an independently compiled pristine
oracle, a shared byte observation contract, an executable LADDER runner,
and a cold provider client. The
[audit repair record](docs/2026-09-06_validation-foundations-audit-repairs.md)
identifies the corrected 32/32 Tier A+B pass, C1/C4 reporting, cold build/proof
and failure measurements. The original delivery and first audit remain dated
history. The [fresh document review](docs/2026-09-06_validation-foundations-document-review.md)
corrects a material fuel-correspondence overclaim and three minor issues;
those were the remaining exits in that dated review. The operator reported
customer acceptance on 2026-09-24 (SUPPORTED.md); the present cleanup does
not infer fresh reporting/audit certification from that acceptance.
Missing historical logs are
explicitly inventoried; they are not evidence of a current pass. See
[the observation contract](docs/2026-09-05_observation-contract.md)
for sequence/set projections and the printer's observational limits.

## 0. The aims and the rule

The four aims, in priority order — [USER 2026-09-03], verbatim:

> "(1) match cerberus-ocaml exactly in cases where we do not have STRONG
> evidence it is incorrect wrt ISO-C, (2) if cerberus-ocaml appears
> clearly incorrect, do the correct thing and log it cleanly for an
> upstream fix, (3) design so that consumers, eg. refined-cerberus get
> the most useful version of the semantics, (4) within the remaining
> design latitude, try to fail-closed i.e default to safe behavior wrt
> correctness for executable semantics and downstream customers"

**The rule** — [USER 2026-09-03], verbatim (charter
`docs/2026-09-03_zero-discrepancy-design.md` §1.1):

> "All *execution* discrepancies are definitionally bugs (other
> machinery intended to support proof is allowed but should have no
> semantic / execution effect whatsoever and all legacy permission
> revoked"

For cerberus-lean: **Lean ≠ oracle (matched mode) on a program both run
= bug.** The oracle's own deviations from ISO C are MIRRORED faithfully
and recorded in the upstream tray (`docs/upstream-tray/INDEX.md`; drafts and filed reports are distinguished there) — the rule is Lean ≠ oracle,
not Lean ≠ ISO. Every previously "declared", "documented-deliberate",
"unobservable" or "temporal-boundary" divergence was re-classified on
2026-09-03 into the classes of §1; the label is not a class, and this
document no longer uses those words for anything but history.

**The referent is the logical semantics** — [USER 2026-09-03], verbatim
(`docs/2026-09-03_logical-semantics-referent-ruling.md`): "ocaml limits
that are hardcoded thanks to ocaml-level execution issues are also
forbidden, the real thing is the logical semantics". What the port
mirrors is the lem model, the Core stdlib and ISO C where the model is
silent — not the OCaml runtime's execution accidents (`Z.Overflow` from
a host-int conversion, `Division_by_zero` from a missing guard,
`Stack_overflow`, 63-bit `int` wrap). A one-sided oracle failure is
therefore of one of two KINDS: (1) a `failwith`/`assert` the model writes
deliberately — a design choice, mirrored as a fail-stop carrying the
OCaml text; (2) an OCaml-execution artifact — NOT mirrored: Lean
implements the logical meaning at that point, the case is logged (tray)
and pinned (immaculate Lean-right/oracle-wrong pair), and it is admitted
to the register (§2) BY CLASS.

**The 2026-10-03 rule and its synthesis with the referent ruling** —
[USER 2026-10-03], verbatim: "Generally, our rule is that we don't innovate
wrt Cerberus-upstream, unless something is very very very obviously a bug.
We're poorly placed to resolve semantic discrepancies, so we don't. ... we
should fall back to loudly rejecting (either as unsupported, or matching
upstream)." The two rulings are reconciled by the synthesis [USER
2026-10-03] "(1) agree with this", on: where upstream's OWN semantics
defines the answer and only OCaml's machinery crashes on the way (a host
artifact), Lean computes that answer (the R3 treatment; R7 for the
alignment reads); where no answer is defined, or Lean's "answer" was
garbage, Lean makes a loud stop mirroring the crash (`Division_by_zero` in
`op_ival`, Z2-M-01; the negative `IntExp` exponent). Applied in
`docs/2026-10-03_total-arith-and-bookkeeping-record.md` §7 (the former
open item O-3 there is resolved).

**UB location is behaviour** — [USER 2026-09-03] "(1) agree": the `loc`
field of an `Undefined` line (and the `stderr` bytes) are part of the
verdict the semantics reports; every lane compares whole `Undefined
{…}` lines since Z1 (`docs/2026-09-03_zero-discrepancy-Z1-record.md` §4).
**Successful output bytes are behaviour too**: since the P0 instrument
repair (2026-09-05, whole-project audit F3;
`docs/2026-09-05_p0-instruments-record.md` §F3) `test_exec.sh` — the
main lane and everything built on it — compares the WHOLE `Defined {…}`
line (value, the program's captured stdout and stderr, blocked) as one
token; before it only the `value: "…"` field was compared, so two
`Defined` lines with the same value and different stdout/stderr read
MATCH. Validation foundations migrated the six required lanes and inventoried
older callers to the shared byte codec and actual-status capture. The
[observation contract](docs/2026-09-05_observation-contract.md) defines the
fields and each lane's sequence/set projection. GCC native exit comparison
and the independent litmus reference remain explicitly weaker projections;
the initial candidate had 67 actual-entry plants, and the repaired candidate
passed all 90 in its identified full run (see the audit repair record).

Terminology. **oracle** = the OCaml Cerberus built from this
repository's `.lem` + OCaml sources, run in the MATCHED MODE (same
`--nolibc`/libc linkage, `--mode=exhaustive` or `--first` ≙ single trace,
default switches, no `--concurrency`, the default address-space top — neither
engine passes `--address-space-top`, §7). **upstream** / **pristine** =
un-forked Cerberus @ `b9aeedcb4` — as source, `deps/cerberus-upstream`; as an
ENGINE, the independently compiled build (pristine source + upstream Lem
`3802cb0`, git archives, `DUNE_CACHE=disabled`, hash-pinned manifest) that
`scripts/ensure_independent_oracle.py` keeps standing at
`.validation-foundations/independent-oracle-v2`. **execution discrepancy** = on a
program both engines run, a difference in the outcome class
(`Defined`/`Undefined`/`Error`/tool failure), the value, the UB code, the
UB location, stdout/stderr bytes, or the trace set. **mirror** = make the
Lean text compute what the OCaml text computes, with a `file:line` cite.

**The reference doctrine** (WP-O, 2026-09-16 — [USER 2026-09-16]: *"right
now we have the ocaml-cerberus as an oracle, but we're also changing it.
There's some danger there!"*; record
`docs/2026-09-16_pristine-oracle-instrument-record.md`). Pristine upstream
`b9aeedcb4` is THE reference. The fork's OCaml is the shared model's
**mirror twin**: it is built from the same `.lem` the Lean port is generated
from, so a shared-model edit moves the fork oracle and Lean TOGETHER and every
fork-vs-Lean lane is blind to it by construction. The fork's deviations from
pristine are therefore a separately gated inventory: the register
`scripts/upstream_oracle_differences.json` (schema 2 — every row classed
`diagnostic-text` | `resource` | `missing-feature` | `shared-model-fix`,
cited to an upstream-tray draft, an ISO-fix register id or a dated record,
with a rationale and both engines' full signatures) is the ONLY permitted
list of fork≠pristine behaviours OBSERVED on the walked corpora; the fork's
source-level deltas from upstream are the reviewed
`scripts/fork_drift_manifest.txt` (§6, `check_fork_drift.sh`), of which the
register is the behavioural projection — a delta with no register row is
either unobservable on the corpora or a missing case, and the S1 charter's
three-way report is how a slice shows which. LADDER Tier B row 10
(`scripts/test_upstream_oracle.py`) is the register's gate: pristine vs fork
over every corpus the fork-vs-Lean lanes GATE on (the Tier A/B baselines)
plus the `tests/ci` and csmith reporting corpora — `test_ci_sweep.sh`'s
fourteen other suites (Tier C row C4, a scoreboard with no baseline) are not
walked and are named as such in the lane's report — every unexplained
difference RED, a pristine-side non-termination admitted only through a
cited `resource`/`shared-model-fix` row (never the fork side), stale rows
RED, and a REGISTERED case always judged by its row: a registered case whose
fork side times out, or a both-sides timeout on a registered case, is RED —
the pin moved.
Since 2026-10-03 the register has 8 `shared-model-fix` rows. They are `multi_tu_tray/node` (draft 37;
draft 38's consult was reverted, §3), the four allocator rows, and the three `_Alignas`
completeness rows of draft 47 (§3). The inventory at
`e9f9d049f`, counted 2026-09-24, had 7 `shared-model-fix` rows (the three cross-TU
struct-value cases of upstream-tray drafts 37/38/39, where the fork answered
`Specified(7)` and pristine loops or rejects; and the two allocator
exhausted-regime witnesses of draft 44, `minimal/112-…`/`113-…`, where
pristine returns an overlapping, misaligned allocation and the fork kills out
of memory — §3; plus the corresponding two `immaculate/nolibc/tray44-*`
wrappers, separately registered). This is seven case rows, not seven
distinct defects; `diagnostic-text` is a
permitted class with zero rows — [USER 2026-09-17] ("(2) agree"): the lane's
diagnostic projection normalises source positions inside OCaml backtrace
frames — and, since the allocator-soundness slice's C1b (2026-09-17; the
[USER 2026-09-17] ruling quoted in §3), the position in the exception HEADER
line `File "…", line N, characters A-B: <text>`, path and text compared raw —
so a both-crash pair whose frames or header differ only there is a
`matching_failure`, not a row; and [USER 2026-09-17] ("(1) agree"): a
BOTH-sides timeout at the lane's own bound is the counted, non-failing
`matching_incomplete` class, never a row (one-sided timeouts and signal kills
stay fatal). A
SHARED-MODEL SLICE runs the three-way `pristine | fork | lean` report
(`test_upstream_oracle.py --with-lean`, LADDER Tier C row C5) over the full
pristine corpus and may add register rows only with a citation; a
fork≠pristine difference no existing citation explains is a finding for the
operator, never a row the slice writes itself.

## 1. The exception classes and their operational tests

Exactly five classes are not bugs. Each has a test a lane or a reader can
apply; anything that fails every test is a BUG-FIX row (mirror + tray).

**(a) Failure-path MESSAGE TEXT** may differ; the failure-vs-success
classification must be identical. *Test:* both engines fail on the input
(both `Error`, or both tool crashes — exit 125 uncaught exception on the
oracle, exit 134 `PANIC` under `LEAN_ABORT_ON_PANIC=1` on Lean), and only
the text differs. A crash on one side and a verdict on the other is NOT
(a). *Standing members:* the `Illformed_program` text (`Main.lean`
`driverErrorBatchMsg` vs `pp_errors.ml:501`; the libxml2-uri lane pins
it modulo the embedded symbol id, tray 17); the both-crash immaculate
pairs (`MATCH | L=CRASH`: `g2-memcmp-uninit`, `g4-bswap64-overflow`,
`g5-decode-multichar`, `offsetof-union-member`, the `zd-z2*` pairs);
front-end rejections reported on stderr by the oracle and as an `Error
{msg: …}` line on stdout by Lean (exit class identical — measured on 112
reject rows, Z1 record §2). Quoted PANIC texts carry build-relative line
numbers (`CerbMem:2075:6` today) — never compare them byte-wise. Since C-TF1 (2026-09-08, `docs/2026-09-08_monadic-failstop-record.md`) the
seven hand-written memory-model fail-stops are TYPED kills
(`Error0 CerbFail.modelFailStopLoc msg`) printed as the batch record
`ModelFailure {msg: "…"}` with exit 1, where the oracle dies with an
uncaught exception (exit 125): a both-fail pair, class (a) — the immaculate
pin label `L=CRASH` covers it under the lane's reviewed coarse crash
policy; the codec never lets a `ModelFailure` count as semantic agreement.

**(b) RESOURCE LIMITS** — Lean must not fail where the oracle succeeds;
the converse is acceptable. *Test:* the oracle completes the input
(within the lane bound) and Lean does not → a **(b)-VIOLATION**, i.e. a
BUG carrying a named mover, not a tolerated limit; loudness (`HANG`,
`KILL`, `TIMEOUT` classes) is necessary, not sufficient. A wall-clock
row is tolerated ONLY per row with measured completion at a larger bound
(charter Q5). *Standing members:* §3 lists them with their movers.
**(b)/fuel** — fuel exhaustion is accepted under (b), [USER 2026-09-03]
verbatim: "fuel is a reasonable exception because we could always just
run the semantics with more fuel"; the bound is a PARAMETER (`--fuel N`,
§7), and a FUEL row is never counted as agreement.

**(c) MISSING FEATURES** — [USER 2026-09-03], verbatim: "*missing
features* are allowed deviations if they are cleanly identified. CerbFS
is kind of an obscure feature as is concurrency, it's unclear if we'll
support it". *Test:* the Lean side REFUSES — non-zero exit AND a message
that names the missing feature and the boundary (not a symptom: a
file-not-found error for a flag is loud but not attributed) — where the
oracle answers. A different answer, or a silent absorption (an errno, a
default, a zero) is never (c). *Standing members:* §3.

**(d) ISO-CORRECTNESS FIXES — the register (§2).** [USER 2026-09-03],
verbatim: "I think that a short listed set of fixes is in keeping for
the purpose of cerberus-lean but the bar for such a fix must be
extremely high." *Test:* the deviation is an enumerated register entry
meeting criteria (i)–(vii) (or admitted BY CLASS as a kind-2 artifact,
§0), individually [USER]-ruled, pinned as a Lean-right/oracle-wrong
immaculate pair, with the `-- ISO-fix register R<n>` code marker. Nothing
else may deviate toward ISO.

**(e) NAMED DEVIATIONS — the register (§2b).** [USER 2026-09-28],
verbatim: "Named deviations are okay in cases we can't easily resolve the
mismatch." *Test:* the difference is an enumerated register entry that
states the mechanism, why neither mirroring nor a loud refusal is
practical, the channels it covers, and a mover (or "none: upstream
artefact"); it is individually [USER]-ruled, pinned by immaculate DIFF
witnesses carrying the Lean value, and marked at the Lean site with
`-- named-deviation register N<n>`. A difference that CAN be refused
cheaply is refused under (c) instead; (e) is never a way to keep serving
something that could be refused.

Two further dispositions are not exceptions but are named here so no
reader mistakes them for one: **kind-1 fail-stops** are mirrored
(`panic!` with the OCaml text; the typed-failure pass — scheduled,
`docs/2026-09-03_typed-failure-outcomes-ruling.md` — will turn them into
a distinguished outcome so in-process consumers see the oracle's failure
class rather than a default value); **instrument artefacts** (a
pretty-printer filter, a stale scoreboard snapshot, a lane's extractor)
have no execution content and are fixed as instruments.

## 2. The ISO-fix register (class (d))

Submission status (2026-09-26): the register's upstream reports 10, 11, 13 and 40 were
communicated privately to the Cerberus maintainers by the operator — [USER 2026-09-26]
"these have been filed privately in that I have notified the cerberus maintainers" — and
are recorded as **Sent** (transmitted, no public issue URL) in the
[tray status table](docs/upstream-tray/INDEX.md#submission-status); report 01 is **Filed**
(#1009); report 19 (the DEFERRED row R4) stays Draft. That private notification is how the
"filed upstream" criterion is met for these rows; the tests enforce registered behavior and
cannot enforce submission or upstream acceptance, which remain operator actions.


The ONE licence for a deliberate Lean deviation TOWARD ISO C (criteria
(i)–(vii) and the tightened (ii′) RATIFIED [USER 2026-09-03], charter
§1.4/§7 Q2/Q3). The policy requires an unambiguous oracle bug against a cited ISO
clause, a second independent oracle agreeing with Lean, upstream filing,
pinned in the immaculate lane as a Lean-right/oracle-wrong pair that
flips to MATCH — retiring the entry — when upstream fixes it,
individually [USER]-ruled, soft cap ≤ 10, and a grep-able code marker
`-- ISO-fix register R<n>` at the Lean site. Kind-2 OCaml-execution
artifacts (§0) are admitted BY CLASS under the referent ruling; the
register still lists them for visibility, the pin and the tray
cross-reference. Anything not listed here is a BUG-FIX (mirror + tray),
whatever a comment used to call it.

| entry | oracle behaviour (site) | ISO clause | 2nd oracle | tray | immaculate pin(s) | Lean code site | ruling |
|---|---|---|---|---|---|---|---|
| **R1** | `'\?'` / `"\?"` make `decode_character_constant` FAILWITH (decode.ml has no `\?` arm; `translation.ml:3032` for the string-literal form): uncaught exception, exit 125 | C11 §6.4.4.4#1 (`\?` is a simple escape sequence), #4 (value = `'?'` = 63) | gcc exit 63; `"a\?b"` → bytes `97 63 98 0`; `ptr_string_literals.c` output = gcc byte-for-byte | 10 (+ string-literal addendum, noodle E2) | `g5-decode-question` ORACLE_CRASH / L=Specified(63); `zd-e2-ptr-string-literals` ORACLE_CRASH / L=Specified(0) + the gcc byte string | `CerbDecode.lean` `| "\\?" => 63` (marker `-- ISO-fix register R1`) | **ADMITTED** [USER 2026-09-03] |
| **R2** | `%c`-stored char round-trips through `Decode.escaped_char` (= `Char.escaped`, decimal `\ddd`, decode.ml:221-222) then the OCTAL reader (decode.ml:184-197) inside `formatted.lem:769-771` `store_chars_in_array`: 127 is stored as 87. The same round trip corrupts every stored byte ≥ 128 and every control byte (200 → 128, 255 → 173), and CRASHES the oracle (uncaught `decode_character_constant` failure, rc 125) on any byte whose decimal escape contains a 9 (19, 29, …, 190–199, e.g. 0xC3 = 195, the usual UTF-8 lead byte) — scope widened 2026-09-29 from the bug hunt's K-1 (`docs/2026-09-29_discrepancy-bug-hunt.md`); same mechanism, same fix | C11 §7.21.6.1#8 (`%c`: the `int` argument converted to `unsigned char` is written) | gcc 127; widened rows gcc 200 / 199 (measured 2026-09-30, `gcc -O0`) | 11 | `g5-escape-roundtrip` DIFF / L=Specified(127); `zd-r2-highbyte` DIFF / L=Specified(200) (oracle 128); `zd-r2-crash-digit9` ORACLE_CRASH / L=Specified(199) | `CerbDecode.escaped_char` (hex `\xNN`, exact round-trip; marker `-- ISO-fix register R2`) | **ADMITTED** [USER 2026-09-03]; scope widened [USER 2026-09-29] ("Agree on everything, yes on the fixes") |
| **R3** | `memcmp` with a huge size: uncaught `Z.Overflow` at `impl_mem.ml:2660` `Z.to_int` — a host-int conversion raised BEFORE the semantic path (a KIND-2 OCaml-execution artifact, §1(d)) | (ii′) shape: no ISO answer for a UB program; the semantics' own checked per-byte load yields `UB_CERB002a` | the class ruling stands in for (ii′)(3): the referent is the logical semantics, and a host-language exception is not part of it ([USER 2026-09-03], `docs/2026-09-03_logical-semantics-referent-ruling.md`); tray 13's Z-native remedy on a scratch oracle build remains the check to run when the draft is filed, not a condition of admission | 13 | `s4b-memcmp-hugesize` ORACLE_CRASH / L=UB_CERB002a (stays as recorded) | `CerbMem.lean` memcmp (line-mirror minus the conversion; marker `-- ISO-fix register R3` at the `getBytes` size use, added 2026-10-03) | **ADMITTED BY CLASS (kind 2)** — the referent ruling [USER 2026-09-03] as read by the orchestrator (`docs/2026-09-03_logical-semantics-referent-ruling.md`, consequences list), CONFIRMED by the operator [USER 2026-09-05: "(2) agree"]; supersedes the Z1 entry's "ADMITTED CONDITIONAL on Z4's (ii′)(3)" |
| **R5** | `float_of_string` (`Impl_mem.str_fval`, `memory/concrete/impl_mem.ml:2523-2524`; the Lem-level `Cerb_floating.of_string`, `util/cerb_floating.ml:8-16`, reaches the same routine) → `caml_float_of_hex` (OCaml 5.4.0 `runtime/floats.c:355` `f = (double)(int64_t) m;`, `:369` `f = ldexp(f, exp);`) rounds TWICE for a subnormal result (the ≤64-bit mantissa → 53 bits → the subnormal's shorter precision): `0x8000000000000BFp-1082` reads as `0x1p-1023`, one quantum below the correctly rounded `0x1.0000000000002p-1023`. Scope: hexadecimal literals with more than 53 significant bits whose value is subnormal and whose 53-bit pre-rounding lands on a tie. The defect is the OCaml RUNTIME's, no Cerberus source involved (also R3's host-artifact class under the referent ruling [USER 2026-09-03]) | C11 §6.4.4.2#3, last sentence: "For hexadecimal floating constants when FLT_RADIX is a power of 2, the result is correctly rounded." (`tools/n1570.json`; the decimal/non-power-of-2 latitude in the same paragraph does not apply) | gcc exit 1 on the pin program (`return 0x8000000000000BFp-1082 == 0x1.0000000000002p-1023;`); Python 3 `float.fromhex` → equal, bits `0x0008000000000001` | `ocaml/01-float-of-hex-double-rounding-subnormal.md` (OCaml-target draft, TRUE BUG) + 40 (Cerberus-facing, INHERITED / minor) | `r5-hex-subnormal-double-rounding` DIFF / `L=VAL:{value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}` (oracle `Specified(0)`); flips to MATCH and retires the entry when the OCaml runtime is fixed | `CerbFloat.lean` `roundToBinary64Bits` — the single exact rounding (marker `-- ISO-fix register R5`); the correctly rounded bits are also pinned in `test/Unit/FloatLiteralTest.lean` | **ADMITTED** [USER 2026-09-15] ("Great, agree on your recommendation. Go ahead with the worker" — on the orchestrator's recommendation to admit the row as R5 and keep the correctly rounded conversion; charter `docs/2026-09-11_codex-charter-semantics-audit-repairs.md` §6) |
| **R6** | lem's `Float.floatMul` has the OCaml target `Cerb_floating.mul = (+.)` — ADDITION (`util/cerb_floating.ml:5`, a copy-paste slip next to the correct `add`/`sub`/`div`). UNREACHABLE: in the kernel constant-dependency closure of the exec entries and of the front-end entries (`tests/failure-probes/FailureReach.lean`, the failure-reach instrument; measured 2026-10-03: `FAILURE_REACH CerbFloat.floatMul false false`, while `CerbMem.opFval` is `true`) `CerbFloat.floatMul` is in neither; its only users are the generated `Defacto_memory.impl_op_fval` (the defacto model, not the executing concrete model, whose `op_fval` multiplies with `*.`, `impl_mem.ml:2529-2537`, mirrored by `CerbMem.opFval`) and float.lem's `NumMult` instance, which no lem code in either cone applies | C11 §6.5.5#4 (the result of `*` is the product) | gcc multiplies (any program) | 01 (Filed: Cerberus #1009, operator 2026-08-19) | none possible — no C program reaches the site, so criterion (iv)'s Lean-right/oracle-wrong pin cannot exist; the reachability claim above is what stands in for it | `CerbFloat.floatMul` (real multiplication; marker `-- ISO-fix register R6`) | **ADMITTED** [USER 2026-10-03] "(2) yes this is the canonical 'obviously a mistake, no semantic ambiguity, just fix'" (proposed by the worker 2026-10-03; record `docs/2026-10-03_total-arith-and-bookkeeping-record.md` §4, §8) |
| **R7** | `_Alignas(N)` with `N` ≥ 2^62 (a power of two, front-end accepted): the member-alignment reads `Z.to_int al_n` in `Concrete.alignof` (`impl_mem.ml:248` struct, `:267` union) and in `Ocaml_implementation.alignof` (`ocaml_implementation.ml:483`/`:501`, the desugarer's `alignof_ty`) raise `Z.Overflow` (uncaught, exit 125, pristine AND fork) — a host-int conversion, the same KIND-2 class as R3: upstream's own Lem interface is unbounded (`implementation.lem:27` `alignof_ty … -> maybe nat`; `mem.lem:191` `alignof_ival` returns an `integer_value`), and `impl_mem.ml` itself marks this conversion class a known limitation (`:1063` "TODO: the Z.to_int on the sizeof() will raise Overflow on huge structs", likewise `:1143`, `:1216`, `:1558`, `:2810`) | (ii′) shape, as R3: upstream's own semantics defines the answer (the unbounded layout); C11 §6.7.5#3/#4 for the alignment rules it applies | the in-range analogues computed by the oracle itself: `offsetof` past a 2^62-aligned member = 2^62 and `sizeof` of the union = 2^62 on BOTH engines (offsetsof/union sizeof keep the `Z`); the 2^61 control `zd-ta-alignas-2p61-control` MATCH | none drafted yet | `zd-ta-alignas-huge-sizeof` ORACLE_CRASH / L=`Specified(0)` (sizeof = 2^63, `(int)` → 0); `zd-ta-alignas-huge-union-alignof` ORACLE_CRASH / L=`Specified(0)` (alignof = 2^62, `(int)` → 0); `zd-ta-alignas-huge-desugar` ORACLE_CRASH / L=`ERR:{msg: "MerrOther "Concrete.allocator: failed (out of memory)""}` — arithmetic in the record §7 | `CerbMem.alignofCtype_lemFuel` struct/union folds and `CerberusImpl.alignof_ty` (unbounded `Nat`; marker `-- ISO-fix register R7`) | **ADMITTED** — [USER 2026-10-03] on the pre-merge audit's F1 (`docs/2026-10-03_total-arith-pre-merge-audit.md`): "Yes, I agree with this analysis. Go ahead" (classify the alignment-overflow sites R3-style), under the synthesis [USER 2026-10-03] "(1) agree with this" (where upstream's own semantics defines the answer and only OCaml's machinery crashes on the way, Lean computes it). A separate row rather than an extension of R3: R3 is one site with its own tray (13) and pin, and each row retires on its own when upstream fixes its site; R7's sites, pins and ruling are different, only the class is shared |

R4 (`dynamic_addrs`, tray 19) is DEFERRED [USER 2026-09-03] — mirrored,
not admitted (charter §2.6). The gate that asserts the register and the
marker set are in bijection is owed (charter §1.4 (vii)); today the
markers are `CerbDecode.lean` R1/R2, `CerbMem.lean` R3 (memcmp, added
2026-10-03), `CerbFloat.lean` R5 R6, `CerbMem.lean`/`CerberusImpl.lean` R7 (`grep "ISO-fix register R"`).

## 2b. The named-deviation register (class (e))

| Id | Difference and mechanism | Why not mirrored or refused | Witnesses | Lean site | Mover | Status |
|---|---|---|---|---|---|---|
| **N1** | A function pointer's NUMBER, observed through an integer conversion (`(intptr_t)&f`), the bytes of a stored function pointer, or `%p` of `(void*)fp`. In libc mode the same numbering artefact also changes function IDENTITY on the oracle: its funptrmap is keyed by number alone (`impl_mem.ml:1206`, upstream FIXME `:1044`), and a user function can draw the number of a libc static and replace its entry, so the oracle calls the wrong function (a spurious UB041 in the witness) where Lean, numbering from one supply, is correct (bug hunt BUG-1, 2026-09-29; tray 48; witness `zd-funptr-libc-conflate` DIFF / L=`Specified(1)`). Both engines serve the function symbol's number (`impl_mem.ml:1203-1220`, `:1047`; mirrored in `CerbMem.memValueToBytes`/`reconstructValue`), but that number is a fresh-supply artefact: the oracle's Core parser draws one per `std.core` symbol before the user TU (`core_parser.mly:184,220`), `CoreParser.lean` mints hashes. nolibc: oracle = Lean + 483 on the probes | Mirroring would mean reproducing the oracle's draw count for `std.core` (a numbering dependency the §5 renumbering principle calls a defect). Refusing: every stored function pointer uses these bytes, and `%p` prints through the pure printer with no memory state, so a precise refusal needs a byte-representation change. The integer conversion was refused for a few hours and broke libc's `atexit`, which round-trips a function pointer through `uintptr_t` (`runtime/libc/src/stdlib.c:194-199`); a round trip never observes the number, so refusing the conversion refuses correct programs (`docs/2026-09-28_funptr-int-refusal-record.md`) | `zd-funptr-int-direct` and `zd-funptr-int-voidptr` DIFF / L=`Specified(47)` (oracle 530); `zd-funptr-bytes-deviation` DIFF / L=`Specified(19)` (oracle 502); `zd-funptr-printf-deviation` DIFF / L=`(@empty, 0xa0)` (oracle `0x283`); the round trip is served and MATCHes (`zd-funptr-call-control`, libc_exec `040`/`041` atexit) | `CerbMem.intfromptr` `PVfunction` arm and `CerbMem.memValueToBytes` `PVfunction` arm (marker `-- named-deviation register N1`) | none planned: upstream artefact, tray 46; a representation change could refuse it later | **ADMITTED** [USER 2026-09-28] ("yes, re the decision, agree with (1). Named deviations are okay in cases we can't easily resolve the mismatch."); integer channel added [USER 2026-09-28] ("agree on atexit as you propose"); libc-mode identity consequence added [USER 2026-09-29] ("Agree on everything, yes on the fixes") |
| **N2** | A NaN's sign and payload bits in memory. Lean stores a float as `Float.toBits`, which canonicalizes every NaN to `0x7ff8000000000000` (measured; the disassembly of `lean_float_to_bits` in Lean 4.32.2 is `ucomisd; movq; movabs $0x7ff8000000000000; cmovnp`); the OCaml stores `Int64.bits_of_float` (`impl_mem.ml:1190`), which keeps them. Observed through the bytes of a stored NaN, union punning, `memcpy` of a double into an integer, and libc code that reads a double's bytes (e.g. a `signbit`) | Mirroring: Lean has no portable access to a NaN's bits (`Float.toBits`, `toString` and `toUInt64` all lose them). Refusing: every C variable lives in memory in this model, so refusing to store a NaN would refuse every program that merely computes one (e.g. to test `isnan`); the stored bytes carry no record that they came from a NaN, so no read-side refusal is precise. Printing a NaN with `%f` IS refused (it is precise; `CerbFloat.formatFixed`) | `zd-nan-bytes-deviation` DIFF / L=`Specified(127)` (oracle 255, gcc 255) | `CerbMem.memValueToBytes` `MVfloating` arm, both forms (marker `-- named-deviation register N2`) | a bit-level float representation (C floats as bit patterns with IEEE arithmetic in Lean, following x86 NaN rules; queued arc, TODO.md, [USER 2026-09-29] "Yes, let's queue as you propose"); a native float-bits seam was rejected (a new kernel-opaque boundary, host-CPU-dependent); upstream note `lean4/03` | **ADMITTED** [USER 2026-09-29] ("agree on all 3", on the orchestrator's recommendation to register the pre-merge audit's F2 as N2) |
| **N3** | Float constants in the libc Lean loads. Lean loads libc from the pinned text dump `tests/libc/libc.core`, which the oracle's Core printer writes with `%.12g` (`pp_core.ml:279-282`); the oracle runs the compiled `libc.co`, whose doubles are exact. The one lossy literal is line 60849, `1.84467440737e+19` for `0x1p64` = 2^64 (`runtime/libc/src/internal.c:303`, decfloat), parsed back 9 551 872 below 2^64, so Lean's `strtod` sets `ERANGE` near `DBL_MAX` where the oracle does not. ISO C11 §6.4.4.2#3 requires `0x1p64` to be exactly 2^64: the oracle is right, Lean is wrong | Fixing it within the dump needs an exact printer; an opt-in printing mode used only for the dump was rejected ([USER 2026-09-30]: "we should not fix deviations with special 'magic mode' paths that work exclusively in one situation"); the principled fixes (a round-tripping Core printer everywhere, or building libc from its C sources, which also fixes Z1-A1's missing libc locations) are queued work. No precise refusal exists | the inventory check `scripts/check_libc_float_literals.py` (row 1): every float literal of the dump = the reviewed register `scripts/libc_float_literals.txt` (24 literals, 1 LOSSY-N3), as multisets, both directions; a 12-significant-digit literal may not be registered exact; 8 plants | `CoreParser.lean` float-literal note (marker `NAMED DEVIATION N3`) | a round-tripping Core printer, or libc built from its C sources (TODO.md) | **ADMITTED** [USER 2026-09-30] ("Right, I think (3) is the right answer for now, and (1) or (2) might be work for later.") |

## 3. Every known Lean-vs-oracle difference, by class

The enumeration is the census — charter
`docs/2026-09-03_zero-discrepancy-design.md` §2 (77 rows at birth + the
Z1/Z2 additions §2.4b/§2.4c), one row per known difference with its
class, evidence and disposition; rows change class only by a commit that
cites its evidence. This section is the standing summary of what is NOT
a bug today and what is a bug still open, in the class vocabulary.

**(a) message text** — the members listed in §1(a). Nothing else.

**(e) named deviations** — the §2b register (N1: a function pointer's
number through an integer conversion, its bytes or `%p`; N2: a NaN's sign
and payload bits in memory; N3: float constants rounded in the pinned libc dump).
Nothing else.

**(b) resource — VIOLATIONS with named movers (bugs, not limits):**

- *Zero-initialised static aggregates above ~8 × 10^6 elements* HANG
  (exit 124, CPU/wall < 0.1; `char g[10000000]` does not complete,
  `char g[8000000]` does; the oracle completes 10 M in ~76–246 s). The
  mechanism is the Lean runtime entering closures by call in a
  function-typed monad's run loop (one `lean_apply_*` frame per element)
  plus the runtime's overflow-handler deadlock (tray `lean4/01`); record
  `docs/2026-09-02_mem-scale-record.md` §S1'. Movers: a lem-backend
  run-loop rendering of the monadic list combinators (lem-lean; TODO.md)
  and the upstream `.lem` accumulate-and-reverse shape (tray 18). Not a
  stack-size knob (a bigger stack only moves the silent onset).
- *Byte-list memory representation* — a large or program-computed
  allocation the oracle never touches is materialised on Lean
  (`tests/suite/parsing/array.c` out-of-memory panic; `pr20621-1.c`;
  `mem_malloc_4gb_lazy.c` OOM-KILLED at 6G). Mover: the representation
  change (chunked/sparse bytes with a compact unspecified-region form —
  `CerbMem.lean` byte path; profile first). Z2-M-04 already made
  `allocate_region` lazy for the untouched case, which moved
  `mem_calloc_overflow.c` from OOM-KILLED to agreement (Z4 docs record
  §2).
- *Exhaustive-mode wall-clock margins* — Lean is ~15–20× slower on
  recursion-heavy shapes with the same verdicts at a larger bound.
  Tolerated ONLY per row with measured completion: `pr63209.c`,
  `pr69320-4.c` have it (AGREE at 60–90 s); the 9 csmith `TIMEOUT` rows
  and the 11 gcc-lane `SKIP_LEAN_TIMEOUT` rows do NOT yet — each is a
  (b)-VIOLATION pending evidence until measured once (the code half of
  Z4).
- *(b)/fuel*: fuel exhaustion (`lem: fuel exhausted`, the FUEL class in
  every classifying lane; `sia_csmith_477/769` at the lane bound) — the
  accepted class, with the parameter (§7).

**(c) missing features — loud, attributed refusals (not bugs):**

- *Semantics switches* (`--switches=…`, `--iso`): since PNVI arc S4 (2026-10-07,
  `docs/2026-10-07_pnvi-s4-lane-record.md`) the base non-default set is SUPPORTED —
  `--switches=PNVI_ae_udi` (both cmdliner forms; a one-element list), matched against the
  oracle under the SAME switch by `scripts/test_pnvi.sh` (§5, LADDER Tier A row 14; the
  run's instance `⟨[.PNVI .AE_UDI]⟩`, one general path — the set only selects the arms).
  The optional `permissive_pointer_arith` combination has a narrower, eight-program
  check in `scripts/test_permissive_pointer_arith.py`: temporary outside pointers,
  concrete subtraction across allocations, address round trips and ambiguous provenance, and rejection
  of null arithmetic/subtraction and out-of-bounds loads. Each verdict and UB location
  must match the OCaml engine; the expected outcome is also checked independently.
  Four `PnviArmsTest` unit checks additionally pin symbolic-provenance preservation
  during shifts/subtraction and shifting a pointer without provenance.
  Other values are REFUSED, each element with its reason (`Main.judgeSwitches` /
  `refuseSwitches`; exit 2, attributed; [AGENT] Q7 recommendation "REFUSE now … plumbing … is
  not wanted", accepted [USER 2026-09-03] for the rest): the other switch names, plain `PNVI`/`PNVI_ae` (unvalidated,
  design §F.3), other mixed lists, `--iso`, and the two places the ORACLE is fail-open
  (design §C.5) — an override in one list (**R-PNVI-11**: the oracle prints "would override
  a previous switch --> ignoring." and runs on) and an unknown name (**R-PNVI-12**: "failed
  to parse switch … --> ignoring."); witnesses `scripts/check_cli_refusals.sh` (row 1).
  **Refusals inside the PNVI-ae-udi semantics** — class (c), [USER 2026-10-05] "Re PNVI - agree on
  your recs except for mirroring crashes / obviously wrong behavior. These should be refusals
  surely?": the upstream arms on the PNVI path that crash, print debug output or call
  themselves wrong are `CerbMem.pnviRefusal` refusals (exit 134 under `LEAN_ABORT_ON_PANIC`,
  message `PNVI_ae_udi refusal (unsupported upstream arm): R-PNVI-nn: …`, design §G, §H):
  R-PNVI-01 (`combine_prov`'s `Prov_symbolic` arm, impl_mem.ml:390-394) and -01b
  (`provs_of_bytes`, shadowed by -01), -02 (`find_overlaping`'s `assert false`), -03 (its
  silently dropped third candidate), -04 (`lookup_iota`'s `Not_found`), -05 (`abst`'s "This is
  wrong" `DoubleAlloc` arm), -06 (pure `array_shift_ptrval` on a symbolic pointer), -07
  (`case_ptrval` on a symbolic pointer), -08 (`diff_ptrval`'s invariant failure), -10 (the
  stdout `Printf.printf` arm of `eff_array_shift_ptrval`). **Fork ≠ Lean on these rows, by
  design**: where the oracle crashes (-01, -06, -07 in the lane) or answers through the
  flagged arm (-05), Lean refuses; the lane records each such row as `REFUSAL R-PNVI-nn
  ORACLE_CRASH|ORACLE_VERDICT` with the oracle's side hash-pinned — a registered refusal,
  never agreement, never "both crash alike". Witnessed in the lane: -01 (4 upstream litmus
  files), -05, -06, -07 (`tests/pnvi_refusals/`); the others by compile-time pins
  (`test/Unit/PnviArmsTest.lean`); reach: -01b/-02/-04 (unreachable by invariant) and -03
  (UNKNOWN) are the failure-reach register's reviewed rows, while -08 and -10 are MONADIC
  sites (`pnviRefuseM`) outside that pure-site census — their reach is UNREVIEWED.
  **Default path unchanged** (design §H, §H.1): the (A)/(B)/(C)-shaped upstream sites that are
  ALSO on the default path stay exactly as before (mirrored fail-stops / kill-without-print),
  including `eff_array_shift_ptrval`'s `PVfunction` arm — R-PNVI-09, reclassified a
  default-path look-alike and NOT placed — pending the queued default-path consistency review;
  the default set `[]` stays bit-identical (every default lane at its baseline).
  Matched default-switch mode is the contract for every other input; since 2026-09-05 the `CerbGlobal`
  config/switch surface is eleven plain `def`s of the driver's DEFAULT
  configuration (kernel-transparent, `rfl` lemmas — no opaque boundary
  row remains; `docs/2026-09-05_cerbglobal-defs-record.md`), so every
  `Switches.has_switch` read in the exec cone evaluates as the oracle's
  default by definition;
  since the seam-hygiene slice (2026-09-19, `docs/2026-09-18_seam-hygiene-record.md`
  §4) unported switch-conditioned arms of `impl_mem.ml` are written in `CerbMem` in the
  explicit `if has_switch … then <loud kill> else <default>` shape; the supported
  PNVI and permissive-pointer arms implement their upstream behavior — `CerbSwitch`
  carries the four switches those arms test (`strict_pointer_equality`,
  `strict_pointer_relationals`, `pointer_arith PERMISSIVE|STRICT`,
  `zero_initialised`, mirroring `switches.ml`), so the specialisation to the empty
  set is kernel-visible (`CerbGlobal.has_switch_*_eq`, by `rfl`; since PNVI arc S1, 2026-10-05, the switch set is the
  instance-implicit parameter `[CerbGlobal.Switches]` and the facts are `has_switch_*_default` at `⟨[]⟩`, the
  instance `Main.lean` supplies — `docs/2026-10-05_pnvi-s1-switch-parameter-record.md`) and greppable, and
  the Z2 record's formerly DECLARED row Z2-M-20 is closed; `using_concurrency` is `def … := false` with
  `using_concurrency_eq : using_concurrency () = false := rfl`, its
  parameterisation remains separate work; the concurrency feature branch is parked.
  The oracle's switches CHANGE the answer (under `PNVI_ae_udi` an integer→pointer UB043
  becomes a value), so each unsupported switch is a feature we do not have, not a
  difference we hide; `PNVI_ae_udi` has its own lane; the permissive combination has the focused checks above.
- *Concurrency* (`--concurrency`): REFUSED, attributed — "not supported;
  the oracle's own mode is non-functional at `b9aeedcb4`" (`internal
  error: CONCURRENCY IS BROKEN`, `nondeterminism.ml:64` via `smt2.ml:38`).
  In matched mode atomics run sequentially and AGREE on both engines
  (`elab_atomic_qualifier_seq.c`, 8 traces each). The operator declared the SC prototype failed on
  2026-09-24 (ruling in TODO.md). It and `feature/concurrency` are parked
  records, with no announcement dependency. The refusal is the contract.
- *CerbFS*: REFUSED IN FULL since 2026-09-28 (contract D2, [USER
  2026-09-28] "refuse FS for now, this seems safer";
  `docs/2026-09-28_cerbfs-refuse-all-record.md`): every one of the 25
  `fs_*` operations, including `read` on any fd (so C-level stdin),
  fails loudly (`PANIC … CerbFS refusal (fail-closed fs-model boundary):
  <op> …`, exit 134). `write`/`vprintf` on fds 1/2 never reach CerbFS
  (the driver routes them to the stdout/stderr records). The served
  subset it replaced had thin positive coverage and served a wrong answer
  on path spellings (the external pathleak report,
  `docs/2026-09-28_cerbfs-path-hotfix-record.md`). Mover: a
  SibylFS-faithful filesystem model (TODO.md).
- *Inline assembly* (contract D9, 2026-10-05; [USER 2026-10-05] "Re inline
  asm, this should be a loud refusal"; `docs/2026-10-05_asm-refusal-record.md`):
  REFUSED in BOTH engines — a refusal, not an ISO fix (it invents no asm
  semantics; §2 is untouched). Upstream erases inline assembly: an asm
  statement desugars to a skip (`cabs_to_ail.lem`, "TODO: erasing inline
  assembly for now") and an asm label on a declarator is dropped by the
  parser (`c_parser.mly` `asm_register`), so a program whose meaning lives in
  its asm ran as if it were absent (real-C census §4.5: `Specified(1)` on both
  engines where gcc gives 5). Now an asm statement — basic, extended,
  `asm goto`, reached or not — fails desugaring in the SHARED `.lem`
  (`Desugar_NotYetSupported "inline assembly (asm statement) is
  unsupported"`: oracle exit 1 with `feature not yet supported: …`; Lean
  `--batch` exit 1 with `Error {msg: "desugaring failed at <asm loc>"}`, the
  cause line naming the feature without `--batch`), and an asm label fails in
  the SHARED parser (`unimplemented keyword 'asm (inline assembly label on a
  declarator is unsupported)'`, exit 1, `--exec` and `--cabs-json` alike — no
  Cabs reaches Lean). Not attributed, but already loud upstream: file-scope
  `asm(...)` (not in the grammar — a syntax error) and `__asm(...)` (an
  undeclared identifier). Witnesses: `scripts/check_asm_refusal.sh` (row 1).
  No gated lane row moved; five Tier C scoreboard rows (`torture_not_std_compliant`)
  move MATCH → reject when the scoreboard is next re-recorded. A deliberate
  fork ≠ pristine difference (below; `scripts/fork_drift_manifest.txt`).
- *`LEAN_ABORT_ON_PANIC` required* (Z2-FL-03): the driver refuses to
  start (exit 2) without it, because a Lean `panic!` — the fail-stop
  mirror of every OCaml failwith/assert/uncaught exception — would
  otherwise print and CONTINUE with a default value. Every harness sets
  it (`scripts/common.sh run_cerberus_lean`).
- *Zero executions from `runND`* (Z-73, [USER 2026-09-03] Q8 = A): Lean
  prints `Error {msg: "cerberus-lean: runND returned no executions"}` and
  exits 1 where the oracle prints nothing and exits 0 — a DECLARED loud
  boundary (a silent success with no verdict is the fail-open shape the
  working practices ban; the oracle's behaviour is a tray candidate).
- *Runtime resolution* (bug hunt BUG-2, fixed 2026-09-29,
  `docs/2026-09-29_bug-hunt-fixes-record.md` §S2): `std.core` and the
  `.impl` file come from `--runtime DIR` or `CERB_INSTALL_PREFIX`
  (runtime = `DIR/lib/cerberus-lib/runtime`, the oracle's SPECIFIED and
  ENV_VAR arms, `util/cerb_runtime.ml:38-56`); without either the driver
  REFUSES (exit 2, `cerberus-lean: refused — runtime: …`). The oracle's
  OPAM arm (`OPAM_SWITCH_PREFIX` or the build-tree source root) is
  deliberately not mirrored: a shared switch's runtime can differ silently
  from the checkout's. An empty value is refused (the oracle would resolve
  it against the working directory). The working directory is never
  searched (it used to be, first `runtime/libcore/std.core` found wins).
  Witnesses: `scripts/check_runtime_resolution.sh` (row 1).
- *Library-location classification outside the runtime* (bug hunt BUG-3,
  fixed 2026-09-29, same record): a Cabs location whose directory ends in
  `runtime/libcore`, `runtime/libcore/impls` or `runtime/libc/include`
  but is not that directory of THIS run's runtime is REFUSED at import
  (exit 2, `cerberus-lean: refused — library-location classification: …`).
  The oracle tests exact equality (`util/cerb_location.ml:512-523`); the
  port's pure `CerbLocation.isLibraryLocation` tests the suffix, and the
  refusal makes the two agree on every served run. A cabs-json exported
  under a different runtime prefix refuses the same way (its `builtins.h`
  location). Witnesses: the same script.
- *Non-UTF-8 bytes in the Cabs JSON* (bug hunt BUG-6 and K-5, refused since
  2026-09-29, `docs/2026-09-29_bug-hunt-fixes-record.md` §S3; before that a
  class-(b) residual that died with an uncaught exception, rc 1, and listed
  only the text fields). The oracle's `--cabs-json` exporter copies the bytes
  ≥ 0x80 of a FILE NAME (the real path, a `#line` or an `#include` name,
  `cabs_json.ml:30` `Cerb_position.file`), of a `Loc_other` string (`:44`),
  of attribute-argument strings (`:599`/`:601` — WHOLE strings,
  `c_parser.mly:1771-1775` concatenates the literal's fragments before the
  exporter sees them) and of magic-comment text (`EDecl_magic`, `:657`)
  into the JSON raw, so the document is not UTF-8 while the oracle's own run
  proceeds. Lean strings are Unicode scalar values, so the bridge cannot
  carry them: `Main.decodeCabsJson` REFUSES (exit 2, `cerberus-lean: refused
  — non-UTF-8 Cabs JSON: …`, naming the fields, the boundary and the first
  invalid offset) — user TUs, `--stdin` and the libc metadata TUs alike.
  String-literal fragments and character-constant bodies are byte-carriers
  (since the 2026-09-11 fix, `docs/2026-09-11_semantics-audit-repairs-record.md`
  §D2) and never reach it. Witnesses: `scripts/check_cabs_json_utf8.sh` (row
  1: `#line` raw byte, `#line` octal escape, a real file name, an `#include`
  name, an attribute string; ASCII controls agree with the oracle). Mover:
  a byte-carrier encoding for the file-name, `Loc_other` and text fields.
- *Accepted command line:* `--batch | --pp-core | --parse-core` (argv[0]),
  `--first`, `--stdin`, `--libc <core>`/`--libc-tu <json>`, `--call <f>`
  [`--call-args`], `--args <str>`, `--trace-nodes`, `--runtime <DIR>` / `--runtime=<DIR>`, `--fuel <N>`, `--address-space-top <N>`
  (address-space-bound slice, 2026-09-17: the run's address-space top, a positive
  integer; absent = upstream's value; 0 or a non-numeral refused, exit 2 — §7); any
  other `--` token, or a known flag out of its canonical position, is
  refused (Z-24; it used to be treated as a file name).

**(d)** — the register, §2 (R1, R2, R3, R5, R6, R7).

The libc-mode allocation-address ordering defect **Z-28 is fixed** by the
Z3 mirror (`2ddc1300c`, already in mainline). The
[Z3 record](docs/2026-09-05_zero-discrepancy-Z3-record.md) records the source
repair and the address-printing programs' agreement. The old committed
sweep's STDOUT_DIFF rows are historical, not an outstanding Z3 implementation
task; current measurements are in the CI reporting record.

The `aligned_alloc(0, n)` row **Z2-M-01 is mirrored** (2026-10-03): upstream's
`op_ival` `IntRem_t`/`IntRem_f` (`impl_mem.ml:2481-2484`) have no zero guard,
so `std.core:385`'s `size rem_t align` raises `Division_by_zero` (uncaught,
exit 125); Lean's `CerbMem.integerRem_t`/`integerRem_f`/`integerDiv_t` now
fail-stop on a zero divisor in the same place (both-crash `MATCH | L=CRASH`,
`zd-z2m01-*`), under [USER 2026-10-03] "we don't innovate wrt
Cerberus-upstream, unless something is very very very obviously a bug ...
we should fall back to loudly rejecting (either as unsupported, or matching
upstream)". The Z2 record's §10.1 recommendation (a Core-level UB045 or a
`std.core:385` guard) is withdrawn as invention under that rule
([record](docs/2026-10-03_total-arith-and-bookkeeping-record.md)).
The same record's sweep (§2) found two more crash sites, both reachable
through a front-end-accepted `_Alignas(2^62)`: upstream reads member
alignments through `Z.to_int` (`impl_mem.ml:248/:267`,
`ocaml_implementation.ml:483/:501`), which raises `Z.Overflow` outside
OCaml's native int range. They were briefly mirrored as stops; under the
2026-10-03 rulings (record §7) they are a host artifact where upstream's own
semantics defines the answer, so Lean computes it — ISO-fix register R7,
pins `zd-ta-alignas-huge-*` ORACLE_CRASH. The sweep's unreachable sites and
operator items are listed in the record.

**Still open (bugs by the rule; each with its owner):**

- *libc-body UB locations* (Z1-A1): a UB raised INSIDE a libc C body
  carries the libc source location on the oracle and `<unknown
  location>` on Lean (the `--libc` pin is the oracle's Core TEXT dump,
  which has no locations). BUG-FIX with a named mover: a libc pin vehicle
  that carries locations. Surfaces as `UB_DIFF` rows in the sweep
  re-record.
- *In-process consumers and the library-location check* (bug-hunt fixes
  pre-merge audit L4): the driver refuses, at import, any location whose
  path passes `CerbLocation.isLibraryLocation`'s suffix test but not the
  oracle's exact test against the runtime root, which makes the two tests
  agree on every accepted input and retires Z-67 for the driver. A
  consumer calling `CabsImport.parseJson` and `isLibraryLocation` directly
  bypasses that check and keeps the Z-67 residual unless it applies the
  same check with its runtime root.
- *In-process consumers and kind-1 fail-stops*: no universal `drive`
  conformance theorem follows from avoiding known failure sites; byte,
  runtime-state and other obligations also remain. `failwithI` has an
  opaque logical definition with a default-valued implementation and a
  native panic override. When a result is discarded, even the native
  executable can erase the failure. Kernel reduction can also discard a
  mapped projection whose native execution aborts. The measured probes and
  strict-result correspondence proposal are in the
  [failure census](docs/2026-09-06_failure-census-and-correspondence.md).
  The earlier typed-failure ruling remains recorded; implementation beyond
  this charter's census/proposal awaits the final design discussion.
- *Instruments, not semantics:* `test_elab.sh`'s 3 recorded DIFF rows are
  a pretty-printer main-file filter difference (Z-40; `Main.lean
  ppCoreSignature` should mirror `pp_cond`); the committed
  `tests/ci_sweep/results/*.tsv` are a 2026-08-22 snapshot whose 43
  `CERB_INCONSISTENT` rows and `pr44468.c` row are stale (Z-42/Z-75) — a
  row that SURVIVES the re-record as `CERB_INCONSISTENT` is a
  bridge-attribution question, never INSTRUMENT by default. Both are the
  code half of Z4.
- *Oracle-suspect rows* (Lean == oracle ≠ ISO/gcc) are CORRECT under the
  rule and are NOT open bugs here: each is mirrored, pinned so a future
  "fix" toward ISO trips the exec lane, and recorded as a tray draft (INDEX
  20–35). The gcc lane records them as `TRIAGED_*` today; the distinct
  `PINNED_TRAY_<n>` class (a confirmed shared-source oracle bug with a
  draft; the pin flips to AGREE on the upstream fix, any other movement
  is a regression) is owed by the code half of Z4 (charter §4.2).

**Fork ≠ pristine — the register (`scripts/upstream_oracle_differences.json`,
schema 2; gate: LADDER Tier B row 10).** These are not Lean-vs-oracle rows:
they are the fork OCaml's reviewed deviations from pristine upstream
`b9aeedcb4` as OBSERVED on row 10's corpora — the mirror twin's own exception
list (§0, the reference doctrine). Source-level fork≠upstream deltas that no
walked corpus witnesses are recorded as content pins in
`scripts/fork_drift_manifest.txt` (§6) and become register rows only once a
corpus observes them — a deliberate shared-model FIX the fork takes ahead of
upstream is nevertheless listed BELOW the moment it lands, with its citation
and pins, so the inventory here is complete even where the register is
silent; and "unobserved on the corpora" is a CLAIM to be tested by seeking a
witness, never assumed — the allocator fix of 2026-09-16 was first labelled
UNOBSERVABLE here and the label was FALSE (a 13-line program witnesses it;
its rows are below, added by the part-one pre-merge audit's finding M1). Every row binds both engines' signatures (exit status, stdout
sha256, stderr sha256 under the lane's diagnostic projection) and moves only
by a cited re-record.

- **`shared-model-fix` (1 row; citations upstream-tray draft 37,
  `tests/multi_tu_tray/README.md`):** `multi_tu_tray/node` — pristine does
  not terminate (`Ctype_aux.are_compatible` recurses forever on a
  self-referential struct defined in two TUs, draft 37; rc 124 at the lane's
  30 s bound — one of the two pristine-side incompletes the register admits, with
  `coverage/alignas/alignas-001`, where pristine also hangs (tray 47)). The
  fork's `are_compatible` terminates (draft 37's assumed-compatible set), so
  the fork reaches `PEmemberof(struct)`'s exact-tag guard, which is upstream's
  text: `Error {msg: "ill-formed program: \`PEmemberof(struct) ==> mismatched
  tags: Symbol(531, SD_Id("node")) vs Symbol(502, SD_Id("node"))'"}` rc 1, the
  same rejection pristine gives every other cross-TU struct value in the tray.
  The row retires (the case moves into `tests/multi_tu/`) when upstream fixes
  draft 37. Row 6b pins fork OCaml == Lean on the same input.
  History: from D3 (2026-09-15, `dbe633ec5`) until 2026-10-03 the fork also
  carried draft 38's `are_compatible` consult at that guard. `node`,
  `arr-2-2-return` and `arr-incomplete-ptr-return` then answered
  `Specified(7)`, and the latter two had rows here (pristine rejected them at the
  exact-tag guard). The consult was REVERTED on 2026-10-03 (branch
  `fix/mirror-upstream-d38-alignas`, record
  `docs/2026-10-03_mirror-upstream-d38-alignas-record.md`), under [USER 2026-10-03] "Generally, our rule
  is that we don't innovate wrt Cerberus-upstream, unless something is very
  very very obviously a bug. We're poorly placed to resolve semantic
  discrepancies, so we don't. ... fall back to loudly rejecting (either as
  unsupported, or matching upstream)." cerberus-sl confirmed it does not rely on
  cross-TU `PEmemberof`. Those two cases now agree with pristine, so their rows
  are gone. Draft 39's one-token array-bound fix stays.
- **`shared-model-fix` — the allocator's EXHAUSTED regime (2 rows, added 2026-09-17
  by C1c; citations upstream-tray draft 44 +
  `docs/2026-09-16_allocator-soundness-address-bound-record.md`; TRUE BUG / model
  soundness; [USER 2026-09-16] *"unambiguously wrong … allowed to fix ahead of
  upstream"*):** `minimal/112-allocator-exhausted-single-request` and
  `minimal/113-allocator-exhausted-single-request-overlap`. Pristine `b9aeedcb4`
  `memory/concrete/impl_mem.ml:1254` (VIP twin `:209`) aligns the new base with
  the truncating-division idiom `z - (if q < 0 then -m else m)` over the
  EUCLIDEAN `quomod = ediv_rem` (`:9`), so once the cursor is below the request
  (`z = last_address - sz < 0`, within `-align/2 < z`) the allocation SUCCEEDS at
  an address in `(0, align)` — overlapping the live object at the cursor,
  misaligned. OBSERVABLE at upstream's own bound by ONE request larger than the
  cursor: the program reads its cursor as `(uintptr_t)malloc(1)` and requests
  `a - 7` bytes (`malloc_proxy`'s 8-byte argument temporary puts the cursor at
  `a - 8`; `z = -1`, `IvMaxAlignment` 8) — pristine `Defined {value:
  "Specified(6)", stdout: "", stderr: "", blocked: "false"}` rc 0 (112) and
  `"Specified(106)"` (113: address 6, + 100 "ends above the cursor", + 0 "not
  8-aligned"); the fork AND Lean `Error {msg: "MerrOther "Concrete.allocator:
  failed (out of memory)""}` rc 1. Found by the part-one pre-merge audit
  (`docs/2026-09-17_allocator-part-one-audit-premerge.md` M1, branch
  `audit/allocator-part-one`); UNOBSERVED by every previously walked corpus (no
  corpus program requested within `align/2` of its cursor) — the §0 doctrine's
  missing-case disjunct, now closed: both witnesses are `tests/minimal` rows
  (`scripts/exec_baseline.txt`, class `CERB_SKIP`: the exec lane does not sample Lean after an oracle `Error {` line, so these two rows GATE nothing on the Lean side — fork = Lean on them is evidenced by the kernel theorem, the unit witness's exact kill text and the three-engine report's `lean_agreement`, not by a pinned baseline; a gating pin is `tests/immaculate/nolibc` rows, part two's first instrument commit) and register rows. The C1
  text of this entry called the deviation "UNOBSERVABLE at upstream's bound
  (~2^48 bytes of cumulative allocation needed)" — FALSE; one request suffices.
  The fork takes remedy 1 in BOTH OCaml models (`memory/concrete/impl_mem.ml:
  1255-1263`, `memory/vip/impl_mem.ml:210-218`: the existing out-of-memory kill
  BEFORE rounding, then a plain align-down; the dead branch deleted) and in the
  Lean mirror (`CerbMem.lean` `allocator`, line by line), with the GENERAL kernel
  theorem `CerbMem.allocator_active_sound` (`CerbMemAllocatorProofs.lean`: an
  ACTIVE allocation is `align`-aligned, strictly positive, its end `a + sz` at or
  below the cursor — disjoint from everything at or above it, for `sz ≥ 0` — and
  becomes the cursor; no hypothesis on `sz`/`align`; axioms `propext`,
  `Classical.choice`, `Quot.sound`) and `allocator_below_request_kills` (remedy 1
  in kernel terms), plus the runtime witness `allocator-soundness-test` (the four
  draft-44 states on the actual `CerbMem.allocator`, the pre-fix values as the
  negative control). Fork engines AGREE with each other (Tier A rows 1–4b unmoved;
  the two new exec rows are `CERB_SKIP`, see above — the agreement on them is the theorem + witness + three-engine report); both files' content pins moved
  (`scripts/fork_drift_manifest.txt`, header notes "allocator-soundness C1"/"C1c").
  The rows retire when upstream takes the fix. A tiny address-space bound (the
  charter's part two, C2/C3) widens the witness set; it does not create it.
- **`shared-model-fix` — `_Alignas` completeness (3 rows, added 2026-10-03; branch
  `fix/mirror-upstream-d38-alignas`; record
  `docs/2026-10-03_mirror-upstream-d38-alignas-record.md` §2; citation upstream-tray
  draft 47):** `desugar_alignment_specifier` (`cabs_to_ail.lem`) applies C11
  §6.5.3.4#1 (via §6.7.5#5) to `_Alignas(type-name)`, reusing
  `AlignofInvalidApplication`. The rulings are [USER 2026-09-27] F-A2 "yes,
  'constraint violation' - and this goes in the tray if it isn't there already"
  and [USER 2026-10-03], agreeing to "keep only the completeness check and mirror
  upstream on alignment compatibility".
  - `coverage/alignas/alignas-001-self-char.c`: pristine does not terminate
    (rc 124). It is admitted only through this cited row.
  - `alignas-002-fwd-char.c` and `-003-self-int.c`: pristine raises an uncaught
    `Not_found` (rc 125).
  - On all three, the fork prints the `AlignofInvalidApplication` constraint
    diagnostic on stderr, rc 1. They are `CERB_SKIP` in
    `scripts/exec_coverage_baseline.txt`, because the exec lane does not sample
    Lean after an oracle refusal that has no batch verdict.
  - Lean refuses at the same source location (`Error {msg: "desugaring failed at
    <loc>"}`, rc 1). The record's three-engine table is the evidence for that; no
    pinned lane row covers it.
  - The control `alignas-004` agrees on every engine.

  The alignment-COMPATIBILITY half that the record branch `fix/alignas-p2d3`
  (`cf4af48f8`) also wrote was deliberately not taken. `ctype_aux.lem` keeps
  upstream's `(*TODO alignment*)` placeholders. The `cabs_to_ail.lem` content pin
  and the generated `cabs_to_ail.ml` delta pin moved
  (`scripts/fork_drift_manifest.txt`, header note "task 2"). The rows retire when
  upstream takes draft 47's fix.
- **Fork refusal — inline assembly (0 register rows; added 2026-10-05; contract
  D9; record `docs/2026-10-05_asm-refusal-record.md`):** the fork REFUSES what
  pristine ERASES (§3(c) above): `cabs_to_ail.lem`'s `CabsSasm` arm fails with
  `Desugar_NotYetSupported` where upstream returns `AilSskip`, and
  `c_parser.mly`'s `asm_register` action raises `Cparser_unimplemented_keyword`
  where upstream drops the label. No program on row 10's walked corpora
  contains inline assembly (grep over `tests/`, `runtime/`, `lean_frontend/`,
  the CN corpus and the libxml2 TUs, record §2), so the register has no row;
  the content pins (`cabs_to_ail.lem`, the NEW `parsers/c/c_parser.mly` row)
  and the generated `cabs_to_ail.ml` delta pin moved
  (`scripts/fork_drift_manifest.txt`, header note "fix/asm-refusal"). Upstream
  disposition: none planned — the refusal is the fork's contract, not a fix
  for upstream to take [AGENT].
- **`diagnostic-text` (0 rows; a permitted class).** RESOLVED [USER
  2026-09-17] ("(2) agree", on the orchestrator's question — record §7): the
  lane's diagnostic projection — the one `matching_failure` and the
  register's stderr signature already used (the `Time spent` trailer removed)
  — additionally normalises `line N[-M], characters A-B` positions inside
  OCaml backtrace frames (`Raised at` / `Raised by primitive operation at` /
  `Called from` / `Re-raised at … in file "…"`) in BOTH engines' stderr, and —
  allocator-soundness C1b, 2026-09-17; [USER 2026-09-17], verbatim: *"yes,
  agreed regarding landing C1 as-is and then working on C2/C3 separately"*,
  given on the orchestrator's proposal that this projection be extended to the
  header (the proposal's text is quoted verbatim in record §S1,
  `docs/2026-09-16_allocator-soundness-address-bound-record.md`) — the same
  position in an OCaml exception HEADER line `File "<path>",
  line N[-M], characters A-B: <text>` (the `Assert_failure`/`Match_failure`
  printers; a fork edit ABOVE an assert site shifts it exactly as it shifts
  frames: C1's +5 lines moved `impl_mem.ml`'s `memcmp` assert 2659 → 2664,
  `immaculate/libc/g2-memcmp-uninit`, record
  `docs/2026-09-16_allocator-soundness-address-bound-record.md` §S1), the path
  and the text after the colon still byte-compared; the exception text, the
  frames' function and file names, non-frame lines (a Cerberus diagnostic
  quoting `line N, characters A-B` included) and every stdout byte (a
  header-shaped stdout line included) are compared untouched, and the raw
  stderr is retained in every capture. A both-crash pair whose frames differ only in positions
  (generated `.ml` line numbers shifted by the fork's `.lem` edits,
  `lem_list.ml` frames from the different Lem runtime, `pipeline.ml`/`main.ml`
  frames from the fork's driver additions) is therefore a `matching_failure`
  — `minimal/097`, the 16 `tests/immaculate` both-crash pins and the 4
  `tests/ci` `.error.c` rows all read so (row 10 `matching_failure` 11 → 28,
  C6 102 → 106) and the 21 rows that had pinned them were DELETED. A genuine
  exception-TEXT difference still needs a cited row of this class
  (plant-tested: an exception-text, frame-function or non-frame-position
  difference stays `difference`).
- **`matching_incomplete` — a REPORTED class, never a register row.** RESOLVED
  [USER 2026-09-17] ("(1) agree"): when BOTH engines exceed the owning lane's
  own bound (status 124 on both sides) the case is counted
  `matching_incomplete` — never agreement, not a failure; any ONE-sided
  timeout (either side) and any 137 stay `incomplete` and fatal exactly as
  before, and no register row is written for a matching timeout (the loader
  still refuses fork-side 124/137). The class is for UNREGISTERED cases: a
  registered case is always judged by its row, so a both-sides timeout (or a
  fork timeout) on a registered case is `difference` — the pin moved
  (pre-merge audit M1, [AGENT] reading flagged to the operator). Standing members: `tests/ci`
  `0023-jump1.c`/`0025-jump3.c` (30 s) and 21 of the first csmith shard's 50
  programs (15 s) — the fork lanes' own `CERB_SKIP` rows. `--corpus ci` and
  `--corpus csmith --shard K/34` are Tier C reporting rows that now exit 0
  (C6: 134 agree / 2 `matching_incomplete` / 106 `matching_failure`; shard
  1/34: 26 / 21 / 3).

## 3b. Deviations the consumer relies on (cerberus-sl)

The rule is [USER 2026-10-03]: "Generally, our rule is that we don't innovate wrt
Cerberus-upstream, unless something is very very very obviously a bug. ... fall back to loudly
rejecting (either as unsupported, or matching upstream)." That rule can prompt reverting
deviations taken earlier. Some of those deviations are load-bearing for the consumer, cerberus-sl,
which pins this repository by commit. The operator's framing is: "we shouldn't revert work that
allows the iris reasoning to work properly" ([USER 2026-10-03]).

cerberus-sl stated (orchestrator relay, 2026-10-03) that it relies on the five behaviours below.
The names in the right-hand column are cerberus-sl's own (`CerberusIris/CerberusIris/…`).

| Fork behaviour | Where it is recorded here | What cerberus-sl uses it for |
|---|---|---|
| `--address-space-top N`, the address-space top as a parameter of both engines (pristine has no such flag; §7, `docs/2026-09-17_address-space-bound-part-two-record.md`) | §7 "address-space top"; Tier A row 12 | `Interface.AdmittedTop` (the admitted tops `0 < top < 2^64`) and the theorems quantified over them |
| The run digest as run-state data (`core_run_state.sym_digest`, seeded from the last program TU; D-S, `docs/2026-09-22_run-digest-as-state-record.md`) | §9 boundary list (the FRONTEND digest seam) | `AdequacyG.adequacy_wp_G`'s premise `rs.sym_digest = P.digest` |
| The enum reader: an enum's compatible type is program data (`enum_definitions` / `file.enumDefs`; E-A, `docs/2026-09-20_program-data-parameters-EA-DA-record.md`; unit exe `enum-data-test`) | §9 boundary list ("`CerberusImpl`'s enum registry — LEFT the boundary") | the enum rows (enum layout and `Ivmin`/`Ivmax` read through the pinned reader, e.g. `BoolEnumExamples`) |
| The fail-closed tuple-arity matcher (`match_pattern`/`typecheck_pattern` refuse a tuple-arity mismatch; `docs/2026-09-20_match-pattern-arity-record.md`; unit exe `match-pattern-arity-test`) | that record; upstream-tray draft 45 | `RoundThread.pick_complete` / `pcall_complete` |
| The fuel-indexed ND runner and its exhaustion and out-of-memory outcomes (`CerbND.runNDFuel`, the kill `CerbND.fuelExhaustedKill`, the allocator's `MerrOther "Concrete.allocator: failed (out of memory)"`) | §7 | `CerbND.runNDFuel` / `fuelExhaustedKill` and `Interface.oomOutcome` |

cerberus-sl does NOT rely on cross-TU `PEmemberof` struct compatibility (draft 38). That was
confirmed before the 2026-10-03 revert (§3, `multi_tu_tray/node`).

**Rule.** Before any retrospective revert of a fork deviation (a "mirror upstream" pass, a
register clean-up, a re-pin that drops a fork change), check this list. If the deviation is on
it, or might feed one of these names, ask cerberus-sl first (re-pin notes and consumer questions
go to its repository, `scripts/semantics-pin.env`), and record its answer with the revert. This
list is the consumer's statement as of 2026-10-03. It is not proof that nothing else is used. A
deviation that is absent from it still gets the question whenever the consumer's proofs might
touch it.

## 4. What is compared, against what

**The oracle.** The OCaml Cerberus in this repository, built from the
same `.lem` sources (`make prelude-src` + dune). It is an *immovable
object* on the trust boundary. Plain-batch lanes decode complete verdicts
and validate process completion through the shared
[observation contract](docs/2026-09-05_observation-contract.md). `Defined`
includes value, stdout/stderr bytes and blocked state; `Undefined` includes
UB code, stderr and location; `Error` retains its full printed message.
The contract's matrix names each lane's ordering and projection: GCC uses
native exit membership, call-point pins project a single value/UB, and
legacy printer/reference checks retain their documented narrower purpose.
An acknowledged baseline difference or refusal is not observation agreement.

**Pristine upstream, the reference (§0).** The independently compiled
pristine engine (`b9aeedcb4` + upstream Lem `3802cb0`; kept standing by
`scripts/ensure_independent_oracle.py`, which reuses the lane's own
fail-closed manifest validator and never deletes or overwrites a build) is
compared with the fork OCaml by LADDER Tier B row 10 over every corpus the
fork-vs-Lean lanes GATE on — `tests/{minimal,coverage,debug,float,bytes,
libc_exec}`, `tests/multi_tu` + `tests/multi_tu_tray`, the 213 CN rows, the
libxml2 `uri` harness (libc and nolibc), `tests/immaculate` (nolibc/argv/
libc), `tests/verify` + the `lean_frontend/corpus` main-mode fixtures, and
two legacy CLI modes (855 cases, ~2 min warm); libxml2 `chvalid` is its own
Tier B row (4 slices, ~7 min); `tests/ci` and the csmith corpus are
reporting rows; `test_ci_sweep.sh`'s fourteen other suites (Tier C row C4,
`tests/gcc-torture/breakdown/*`, `tests/tcc`, `tests/suite`,
`tests/pnvi_testsuite`, `tests/hacl-star`, `tests/freebsd`, `tests/examples`,
`tests/cheri-ci` — a scoreboard with no baseline) are not walked and are
named in the report's `not_applicable`. Each corpus runs with the flags,
exclusions and per-case timeout of the lane that owns it (cited in
`corpus()`; `libc_exec` and `uri` at their lanes' 300 s, `immaculate` 60 s,
csmith 15 s, the rest 30 s; the three CLI rows, which no lane owns, at the
lane's default 30 s); the fork-only
interfaces (`--cabs-json`, `--call` and the wrapper TUs that mirror it,
`--pp=core` pin derivations, `--batch-alloc-census`) are named as not
applicable. The register (§3) is the exception list; everything else must
agree — semantically through the shared codec, or as the same failure under
the diagnostic projection (the `Time spent` trailer removed; OCaml backtrace
frame positions normalised, [USER 2026-09-17]); a both-sides timeout at the
lane's own bound is counted `matching_incomplete` ([USER 2026-09-17]) — never
agreement, not a failure — while one-sided timeouts and signal kills stay
fatal. This separates "our fork's
behaviour" from "upstream's behaviour": fork regressions and upstream bugs
are attributed, not conflated, and a shared-model change cannot move the
oracle and Lean together unnoticed. **Three engines on one input:**
`test_upstream_oracle.py --with-lean` (Tier C row C5) adds the Lean engine
through the fork's `--cabs-json` bridge exactly as each owning lane runs it
(bridge and driver under the lane's per-test memory cap `CAPPED_TEST` where
that lane caps: libc_exec, immaculate, uri, chvalid) and reports `pristine |
fork | lean` per case — report-only here (Lean vs
fork is gated by its own lanes); at WP-O's landing every one of its 40
Lean≠fork rows was a recorded pin of the owning lane (record §O2).

**Recorded expectations, where the oracle can't reach.** A few legs
are oracle-independent by design: the `tests/bytes` micro-lane
compares against committed upstream `.exec` records, and the
expectation files under `tests/verify`/`tests/corpus` pin previously
recorded verdicts as drift detection *on top of* the live
oracle-differential run.

## 5. The differential lanes

Normative tiers (what runs when) live in `scripts/LADDER.md`. The
lanes, with their recorded states:

| Lane | Corpus | Bar |
|---|---|---|
| `test_exec.sh --check-baseline` | upstream `tests/minimal` | 113 baseline rows: 90 MATCH + 18 UB_MATCH + 5 CERB_SKIP (derived 2026-09-24 at `e9f9d049f`; exclusions are not agreements) |
| `test_exec.sh` (coverage/debug/float baselines) | upstream suites | rc 0 at pinned baselines (recorded DIFFs unchanged) |
| `test_bytes.sh` | `tests/bytes` | 9/9 at committed upstream `.exec` records + 5/5 reject pins (oracle-independent) |
| `test_memory_access.py` | Paired concrete load/store and ND fixtures in `backend/memory_probe/access_probe.ml` and `test/Unit/MemoryAccess.lean` (Tier A row 13) | Primitive diagnostic with independently specified LP64 expectations, not an oracle differential lane: exact whole-transcript match from each engine, empty stderr and exit 0; in-process erasure checks of results and every sequential state field; drain/re-enable controls; all six ND constructors through unchanged `liftND`; eight instrument controls. Builds `Unit.MemoryAccessProofs`, whose kernel erasure theorems prove literal whole-state/result equality for production load/store at arbitrary fuel (since 2026-10-08 the proofs live in the theorem-only seam `CerbMemAccessFacts.lean` as `CerbMem.loadM_erasure`/`CerbMem.storeM_erasure` and their helpers, citable by a consumer; the test restates each under its old name and text, proved by the seam theorem; record `docs/2026-10-08_memory-access-facts-seam-record.md`). The runtime Lean comparator uses the existing type equality, which ignores annotations; the theorem supplies the stronger equality. See the [WP0 record](docs/2026-09-25_sc-wp0-passive-access.md) for scope and cost evidence. |
| `test_address_space.sh` (+ `--selftest`) | `tests/address_space` (6 programs × tops 64/32/8; LADDER Tier A row 12, address-space-bound part two C3/C4/C5, 2026-09-17/18) | both engines at TINY address-space tops (the fork's FORK-ONLY `--address-space-top N`, cerberus-lean's `--address-space-top N` — the parameter of §7 instantiated where the allocator's exhausted regime is reached by ordinary programs): 18/18 LEAN = FORK complete observations through the shared codec (any difference fatal — the S4 class) AND every fork observation = its pinned row in `tests/address_space/expectations.txt`, fail-closed both directions (an unterminated final row is read — audit F3); the corpus holds ONE genuine discriminator of the draft-44 defect, `window-char-int7@32` (the pre-fix ALLOCATION at address 2 executed by the old-body probe, the C observation `Specified(2)` derived from it; fixed: the kill), and `--selftest` rejects that case forged to its pre-fix observation, a missing/truncated file, phantom/duplicate/malformed rows with and without a final newline, accepts the valid file without its final newline, and checks both CLIs refuse `2^64`, `0x40`, `6_4` and `1_8446744073709551615`, and accept `64` and `2^64 − 1` |
| `test_parse.sh` | tests/minimal + tests/ci | Cabs-JSON bridge, 234 files, 100% |
| `test_core.sh` | tests/minimal (+ tests/ci) | Core text parser vs oracle `--pp=core`, 111/111 minimal |
| `test_elab.sh` | elaboration corpus | recorded same/diff state, rc 0 |
| `test_multi_tu.sh` | `tests/multi_tu` | multi-TU linking differential, all entries |
| `test_multi_tu.sh --failure-class-projection tests/multi_tu_tray` | `tests/multi_tu_tray` (7 cross-TU struct-value cases; LADDER Tier A row 6b, 2026-09-15) | the same differential under the LABELLED WEAKER projection `failure-class` — `Symbol(<digits>, ` elided in Error/Undefined payloads only (the engines number symbols differently); 7/7 MATCH (since 2026-10-03, draft 38 reverted: five `mismatched tags` rejections + the two argument-shape `Specified(7)` rows); the ONLY row not on `full`; two rows are OBSERVED MODELLING-LIMIT pins (`tests/multi_tu_tray/README.md`) |
| `test_libc_exec.sh` | `tests/libc_exec` | libc-linked execution at the committed baseline |
| `test_pnvi.sh` (+ `--selftest`) | **TRUST SURFACE** (PNVI arc S4, 2026-10-07, LADDER Tier A row 14): both engines at `--switches=PNVI_ae_udi` over upstream's PNVI litmus suite `tests/pnvi_testsuite` (44, libc mode, exhaustive), the refusal witnesses `tests/pnvi_refusals` (3), the census pKVM allocator drivers (`pkvm-alloc`/`-free`/`-split-merge` in `--first` vs the oracle's one random trace — OUTSIDE CONTRACT §1, their exhaustive sets breach the 4G cap on the oracle; `pkvm-init` exhaustive, its two-execution UB088 set pinned; `page_alloc_census.c` derived at run time, never committed) and `tests/minimal` (113, `--nolibc`) | 164 rows at `tests/pnvi_lane/baseline.txt`, fail-closed both directions with the oracle side hash-pinned per row: 152 AGREE, 3 AGREE-FIRST, 7 registered refusal rows (4 × `REFUSAL R-PNVI-01 ORACLE_CRASH`, `R-PNVI-05 ORACLE_VERDICT`, `R-PNVI-06 ORACLE_CRASH`, `R-PNVI-07 ORACLE_CRASH`), 2 BOTH_FAIL (class (a): `073-exit.libc`/`074-abort.libc`, both "ill-formed program", symbol number differs — as in default mode; BOTH_FAIL admits only one `Error` each equal under the codec's `failure-class` projection, or crash/crash where the oracle's crash is not R-PNVI-named, and pins the Lean side's hash too; an oracle crash an R-PNVI id names requires that refusal); any DIFF/INVALID row, a Lean resource failure where the oracle completes, an empty selection or a missing engine is RED. The oracle's default-mode answer is recorded per row (`default=same|changed`: litmus 27/17, minimal 111/2). `--selftest`: control green; plants RED — Lean ignoring the switch, Lean refusing everything, a refusal turned into an unnamed crash, a refusal mirrored as the oracle's crash text, the oracle's `combine_prov` crash against a Lean `Error`, an Error/Error pair of different failure class, a Lean-side change on a BOTH_FAIL row, the oracle ignoring the switch, a missing engine, an empty selection, and seven doctored baselines (classifier `scripts/pnvi_lane.py`) |
| `test_libxml2_uri.sh` | 16 URIs, 5 TUs, libc | **16/16 byte-identical** lean+libc vs oracle+libc, pinned per-lane expectations |
| `test_libxml2.sh` | libxml2 `chvalid` battery | 4 slices × 1,354 points, byte-equal verdicts (slow tier) |
| `test_cn_coverage.sh` | `deps/cn/tests/cn` | **213/213** at the exact-match baseline (multi-TU drivers, reject lane, manifest bijection) |
| `test_immaculate.sh` | curated pin suite | at baseline (incl. adversarial pins, e.g. the symbol-hash-collision tripwire) |
| `test_gcc_oracle.sh --check-baseline` | tests/minimal + debug + float + immaculate/nolibc + the staged csmith tier (1,997 final-candidate rows: 1,963 + the 34 rows added 2026-09-11/15) | gcc SECOND oracle (oracle-independent): native `gcc -O0` exit status vs the Lean verdict set, `-O2` spot tier, fail-closed triage ledger; at the pinned skip ledger `scripts/gcc_oracle_baseline.txt` (regressions fatal; improvements printed at rc 0). Tier B GATE since 2026-09-02 [USER]. Load caveat: the TIMEOUT-class rows are wall-clock sensitive (TIMEOUT_SECS=30; the slowest csmith rows hand-time at ~17 s on a quiet box, and a busy box — load ≈12 at the 2026-09-02 audit — pushed one over) — a REGRESSION whose only movement is into SKIP_LEAN_TIMEOUT is re-run on a quiet box before it is read as red; no code change. |
| `test_verify.sh` | `tests/verify` + `corpus/` | pin provenance (oracle `--pp=core` re-derivation byte-identical / content-hash) + main-mode differentials + per-function call-point differentials (Lean `--call` vs oracle wrapper TU vs recorded pin) — 127 checks at the Z2 close (record §14) |
| `test_speclab*.sh` (6 scripts) | rendered harness families | five families (scalar/bytes/list/tree/CN-seed): sweeps, deterministic fuzz with byte-wise shrinking, plant tests, pinned-term gates — ~2,000 recorded differential executions, all agreeing |
| `test_csmith_corpus.sh` | 1,669 in-tree csmith programs | classified pinned baseline (sharded; reporting tier full-pass): 0 MISMATCH/DIFF rows; the non-MATCH rows are 499 `CERB_SKIP` (oracle-side) + 9 `TIMEOUT` (derived from `scripts/exec_csmith_corpus_baseline.txt` at `928aa1e76`; the header's per-row narrative is the arc-13 record) |
| `test_ci_sweep.sh` | 2,186-file upstream CI suite | [Repaired candidate measurement](docs/2026-09-06_ci-reporting-results.md): 1,359 matching observations, one UB-location difference, three filesystem refusals, three Lean timeouts and 820 oracle-side non-comparisons. All 15 fresh TSVs/raw records are archived. The default TSVs under `tests/ci_sweep/results/` remain historical (14 from August 22, TCC from September 2); no automatic baseline adoption. |
| `fuzz_csmith.sh` | generated csmith programs | deterministic seeded fuzz kit (reporting tier) |
| `test_upstream_oracle.py` (+ `--plant`) | pristine upstream `b9aeedcb4` vs fork OCaml over the Tier B row-10 corpus (855 cases: the six Tier A exec corpora, both multi-TU roots, 213 CN rows, uri ×2, immaculate, verify + corpus, 3 CLI rows) | **Tier B row 10 GATE**: `passed; {'semantic_agreement': 822, 'matching_failure': 28, 'reviewed_difference': 3, 'interface_agreement': 2}` at WP-O O5 (2026-09-17; before the two rulings: 822 / 11 / 20 / 2); the 3 reviewed rows are the register's (§3); plants: 19 doctored registers rejected at load (incl. untracked-file, out-of-range-line and `..` citations) and the committed register loads, the compare() timeout/kill/stale matrix (unregistered both-sides 124 → `matching_incomplete`; a registered case judged by its row — its fork timing out or a both-sides timeout is `difference`; one-sided and 137 fatal), the projection plants (frame positions only → `matching_failure`; exception text / frame function / non-frame position → `difference`), a fork-verdict mutation and a REAL registered difference with its row withheld → RED |
| `test_upstream_oracle.py --corpus libxml2_chvalid` | pristine vs fork on the 4 chvalid slices (the fork lane's flags and 300 s bound) | **Tier B GATE**: 4/4 `semantic_agreement` (~7 min) |
| `test_upstream_oracle.py --with-lean` | the same corpus, three engines | Tier C row C5, report-only Lean column: 813 agree / 28 difference / 12 both-undecodable / 2 n/a at WP-O, all 40 Lean≠fork rows recorded pins (§4) |
| `test_upstream_oracle.py --corpus ci` / `--corpus csmith --shard K/34` | `tests/ci` (242 cases) / the 1669 staged csmith programs | Tier C reporting rows, rc 0 since [USER 2026-09-17]: ci `passed; {'semantic_agreement': 134, 'matching_incomplete': 2, 'matching_failure': 106}`; csmith shard 1/34 `subset_passed; {'semantic_agreement': 26, 'matching_failure': 3, 'matching_incomplete': 21}`, ~11 min per shard (~6 h for the corpus — never one step) |

Lane semantics worth knowing:

- **Baselines fail closed in both directions** — with one audited,
  deliberate exception. In the oracle-differential exec lanes
  (`test_exec.sh --check-baseline` and friends) a regression fails
  AND an unexplained improvement fails (silent movement is how errors
  hide). The gcc SECOND-oracle lane (`test_gcc_oracle.sh`) fails on
  regressions only and surfaces improvements loudly at rc 0 (by the
  lane's own audited design: its rows classify oracle-INDEPENDENT
  gcc-agreement, where an improvement is a skip-class row starting to
  agree with gcc — e.g. after an unrelated fix lands on mainline —
  and blocking every commit on re-recording that scoreboard would
  make the gate fire on good news; the improvement is still printed,
  and re-records remain dedicated instrument commits). Since
  2026-09-02 [USER] the lane is a Tier B GATE on that asymmetric
  contract: rc must be 0 at slice boundaries / pre-merge. Baseline
  updates are instrument changes: dedicated commit, justification in
  the header.
- **Plant tests.** Gates and lanes are themselves tested by
  deliberate sabotage: break the thing the gate should catch, watch
  it go red, revert, re-verify green. A gate that has never caught a
  plant is treated as untested code.
- **The oracle guards itself.** The single-supply backstop
  (`CERB_FRESH_FLOOR_VIOLATION`, exit 70) makes a mis-built oracle
  refuse loudly rather than compare wrongly, and the lem-sync
  content-hash gate makes a stale generated tree a build failure on
  both the OCaml and Lean sides.
- **The tolerated renumbering class (upstream divergence, declared).**
  The effect-retirement arc replaced the ambient fresh-symbol counter
  with explicit supply threading; the oracle's dynamic draw SEQUENCE
  moved on affected inputs (eager-batch dispersal — statement lists,
  call-argument batches, elaboration prefixes), so the fork's oracle
  Core dumps diverge from un-forked upstream **textually,
  up-to-renaming of symbol ids, on affected inputs** — same term,
  bijectively renamed, verdicts everywhere unmoved. Ruled TOLERATED
  [USER 2026-08-31, re-affirmed over the enlarged class 2026-09-01]
  with a standing operator principle: output depending on symbol
  numbering beyond binding identity is itself a defect (registered
  finding + upstream candidate, never accommodated). The affected pin
  set and its one-time rebaseline: every moved artifact was admitted
  only on machine-checked same-draw-count + permutation-only
  equivalence (`scripts/check_renumber_only.py`, itself plant-tested
  by `scripts/test_renumber_plants.sh`); the enumeration lives in the
  C1/C2 rebaseline commits and `scripts/fork_drift_manifest.txt`'s
  header note. One numbering-dependent output site was found and
  registered (finding C1-F2: a libxml2-uri diagnostic embedding a raw
  symbol id — upstream candidate; the oracle's own diagnostic does
  the same). Records: `docs/2026-08-31_effect-retirement-design.md`
  §3.6/§9, `docs/2026-09-01_C1-adoption-record.md`,
  `docs/2026-09-01_C2-ratchet-record.md`.

**Per-test resource limits.** Execution lanes use `timeout` with
lane-specific bounds. The seven larger-input harnesses listed in
`scripts/LADDER.md`'s resource-cap convention additionally use a per-test
cgroup RESIDENT-memory cap since mem-scale S2 (2026-09-02, Q2 [USER
2026-09-02]):
`scripts/common.sh` `CAPPED_TEST` → `scripts/capped` with
`CERB_TEST_MEM_MAX` (default 4G), replacing the arc-5 `ulimit -v 4000000`
(a virtual-address-space cap that killed Lean at ~1.7 GB RSS while the
oracle ran to 3.1 GB — record `docs/2026-09-01_mem-scale-profile.md` §2).
The cap does not cover every direct invocation in every script; for example,
`test_exec.sh`'s small-corpus helpers use timeout without `CAPPED_TEST`.
The classifying lanes distinguish a low-CPU timeout (`HANG`, S0) from a cap
breach. A positive capped OOM witness, derived from `memory.events oom_kill`,
identifies a breach at any surviving parent status, including 0 and 1.
It produces the lane's KILL class and never observation agreement. Native
GCC's `SKIP_GCC_KILL`/`O2_SKIP_KILL` are explicit applicability exclusions.
A bare 137 without the witness follows the relevant engine/native protocol,
not an assumed OOM classification. Plants:
`scripts/test_hang_plant.sh`, `scripts/test_kill_plant.sh`.

## 6. The build-time gates (`scripts/test_unit.sh`)

Unit executables (parser tests, pretty-printer mirrors vs recorded
OCaml output, fresh-symbol/native-extern probes, and the compile-time
totality/reader-lifting exemplars `effects-proof-test` /
`totality-proof-test`: every fuel'd wrapper FUEL-PARAMETRIC — `@f ⟨n⟩ =
f_lemFuel n` for every `n`, by rfl —, symbolic equations on the total
layout defs, `tagDefs` an honest parameter — properties of the exec cone
as built; and `fuel-exemplar-test`, the FUEL arc's consumer-shaped ∀-fuel
theorem over the shipped pipeline `@drive ⟨fuel⟩` at the ambient
`[LemFuel]` instance, §7), then the gate scripts — all fail-closed:

| Gate | Guarantee |
|---|---|
| sync gate (`tools/check_handwritten_sync.sh`) | every hand-written file byte-identical to its compiled `generated/` copy (the binary corresponds to the sources); copy set enumerated from `lean_frontend/handwritten_copy.manifest`, the same list the Makefile copies from; every `lean_frontend/*.lean` must be listed; empty set = FAIL. Also a precondition of `build_lean` and of the driver-freshness stamp's Lean record/check (2026-09-02 gap: a green stamp over a stale-copy binary) |
| `check_exec_purity.sh` | the execution slice is free of unsanctioned IO/effects |
| `check_theorem_axioms.sh` | **zero `axiom` declarations anywhere** — hand-written census, generated-tree census, and the recursive census of the consumed LemLib package copy (the effect-retirement end state: `runEffectful` is deleted, `declare {lean} effectful` is refused by lem itself); `runEffectful` token-banned (comment-stripped) across all three trees; the `@[implemented_by]`/`unsafe`/`unsafeBaseIO` seam population pinned to `scripts/unsafebaseio_allowlist.txt`'s PIN rows exactly, both directions (a new seam fails naming itself — this bans an axiom-free reintroduction of the effect projection); the boundary-OPAQUE POPULATION pinned exactly-once, both directions (9 registered rows since `bounded_integer` left on 2026-09-28 (10 after enum-state retirement, derived 2026-09-24 at `e9f9d049f`) — the frontend digest boundary and the pure atoms `CerbFuel.fuelExhaustedLoc`/`CerbFail.modelFailStopLoc`; history: 15 from 2026-09-05 when the 11 `CerbGlobal` config/switch opaques became plain `def`s (`docs/2026-09-05_cerbglobal-defs-record.md`), 16 with C-TF1's `modelFailStopLoc`, 12 when the CerbUtils timing/log trio and `CerbMem.beqMemValueSafe` became plain defs (`docs/2026-09-18_seam-hygiene-record.md` §5.4); an unregistered `opaque` fails naming itself); zero `unsafeCast`; exemplar + `driver2` cones free of `sorryAx`/`ofReduce*`/DAEMON; the FUEL arc's contract lemmas (the nine GENERATED `*_lemFuel_zero`, the `CerbND` runner leaves, the fuel-parametricity `rfl`s `@X ⟨n⟩ = X_lemFuel n`) and the exemplar theorems at the exact allowlist; the full exec-entry set (`driver2`, `drive`, `initial_driver_state`, `desugar`, `annotate_program`, `translate`, `link`, `convert_file`, `CerbCall.driveCall`) at the **exact** axiom allowlist `[propext, Classical.choice, Quot.sound]`; non-kernel decision procedures (`native_decide`/`bv_decide`) grep-banned. Source-scan legs are the primary evidence; the `#print axioms` probes are end-to-end spot checks (they underreport across `partial def` boundaries) |
| `check_sorry_token.sh` | zero `sorry` TOKENS in source text — comment- and string-stripped — over `generated/`, the hand-written seams + tests, and the consumed LemLib copy (the axiom gate probes `sorryAx` in cones only; the tree's last `sorry`, cmm_op.lem's target_rep, was closed by the FUEL arc). Empty scan set = FAIL |
| `test_fuel_classifier.sh` | the one FUEL classifier (`scripts/fuel_classify.sh classify_fuel_outcome`) reads its fixture captures correctly: both fuel forms positive; a genuine `Error` kill, a PANIC without the marker, and program stdout carrying the words all negative (§7) |
| `check_no_fuel_numerals.sh` | **a plant-tested SPEEDBUMP against fuel numerals in the Lean text a consumer reasons against** (fuel-parameter arc, 2026-09-04; [USER 2026-09-03] "any and all magic values that are hardcoded and can't be quantified over are definitionally bugs"): seams, `generated/`, `test/`, `speclab/`, `tests/**/*.lean` scanned comment-stripped for the enumerated idiomatic shapes F1–F6 (the deleted `lemDefaultFuel`/`driverFuel`/`ndDefaultFuel`; a global `instance : LemFuel`; a worker at a literal counter — bare, parenthesised, hex, or after a carried instance `f_lemFuel ⟨i⟩ 5`; `LemFuel := ⟨…⟩`/`LemFuel := { fuel := … }`/`LemFuel.mk N`/`LemFuel.mk (…)`; a single-component anonymous constructor led by a numeral `⟨N⟩`/`⟨(N : Nat)⟩`/`⟨0x…⟩`/`⟨10^8⟩`; a fuel-named constant defined as a numeral) — the ONE allowed site is Main.lean's `defaultFuel` (+ the `letI` that consumes it), allowlisted by exact line; vacuity-guarded; its `--selftest` plants 29 shapes red (F1–F6, A1–A3 and the switch-set rule W1, next row) and the unplanted set green on every `test_unit.sh` run. What it does NOT guarantee (pre-merge audit M2): indirection through a non-fuel-named constant (`def budget := 100000000; @f ⟨budget⟩`) and arithmetic spellings not led by a numeral are not regex-closable — the selftest records that gap as a KNOWN GAP line; they are review discipline. The BACKSTOP is the typing, not the grep: every fuel'd function demands a `[LemFuel]` instance, no instance exists in library/generated/seam code, and a measured wrapper carries its sufficiency obligation — a numeral can only enter where a human writes an instance |
| `check_no_fuel_numerals.sh` rule W1 | **a SPEEDBUMP against accidental default `CerbGlobal.Switches` instances** (PNVI arc S1, 2026-10-05; proportionality revision 2026-10-07, record `docs/2026-10-05_pnvi-s1-switch-parameter-record.md` §14): the switch set is the instance-implicit `[CerbGlobal.Switches]`; over the same comment-stripped roots as the fuel rules (seams, `generated/`, `test/`, `speclab/`, `tests/**/*.lean`) an `instance` declaration whose same-line header names `Switches` is RED (plain text pattern); Main.lean's `letI` is not an `instance` declaration; vacuity-guarded (`class Switches` must be seen); `--selftest` plants one in a seam, one in `generated/` and one in a unit test, each RED. What it does NOT guarantee: it is NOT adversarially robust — a header split across lines, an alias, an `extends`, an `instance` attribute, an untyped instance or a raw-string desync passes it, by design. The BACKSTOP is that Main.lean's LOCAL instance (`letI`) wins over any global one for every lane, plus review; a consumer's own instance (outside this repository) is the intended use |
| `check_no_fuel_numerals.sh` rule W2 | **a SPEEDBUMP against production calls of the default-pinned `reconstructValue` wrappers** (PNVI arc S2, 2026-10-07, record `docs/2026-10-07_pnvi-s2-data-shapes-record.md`; design record §B.7 condition (b)): `CerbMem.reconstructValue(_lemFuel)` keep their pre-S2 names and types for the consumer but are pinned at `⟨CerbGlobal.defaultSwitches⟩` (closure fixed, taint dropped; kernel-equal to the pre-S2 text, `test/Unit/ReconstructLegacyTest.lean`); production calls `reconstructValueAbst` with the ambient set. Over the comment-AND-string-stripped seams and `generated/` (the `*_lemMeasureProofs` proof carriers and the theorem-only seam `CerbMemDefaultFacts.lean` excluded — the latter's kernel bridges, PNVI arc S2 review fix F1, NAME the wrappers in their statements), a mention of either old name other than the wrappers' own definition lines (exact-content allowlist, `CerbMem.lean` and its copy) is RED; vacuity-guarded (an allowlisted line must be seen); `--selftest` plants a seam call and a qualified generated-tree call, each RED. What it does NOT guarantee: not adversarially robust — an alias, a call from `test/`/`speclab/`, or a raw-string desync passes it. Not a trust surface: at the default set the two functions agree (kernel), so a stray call moves no lane today; the backstop once a PNVI set is accepted is the PNVI lane (S4) plus review |
| `gen_fuel_parametricity.py --check` | the generated tree's ambient fuel-wrapper SET equals the set pinned by `TotalityProofTest.lean` Part 1's `∀ n, @f ⟨n⟩ = f_lemFuel n` examples, both directions (a new fuel'd function without a pin is RED; `--emit` regenerates the list) — pre-merge audit M1 |
| `check_lakefile_roots.sh` | every `generated/*.lean` — the `_auxiliary` obligation carriers and the `*_lemMeasureProofs` modules included — is a Lake root of the semantics library and every root exists, both directions (lem-lean fuel-measure record §6.4 item 8: an auxiliary module dropped from the roots would silently un-build its obligations); `--selftest` plants a dropped root, a phantom root and an unrooted module |
| `check_exec_totality.sh` | zero `partial` definitions on the execution path (empty allowlist; fuel-totalized recursion with the distinguished fuel-exhaustion outcome, §7) |
| `check_fuel_forms.sh` | **the (A)/(B)/(C) fuel-forms gate** (fuel-parameter arc C2, 2026-09-04; hypotheses C4, 2026-09-05; contract repair P0, 2026-09-05 — `docs/2026-09-05_p0-instruments-record.md` §F2): every fuel'd worker in the compiled environment is MEASURED (obligation of the contract's shape — heads by name, `lemFuel`/`lemHyp` binders, and the ARGUMENT CORRESPONDENCE: the wrapper side is the wrapper on the statement's binders in order, the worker side passes `lemFuel` once at the worker's own `lemFuel` parameter and otherwise only wrapper inputs, and the wrapper's own body unfolds to the worker on those very arguments with the hypothesis' μ at the fuel position; obligation + proof cones ⊆ the standard three), ABSORBING = kill at zero (its `_zero` lemma states THE worker at literal 0 on its own binders and its RHS is the monad's absorbing element; cone ⊆ the standard three; propagation of exhaustion through successor cases is NOT proved — lem-lean TODO row 13), or AMBIENT and then either unreachable from the drive cone (kernel constant closure incl. mutual blocks) or a reviewed row of `scripts/fuel_forms_pending.txt` — both directions; the classifier is `lean_frontend/test/Unit/FuelFormsTool.lean` (runtime `importModules`, no source regex; the fuel binder pinned by its NAME `lemFuel`, the hypothesis-carrying form by its reserved binder `lemHyp` immediately before it, whose type is reported as the `hyp` column); **the gate BUILDS every module it imports before importing it** (hotfix `fix/fuel-forms-carriers` 2026-09-20, finding F-1 — `docs/2026-09-20_fuel-forms-carriers-hotfix-record.md`: `lake build` of the exec entries and every `*_auxiliary`/`*_lemMeasureProofs` carrier, and the selftest's scratch decoys compiled from source — fail-closed, the FAIL naming the module; until then a carrier's `.olean` was imported AS FOUND, and `CerbMem_lemMeasureProofs`' pre-seam-hygiene artifact certified nine obligations vacuously from 2026-09-19 to 2026-09-20). Every MEASURED-under-hypothesis row must equal a row of the REVIEWED register `scripts/fuel_hypotheses.txt` (worker, exact hypothesis text, the frontend invariant with a `.lem:<line>` cite, a reviewer) — both directions, because a CONTRADICTORY hypothesis (`x ≠ x`) passes generation and proves its obligation vacuously (lem-lean measure-hypothesis audit F1). `--selftest` plants six doctored tables, three doctored registers, the F-1 stale-carrier plant P24 (a stale-valid `.olean` over a source that no longer compiles: the gate must FAIL naming the module with the `.olean` untouched) and 15 COMPILED decoys (a same-named theorem of type `True`; the right shape with the wrong worker constant; the real `CerbMem.alignofCtype` obligation under `cty ≠ cty` — MEASURED by shape, RED by the register; a real registered obligation with an EXTRA Prop binder — audit F-A4; the whole-project audit's two decoys verbatim — a `_zero` lemma about `CerbND.runNDFuel` under another worker's name, and `review_shift_lemFuel lemFuel 0 = review_shift x`; wrong fuel position; swapped arguments on either side; a changed measure; a wrapper calling another worker; a premise hidden in the `≤` binder; a well-formed `_zero` positive control; a `_zero` at a term; a `_zero` at fuel 1) — each rejected with its own message; MEASURED/ABSORBING are decided by the fully-qualified name AND the statement's shape against the worker and wrapper definitions (§7, the (A)/(B)/(C) table) |
| lem-sync gate | generated trees content-in-sync with the `.lem` sources (stamped; also wired into the dune graph for the libc `.co` artifacts) |
| `check_fork_drift.sh` | the fork's oracle-side surface equals a reviewed manifest, and generated-OCaml fork-vs-upstream deltas match pinned hashes |
| `check_pin_sites.sh` | the lem-lean pin is ONE value at every site that names it — the manifest `lem-pin`, the Lake `LemLib` rev, the three lake-manifests (`rev` + `inputRev`) and the README's newcomer `opam pin` command (fresh-clone finding 2026-09-25; 8 plants) |
| `check_fixture_freeze.sh` | the `corpus/` differential-fixture set matches its hash manifest exactly (additions included) |
| `check_failure_reach.sh` | **the failure-reach register gate** (fuel-pending close-out 2026-09-08 — option C of the pure-failure reachability census `docs/2026-09-07_pure-failure-reachability-census.md`; the TRIPWIRE the parked twin design `docs/2026-09-07_pure-failure-correspondence-design.md` names): rebuilds the one-module declaration-dependency instrument `tests/failure-probes/FailureReach.lean` (fresh scratch Lake package, ~6 s), takes the lexical census (`scripts/failure_census.py`) and requires every PURE `failwithI`/`panic!` site of the exec dependency closure (237) + every pure site with an unresolved kernel owner (2) to equal a row of `scripts/failure_reach_register.txt` — same position class (the census's token-level classifier `scripts/failure_position.py`), the census's reviewed reach class (173 UNREACHABLE-BY-INVARIANT / 44 REACHABLE / 22 UNKNOWN over 239 rows, the 2 unresolved rows among the UNKNOWN; counts as of 2026-10-07, PNVI arc S4 — the PNVI refusal rows re-reviewed once the switch became accepted — the gate's OK line is authoritative), sealed rows — both directions, matched on the key file/owner/token/message (the first 60 whitespace-collapsed chars after the token; inside a group of sites sharing that key the window is lengthened to the minimum that tells them apart, and a group identical even on the full recorded window is a loud FAIL — 2026-10-04, `docs/2026-10-04_failure-reach-key-groups-record.md`); RED naming the rows on a NEW site, a stale row, a moved position class, a DISCARDABLE generated let-binding (the F1 shape: a dead binding of a failure — today 0) or an unsealed class edit. Reach classes are reviewed claims (an invariant NAME with a cite, or a witness under `tests/failure-probes/reach/`), not theorems; the closure is a kernel constant-dependency closure, not a path. `--selftest` plants on scratch copies (a new site in a generated exec-closure definition, a dead let, an unsealed class edit, a phantom row, an edited tally, mis-shaped `lem_if`/`lemSeq` heads (P6/P7), and P8: two same-owner rows' reach classes swapped together with their seals — the pre-merge audit A3 hole, now RED SEAL MISMATCH) plus classifier witnesses C1-C7 and the key-group witness K1 |
| `test_renumber_plants.sh` | the rebaseline-admission instrument (`check_renumber_only.py`) refuses what it must: committed adversarial pairs (string-content/comment-boundary holes + count/token/order plants) fail, positive controls admit with their declared class |
| `check_runtime_resolution.sh --selftest` | the driver's runtime is the oracle's (`--runtime DIR` / `CERB_INSTALL_PREFIX`), never the working directory, and a missing runtime or a suffix-library-but-not-exact location refuses (bug hunt BUG-2/BUG-3, 2026-09-29; §3(c)); plants: a runtime-ignoring stub and a refuse-everything stub must fail it |
| `check_cabs_json_utf8.sh --selftest` | a non-UTF-8 Cabs JSON (a raw byte ≥ 0x80 in a file name or attribute string) is refused with the attributed message instead of an uncaught exception, and ASCII controls agree with the oracle (bug hunt BUG-6/K-5, 2026-09-29; §3(c)); plants: a pre-fix uncaught-exception stub and a refuse-everything stub must fail it |
| `check_asm_refusal.sh --selftest` | inline assembly is refused, never erased: 4 asm statements (basic, extended, `asm goto`, in a never-called function) are refused by the oracle and by Lean with the attributed desugar message at the asm location, 3 declarator asm labels are refused by the shared parser for `--exec` and `--cabs-json` (no Cabs JSON), and 2 controls (asm-free; asm only in a comment and a string) agree with the oracle (contract D9, 2026-10-05; §3(c)); plants: a pre-fix erasing oracle (strips the asm, both engines then run it), a Lean-only erasing stub and a refuse-everything pair must fail it |
| `check_libc_float_literals.py --selftest` + check | every float literal of the pinned `tests/libc/libc.core` equals the reviewed register `scripts/libc_float_literals.txt`, as multisets, both directions; a 12-significant-digit literal may not be registered exact (named deviation N3); 8 plants |

Certification-integrity rules ride the gates: validation of
build-rule-affecting changes is cache-disabled from re-derived
generated trees; audits check the artifact the consumer actually
loads (the libc.co staging pattern); quoted outputs are verbatim.

## 7. Fuel — the parameter, the exhaustion outcome, the (A)/(B)/(C) forms

**Fuel is a PARAMETER of the semantics; fuel exhaustion is a typed,
distinguished outcome.** Every fuel'd generated function (67 sentinel
declares at the C1 slice; the `declare {lean} fuel val f = \`sentinel\``
form) is a total worker `f_lemFuel (lemFuel : Nat) …` whose wrapper
starts the counter from the LemLib class instance `[LemFuel]` (`def f
[LemFuel] := f_lemFuel LemFuel.fuel`) — or, for a `declare {lean}
fuel_measure val f = \`lemSize x\`` function, from the backend-derived
structural size of its argument (`def ctypeEqual (c c0) := ctypeEqual_lemFuel
(ctype.lemSize c) c c0`: no fuel binder, kernel-computable, with the
generated sufficiency obligation `ctypeEqual_measure_sufficient` proved
in the hand-written `Ctype_lemMeasureProofs.lean`; three such at C1:
`ctypeEqual`, `eq_core_base_type`, `fake_mem_value_eq`, the `Eq`
instance methods) — and every definition that
reaches one takes the same instance-implicit binder (the backend's fuel
lifting; the hand-written seams that reach fuel — the `CerbMem` layout
and (de)serialisation entries, `runND`/`runND1`/`runND1Trace`,
`CerbCall.driveCall`, `Main.runPipeline` — take it too, and the 19
`mem.lem` reps whose implementations read it are `declare {lean}
fuel_consumer`). So the whole run has ONE fuel, instantiated exactly
once at the executable's entry: `cerberus-lean … --fuel N` (default
`Main.lean` `defaultFuel` = 10^8, THE ONLY fuel numeral permitted in
the repository's Lean text — `check_no_fuel_numerals.sh`; 0 or a
non-numeral is refused, exit 2), and a theorem quantifies over it
(`∀ n, @f ⟨n⟩ = f_lemFuel n` by rfl is the parametricity pin for every
wrapper — `totality-proof-test`, `CerbND.*_wrapper_defeq`; the
consumer's hypotheses become `∀ [LemFuel], potential e ≤ LemFuel.fuel →
…`). This is the fuel-parameter arc ([USER 2026-09-03]: fuel "is an
execution parameter that 'doesn't matter' … a parameter which can be
chosen as 10^8 or any other value when calling the interpreter"; "Any
and all magic values that are hardcoded and can't be quantified over
are definitionally bugs"); the former constants `CerbFuel.driverFuel`
(10^8, the driver family), `CerbND.ndDefaultFuel` and LemLib's
`lemDefaultFuel` (10^6, everything else) and the per-declaration numeric
budget form are DELETED (lem-lean
`doc/lean-backend/2026-09-03_fuel-parameter-design.md` R1–R3;
`docs/2026-09-04_fuel-parameter-C1-record.md`). Every fuel'd callee
starts from the FULL ambient, never from its caller's remaining
counter.

The exhaustion outcome: for the ND monad's fueled workers (the driver
loop family, the memory-model ND workers, and the `CerbND` runners) the
fuel-zero arm is `NDkilled CerbND.fuelExhaustedKill` = `Error0
CerbFuel.fuelExhaustedLoc "lem: fuel exhausted"`, where
`fuelExhaustedLoc` is a pure, kernel-checked `opaque` constant on the
boundary-opaque census (present exactly once; no native binding). Every
proof is uniform in the opaque atom; the sentinel is a fresh location
for every provable statement — a theorem "every outcome is `Killed _
fuelExhaustedKill` or good" holds under the reading where the atom is a
location no model term denotes, and a program that genuinely kills makes
it unprovable, not false; so no distinctness lemma is needed (corollary:
no `.lem` term, Core text, or JSON input can denote the atom). The
`_zero` lemmas are GENERATED by lem beside each wrapper
(`f_lemFuel_zero … : f_lemFuel 0 … = <sentinel> := rfl`; the nine
ND-typed ones are gate-probed).

**The (A)/(B)/(C) classification (C2, 2026-09-04; counts as of the
parser-progress-measure slice, 2026-09-15 — `docs/2026-09-11_parser-progress-measure-record.md`; before it the fuel-pending close-out, 2026-09-08 — `docs/2026-09-08_fuel-pending-closeout-record.md`) — the consumer's truth condition, gate-checked by
`scripts/check_fuel_forms.sh` from the kernel environment
(`lean_frontend/test/Unit/FuelFormsTool.lean`; records
`docs/2026-09-04_fuel-parameter-C2-record.md`,
`docs/2026-09-05_fuel-parameter-C3-record.md`,
`docs/2026-09-05_fuel-parameter-C4-record.md`):** every fuel'd worker
(81: 67 generated + 14 hand-written) is

| form | count | meaning | for the consumer |
|---|---|---|---|
| (A) MEASURED | 63 (13 under a hypothesis) | `def f xs := f_lemFuel (<data measure>) xs`; theorem `f_measure_sufficient : [H →] measure ≤ n → f_lemFuel n xs = f xs`, cone ⊆ the standard three (53 generated + 10 `CerbMem` seams by hand: `typeofMval`/`unqualifyAndUnatomic`/`memValueToBytes` unconditional, and — C4 — the layout oracle `sizeofCtype`/`alignofCtype`/`memberAlign`/`offsetsofMembers`/`offsetsof` and `reconstructValue` — since PNVI arc S2 (2026-10-07) also the full reconstruction `reconstructValueAbst` it projects, with its own obligation and register row — under `CerbTagsWf.Acyclic ambient` (`AcyclicPair ambient tagDefs` for `offsetsof`): a rank on tag-environment entries descends along every by-VALUE reference — a theorem hypothesis, not an established frontend invariant, `scripts/fuel_hypotheses.txt`; measures `CerbTagsWf.envBound` & co. = structural size + the environment's weight; plus `showNonNegativeWithBasis_aux` under `2 ≤ b` (lem `assuming`, the first generated hypothesis-carrying row); and — the fuel-pending close-out, 2026-09-08 — the three always-on-path sentinels `hack` (`lemSize pexpr1` under `CerbCoreShape.IsValuePexpr pexpr1`), `to_pure` (`lemSize g` under `CerbCoreShape.IsPureExpr g`) and `to_pures` (`List.length l + 1` under `CerbCoreShape.AllPureExprs l`): the arena is `Epure` of a `PEval` value after `prepare_exit` (driver.lem:1309-1316), the only exit of `driver2`, so each needs ONE hop at `finalize`/`driver_globals`; `CerbCoreShape.lean` is the shape vocabulary, `Driver_lemMeasureProofs.lean` / `Core_aux_lemMeasureProofs.lean` the proofs; and — the parser-progress-measure slice, 2026-09-15 — the two parser workers `many_run`/`many1_run` (`2 * List.length cs + 2` / `+ 1` under `CerbParserProgress.Consumes p`: every result of `parse p cs` leaves a strictly shorter rest; `many`/`many1` were restated as input-indexed recursion so the input IS a parameter — the same parsers on every input, kernel-related to the old workers in `test/Unit/ManyRestatementTest.lean`; the hypothesis is a THEOREM at every printf call site, `CerbParserProgress.callSites_consume`; proofs `Monadic_parsing_lemMeasureProofs.lean`). The six point-free `function` tails joined at C3 — lem d4ba548 hoists the scrutinee into the head as `lemTail`; the two mutual blocks share one counter, so each member's measure bounds the whole block) | fuel-FREE: no `[LemFuel]` in statements (four keep the binder for an ambient callee: `memValueFromValue`, `step_eval_pexpr`, `easy_update_mem_value_aux`, `memcmp_load_aux`; `CerbMem.memValueToBytes` lost its binder at C4 with the layout oracle it read) |
| (B) ABSORBING ("kill at zero") | 13 | `f_lemFuel_zero` states `f_lemFuel 0 xs…` — the worker itself, at literal 0, on the lemma's own binders (P0 gate check) — and its RHS is the monad's absorbing element at the fuel atom: the ND kill (`nd_bind`, `liftND`, `liftAction`, `driver2`, `drive_nonmemory_steps_aux2`, `print_eval_conv_aux`, `load_character_array_aux`), `Result (Error fuelExhaustedLoc fuelExhaustedMsg)` in the undefined monad (`full_eval_pexpr`, `eval_pexpr_aux2`, `eval_pexpr_aux_broken`), the runners' `Killed` | at fuel 0 the result IS the kill; that exhaustion at a deeper fuel propagates through every successor case ("never continues as a value") is NOT proved by this gate — it is lem-lean TODO row 13 (fuel monotonicity), pending |
| (C) OUTSIDE EXEC DEPENDENCY CLOSURE | 5 ambient | not in the kernel constant closure of `drive`/`initial_driver_state`/the runners/`CerbCall.driveCall` (mutual blocks closed): the DEFACTO memory model's `mkUnspec`/`simplify_integer_value_base` (not the wired model), `zeros_aux` (front end), `list_unfoldr_aux`, one `CerbMem` reference form (`memValueToBytes_append_lemFuel`; the reconstruct reference form was retired to `test/Unit/ReconstructLegacyTest.lean` in PNVI arc S2) | absent from this dependency closure; no general API unreachability claim |
| PENDING | 0 | reachable AND ambient, each a reviewed row of `scripts/fuel_forms_pending.txt` with its reason — the register is EMPTY (header-only; the gate accepts an empty register and any new reachable ambient worker is RED). History: the 6 point-free tails left the register at C3, the 6 `CerbMem` layout rows and `showNonNegativeWithBasis_aux` at C4, `hack`/`to_pure`/`to_pures` at the 2026-09-08 close-out, and the `ctype_aux` compatibility trio `are_compatible_aux`/`are_compatible_params_aux0`/`are_compatible_params0` on 2026-09-10 — not by a hypothesis but by the shared-model change that makes the block total (a path-local assumed-compatible list of tag pairs, C11 §6.2.7#1's device; `docs/2026-09-10_are-compatible-assumed-set-record.md`, upstream-tray draft 37), measured WITHOUT a hypothesis (`CerbCtypeMeasure`), and `many`/`many1` on 2026-09-15 — by the input-indexed restatement (`many_run`/`many1_run` on the input; `docs/2026-09-11_parser-progress-measure-record.md`, upstream-tray draft 43), measured under `CerbParserProgress.Consumes p`; exhaustion = the opaque panicking sentinel | (none left; statements about a future pending worker would need a depth hypothesis, C2 record §9) |

The fuel-measure-cost change (Codex D3 `6ce040f06`, landed 2026-09-08 as a
named structural measure — [record](docs/2026-09-07_fuel-measure-cost-record.md)
§D3 and "Landing improvements") keeps this census and all obligation shapes.
`get_ctx` and `get_ctx_unseq_aux` now instantiate their shared counter with
the proved conservative context CALL-DEPTH bound `CerbCoreMeasure.getCtxBound`
on the expression/list state (`Sum.inl g` / `Sum.inr lemTail`) instead of the
whole-arena `lemSize + 1`. The bound is an ordinary structural definition
(`lean_frontend/CerbCoreMeasure.lean`, imported by the generated
`Core_reduction` via `declare {lean} extra_import`; no `WellFounded.fix`, no
erased rank, no macro — the qualified-helper form lem's FM-free validator was
written to accept): one unit per worker frame plus the maximum over the
possible children (`Ewseq`/`Esseq` left operand, `Ebound`/`Eannot` body,
`Eunseq` operand list; a nonempty list its head and tail). The two
sufficiency cones and the seam's lemmas are within the standard three, and
two kernel-checked equalities relate the previous measures' worker results to
the new wrappers. The six environment measures and their acyclicity
hypotheses are unchanged. No frontend acyclicity invariant is newly claimed.

The gate is RED on a NEW reachable ambient worker and on a stale register
row (both directions), on a same-named obligation whose TYPE is not the
contract's shape, on a measured cone outside the standard three, on a
truncated table or a non-partitioning form count, and — C4 — on a worker
MEASURED under a hypothesis with no row of the reviewed register
`scripts/fuel_hypotheses.txt` naming that exact hypothesis (or a stale or
cite-less register row), on an obligation with a binder that is neither
reserved nor a wrapper argument (audit F-A4), and — P0 2026-09-05 — on an
obligation whose argument correspondence fails (a literal or foreign term on
the worker side, `lemFuel` at the wrong position, arguments swapped on either
side, a lower bound that is not the wrapper's measure, a wrapper that does
not call the worker) or a `_zero` lemma not about the worker at literal 0 on
its own binders, or with a cone outside the standard three; `--selftest`
plants six doctored tables, three doctored registers and 15 compiled decoys
(the table row of each carries its own rejection message). The ambient
panic form: exit 134, `lem: fuel exhausted` on stderr — at a tiny fuel
the FRONT END's pure workers exhaust first (measured at C1: `--fuel 1`
on `tests/minimal/001-return-literal.c` is the panic form).
The classifying lanes (`test_exec.sh` and its csmith wrapper,
`test_gcc_oracle.sh`, `test_ci_sweep.sh`, `test_cn_coverage.sh`,
`tests/mem-scale-probes/measure.sh`) assign the FUEL class to both
forms by the printed message (fail-noisy, never agreement;
reporting-only, no soundness rests on it); the byte-compare lanes
(`test_libc_exec.sh`, `test_multi_tu.sh`, `test_verify.sh`,
`test_immaculate.sh`, `test_libxml2_uri.sh`, `test_bytes.sh`) report
DIFF/FAIL; `test_fuel_plant.sh` runs the real driver at `--fuel 1`
(FUEL) and at the default (MATCH). The harness default 10^8 is
unreachable inside any gate lane's timeout (15-30 s ⇒ ≤ 7×10^6 fuel per
invocation); it is exercised only by `measure.sh` (600 s) and unbounded
single probes. Why a fuel row is an accepted Lean-vs-oracle discrepancy
at all — [USER 2026-09-03]: "fuel is a reasonable exception because we
could always just run the semantics with more fuel." That ruling's
frame is §0/§1 of this document: every Lean-vs-oracle execution
discrepancy is a bug; fuel exhaustion is accepted under class (b) with
the rationale that the bound is a PARAMETER of the port rather than a
fixed semantic limit. General sufficient-fuel completion and observation
agreement are not established; they require explicit domain, failure,
state and runtime assumptions. Increasing fuel does not repair known
non-fuel discrepancies, such as the libc UB-location loss in the
[2026-09-06 CI record](docs/2026-09-06_ci-reporting-results.md).
Fuel STABILITY is delivered for the ND infrastructure only (2026-09-09,
`CerbNDFuelProofs.lean`, record `docs/2026-09-08_nd-fuel-stability-record.md`):
for the three runners `runNDFuel`/`runND1Fuel`/`runND1TraceFuel` and for
`nd_bind`/`liftND`/`liftAction`, if the earlier observation contains no
fuel-exhaustion outcome (`NoFuel`), every larger budget yields the SAME
observation — exact order, multiplicity, failure reasons, states and trace
labels — with operands fixed and worker/observer budgets quantified
independently. Fuel monotonicity for the seven driver-level absorbing
workers (`driver2`, `full_eval_pexpr`, …) and whole-interpreter stability
under a larger AMBIENT fuel captured inside operands are NOT provided: they
depend on how each body consumes exhaustion (lem-lean fuel-parameter record
§5) and need composition proofs. A FUEL row is never counted as agreement.
Records: `docs/2026-09-02_fuel-arc-design.md`,
`docs/2026-09-04_fuel-parameter-C1-record.md`.
**The address-space top is a parameter too** (address-space-bound slice,
2026-09-17; [USER 2026-09-16] *"the semantics should be quantified over such
bounds"*; record `docs/2026-09-17_address-space-bound-part-two-record.md`,
design DESIGN.md §4). The concrete allocator's initial cursor — upstream's
`last_address = 0xFFFFFFFFFFFF` = 281474976710655 — is no longer a literal in
`memory/concrete/impl_mem.ml`/`memory/vip/impl_mem.ml` or a field default in
`CerbMem.lean`: `Mem.initial_mem_state : integer -> mem_state`
(`CerbMem.initialMemState top`) takes it, `initial_driver_state sup top digest file fs`
and `Cabs_to_ail.desugar sup top …` (the desugar state carries it for the
const-expr mini-run's own driver state) thread it, and each executable
instantiates it ONCE at its entry: `cerberus-lean … --address-space-top N`
(default `Main.lean` `defaultAddressSpaceTop`, THE ONLY address-space numeral
permitted in the repository's Lean text — `check_no_fuel_numerals.sh`'s A1–A3
shapes, plant-tested; 0 or a non-numeral is refused, exit 2) and the fork
oracle's `Driver_ocaml.address_space_top_default` (the fork-only
`--address-space-top N` flag of C3; pristine upstream has no such parameter).
Matched mode passes the flag on neither engine, so every baseline row is
unmoved; the tests choose their own values (`MonadicFailstop.testAddressSpaceTop`,
the speclab gates' `gateAddressSpaceTop`, …) as the ruling allows. **The DOMAIN**
(C4, 2026-09-18 — the pre-merge audit and the consumer's review
`cerberus-sl/docs/2026-09-18_s3-checkpoint-review.md`: their invariant
`MemWF.la_wf` needs `lastAddress ≤ 2^64` and `la_pos` positivity): an address
must fit an LP64 pointer, so `0 < top < 2^64` — `2^(8 · sizeof_pointer)`,
derived on both engines from the implementation's `sizeof_pointer = 8`
(`CerberusImpl.sizeof_pointer`, `ocaml_implementation.ml DefaultImpl`), and
both CLIs refuse anything else — non-decimal spellings included — with the
same sentence (`the address-space top must fit an LP64 pointer: 0 < top <
2^64`; only the exit code is the CLI library's). **The shared grammar** (C5,
re-review R1; [AGENT orchestrator], mirror doctrine): the flag's argument is
"nonempty ASCII decimal digits, `0 < value < 2^64`" on BOTH engines — Lean
validates the digits BEFORE `String.toNat?` (which alone accepts `6_4`), the
fork's converter is digit-only; `18446744073709551615` (= 2^64 − 1) is the
last accepted value on both (LADDER A12 plants P12–P14). **Non-default values are
outside the mirroring promise** (2026-10-03; CONTRACT §2): the parameter is a
DELIBERATE lift for proof use — [USER 2026-10-03] "we specifically want to lift
the address-space-top restriction for the sake of treating cerberus as a proof
artifact. Agree on your recommendations with that framing (we shouldn't revert
work that allows the iris reasoning to work properly)" — and only its default
mirrors upstream (`impl_mem.ml` `last_address= Z.of_int 0xFFFFFFFFFFFF; (* TODO:
this is a random impl-def choice *)`). The A12 lane's Lean = fork agreement at
tiny tops is evidence about the fork's own extension, not upstream agreement;
at tops ≥ 2^62 the fork oracle's `Z.to_int` on object sizes would raise where
Lean computes (total-arith record §2.3 O-1). The fork's symbolic and CHERI
memory models accept the fork-only flag and ignore it
(`memory/symbolic/impl_mem.ml` and `memory/cheri-coq/impl_mem.ml`
`initial_mem_state (_address_space_top: Z.t)`); those models are fork-oracle
only (separate executables: `cerberus-cheri`; the symbolic driver is commented
out of `backend/driver/dune`) — cerberus-lean has the concrete model alone, and
any model-selecting flag is an unknown flag, refused (Z-24). A consumer theorem quantifies
`∀ top` under that domain, alongside `∀ fuel`; the driver's SETUP needs
`8 ≤ top` — its errno `int` (4 bytes, align 4) is the first object, and a
smaller top kills out of memory BEFORE `main` runs (the consumer review's
second fact: a small top OOMs on errno before the program's own state exists),
so a startup theorem carries that room hypothesis while a client-facing
result may fold the OOM into its admitted outcomes. The exemplar's theorem IS
that startup theorem in miniature: `FuelExemplar.exemplar_certified_shipped_forall
(fuel : Nat) (top : Int) (h : 8 ≤ top)` — ∀ fuel, ∀ top with room for errno —
by the symbolic errno lemma `errnoAction_active` (C4, 2026-09-18; the errno
allocation and store discharged from `8 ≤ top` by the allocator's arithmetic and
the store's guards, the post-setup state `S₁ top` stated explicitly), axioms the
standard trio. A tiny top is a legitimate instance. The allocator's two kills, stated
exactly: it kills when `cursor − size < 0` (`CerbMem.allocator_below_request_kills`,
remedy 1 in kernel terms) and when the aligned-down candidate address is `≤ 0`
(cursor 4, request 4, align 4 kills with cursor = request; cursor 5 kills too);
an ACTIVE result satisfies `CerbMem.allocator_active_sound` — a NECESSARY
condition on active allocations (aligned, positive, ending at or below the
cursor), not a characterisation of failure.

## 8. How often

Per `scripts/LADDER.md`: Tier A (every commit) = `test_unit.sh` +
the exec baselines + bytes + libc_exec + multi_tu + parse + core +
elab + the uri gate + cn_coverage; Tier B (slice boundaries,
pre-merge) adds the full libxml2 battery, the tests/ci suites,
`test_verify.sh`, `test_immaculate.sh`, the speclab gate lanes, the
gcc second-oracle lane (`test_gcc_oracle.sh --check-baseline` — a
GATE since 2026-09-02 [USER]), the pristine-oracle lane (row 10, widened
2026-09-16, + its chvalid row 12) and the harness plant batteries
(`test_hang_plant.sh`, `test_kill_plant.sh`; `test_renumber_plants.sh`
rides `test_unit.sh`); Tier C are the committed reporting
instruments (`test_ci_sweep.sh`, the csmith full pass, fuzz). Probe
corpora that are neither gates nor scoreboards (`tests/parity-probes`,
`tests/mem-scale-probes` incl. its `micro/` Lake package,
`tests/csmith_findings`) are enumerated in LADDER.md as instruments.
`scripts/release.py` reads executable membership from `scripts/LADDER.md`:
`--mode fast` selects Tier A, and `--mode full` selects A+B. It records source,
artifact and external-input identities, complete lane logs and completion.
A selected subset is not a complete release. Each command runs in a fresh,
owned cgroup v2 subtree; nested caps stay inside it. Timeout, interruption,
surviving descendants or missing final artifacts prevent certification. A
pipe guardian cleans the subtree after supervisor death. This requires a
writable delegated cgroup v2 parent with memory enabled and `cgroup.kill`;
unavailable containment fails before dispatch. The repaired candidate's
[fresh document review](docs/2026-09-06_validation-foundations-document-review.md)
is complete; its corrections require a renewed landing decision because
the user's merge authorization was conditional on no major findings.

## 9. What this does and does not establish

Differential testing samples behaviour; it never proves equivalence.
The claims this validation surface supports are exactly:

1. The measured MATCH/UB_MATCH rows agree under each lane's documented
   observation comparison. The shared decoder covers the former value-only
   batch extractors; narrower reference/model projections remain explicit
   in its matrix. Baseline stability additionally checks recorded exclusions,
   inherited failures, known differences and open bugs. Those categories,
   including UB_DIFF, refusal, fuel and timeout, never count as agreement.
   The [delivery record](docs/2026-09-06_validation-foundations-delivery.md)
   identifies the historical measurements; the repair record identifies the
   candidate's reruns. No csmith campaign was run by this charter.
2. The artifact you tested is the artifact you built: sync,
   lem-sync, staging, and fork-drift gates close the
   "verified-vs-loaded" gaps.
3. The execution path is total, effect-honest, and axiom-clean as a
   Lean artifact (§6) — properties of this port, checked by the
   build, independent of the oracle.
4. **The customer contract (effect retirement, universal form) is
   MET, with the §6 gate as its standing enforcement**: every
   constant elaborated from this repository and from LemLib has axiom
   cone ⊆ `[propext, Classical.choice, Quot.sound]`. This is derived,
   not sampled — zero `axiom` declarations exist anywhere on the
   scanned surface (hand-written, generated, and the LemLib package,
   recursively), and the standing bans exclude the tactic-introduced
   axioms — with the exec-entry probes as end-to-end spot checks.
   `runEffectful` does not exist under any name; reintroducing
   `declare {lean} effectful` is a lem generation-time refusal.
   (Charter: `docs/2026-08-31_effect-retirement-design.md` §1.3.)
5. Fuel is a quantified parameter (§7). Wrapper equations, measured
   sufficiency lemmas and zero-case lemmas establish their stated local
   contracts; the ND runners and `nd_bind`/`liftND`/`liftAction` carry
   kernel-checked completed-observation STABILITY theorems (§7). General
   completion, driver-level propagation and whole-interpreter stability
   remain obligations under explicit hypotheses; these local results do not
   establish universal agreement with oracle-terminating runs.

Sampling has blind spots, and they are closed by dated records, never
quietly: literal-level adversarial inputs (long hexadecimal mantissas, raw
high bytes in string literals and character constants) were untested before
2026-09-11 — `docs/2026-09-11_semantics-audit-repairs-record.md` (findings
3/4 of the whole-project semantics audit; the corpora had one 21-character
hexadecimal literal and no executed non-ASCII literal).

What remains on the trust boundary: the OCaml oracle itself (and
upstream's correctness — the tray is the log of where we believe it is
wrong), the C parser (shared, upstream), the Lem compiler and its Lean
backend (attacked structurally by the shared model + the mirror
discipline + these differentials), the Lean toolchain, and the RUNTIME
seams — not axioms, enumerated and machine-pinned
(`scripts/unsafebaseio_allowlist.txt`, gate-enforced both directions),
each with its ruled classification [USER 2026-08-31] (`CerbGlobal`
left the list 2026-09-05, see below):

- the FRONTEND digest boundary (`CerberusFresh.digest`/`forceIO`/`md5Hex`) —
  the run's minting digest is explicit run-state data since D-S 2026-09-22
  (`core_run_state.sym_digest`, seeded from the last program TU; empty
  without one). Frontend `Symbol.fresh*` reads and the const-expr mini-run
  seed remain this seam: kernel-checked opaques with native `@[implemented_by]`/`@[extern]`
  bindings (the C2 conversion; nothing postulated, no proof can
  unfold them);
- (`CerbMem.beqMemValueSafe` — LEFT the boundary 2026-09-19, seam-hygiene
  H3: `BEq MemValue` is the structural, kernel-transparent
  `CerbMem.beqMemValue`; the retired unsafe impl's agreement with it was
  witnessed on 23 pinned pairs (`docs/2026-09-18_seam-hygiene-record.md`
  §5.3), so the supported profile's VF-3 correspondence obligation for this
  row is CLOSED — the row is history;)
- (`CerbGlobal` config/switch surface — LEFT the boundary 2026-09-05:
  the refs were never written, so the eleven reads are now plain `def`s
  of the driver's default configuration, kernel-transparent, with `rfl`
  lemmas (`docs/2026-09-05_cerbglobal-defs-record.md`); the switch
  FEATURE stays class (c) — flags refused, plumbing not wanted ([USER
  2026-09-03] Q7, §3). Step 2 — the configuration as a reader-lifted
  parameter — is a separate slice; `using_concurrency`'s step 2 belongs
  to the concurrency feature branch;)
- `CerberusImpl`'s enum registry — LEFT the boundary 2026-09-20
  (program-data parameters E-A, `docs/2026-09-20_program-data-parameters-
  EA-DA-record.md`): the enum's compatible type is program data (the lem
  reader `enum_definitions`); no registry, no opaque, no `implemented_by`
  remains in `CerberusImpl.lean`. The FRONTEND digest seam stays on this
  list; execution minting uses the explicit D-S run-state digest;
- `CerbUtils.boundedIntegerImpl` stub — LEFT the boundary 2026-09-28
  (contract enforcement, served-surface audit P3-1): it returned `lo`;
  `bounded_integer` is now a plain def failing loudly (the live stepper
  fails `any_bounded_int` in both engines). The timing/log refs became
  transparent value identities at seam-hygiene H3 (2026-09-19);
- LemLib's `failwithIImpl`/`fuelExhaustedWithImpl` panic bindings
  (runtime behavior of the axiom-free failure/fuel constants);
- LemLib's `lemSeqImpl` — TEMPORARY (added 2026-09-30 with the lem re-pin to
  `77ad4fa`, `docs/2026-09-30_lem-repin-77ad4fa-record.md`). It is the native
  body of the TRANSPARENT `lemSeq a b := b ()` that lem emits for
  `let _ = e1 in e2` and unused `let`s (B15/B15b): the kernel and every proof
  see `b ()`; at run time `a ()` is forced first, mirroring OCaml's strict
  `let`. A failure or non-termination in the discarded `a` is therefore
  visible at run time and invisible to the logic. Of Cerberus's 268 generated sites,
  all but one are debug `print_debug_pure`/`warn` calls (no-op twins); the exception is `driver2`'s `_non_blocked_th_sts` (`Driver.lean:433`, `driver.lem:1379`), which runs `step_ctx` (four failure sites of UNKNOWN reach) on every driver iteration. Lean's compiler used to drop that work; it now runs as in OCaml (no lane moved; pre-merge audit F1). Ruling D1 [USER 2026-09-30] "D1: agree" (D1(a): temporary, not
  permanent; relayed in lem-lean `doc/lean-backend/2026-09-28_linksem-findings.md`
  "Native seams"); named mover: lem-lean TODO item 24, the failure-monad
  translation, which deletes it. (D1(b) removed LemLib's `@[extern]`
  `lemSetExitOnPanic`; it never reached this list.)

Separately from the runtime seams, the boundary-opaque census (the axiom
gate's exactly-once population, 10 rows at `e9f9d049f`, derived 2026-09-24) carries two PURE
value-carrying opaques with no native binding: `CerbFuel.fuelExhaustedLoc`
(§7) and `CerbFail.modelFailStopLoc` (C-TF1: the kill location of the seven
memory-model fail-stops; proofs are uniform in the atom, no inequality between
the two atoms is claimed — a transparent `def` alternative is a TODO item).

There is no other declared boundary. The debug no-op stubs (`CerbDebug`,
`CerbUtils`) are off every differential path (the oracle's debug level
is 0 in matched mode); `CerbFS` and concurrency are class (c) as stated
in §3; the fuel bound is class (b)/fuel with its parameter. Known
limitations with owners are in §3 and [TODO.md](TODO.md).


## Provisioning the fork-drift oracle

Public prerequisite recipe, documented 2026-09-25 against gate implementation
`bb487dda7c56981e76d67f53ae16e874cfe5ed61` (follow-up changes and
executed commands are recorded in `docs/2026-09-25_public-readiness-followup.md`).
Row 1 needs both the pinned upstream Git ref and an independently generated
upstream OCaml tree. The gate no longer guesses a container-specific path.
Use a new directory and the same installed fork Lem pin as the fork build:

```bash
# From this fork's repository root, after the README installation:
fork_root=$PWD
# Add this remote only if it does not already exist; verify its URL otherwise.
git remote add upstream https://github.com/rems-project/cerberus.git
git fetch upstream master:refs/remotes/upstream/master
upstream_pin=$(sed -n 's/^merge-base=//p' scripts/fork_drift_manifest.txt)
mkdir -p .validation-foundations
upstream_source="$fork_root/.validation-foundations/fork-drift-upstream"
git clone https://github.com/rems-project/cerberus.git "$upstream_source"
git -C "$upstream_source" checkout --detach "$upstream_pin"
opam exec --switch="$fork_root" -- make -C "$upstream_source" prelude-src
export CERB_UPSTREAM_TREE="$upstream_source/ocaml_frontend/generated"
opam exec --switch=. -- ./scripts/check_fork_drift.sh
opam exec --switch=. -- ./scripts/test_unit.sh
```

The gate compares the fork against the PINNED merge-base commit (`merge-base=` in
`scripts/fork_drift_manifest.txt`), which `upstream/master` only serves to locate and
validate; fetching a newer upstream master is therefore not drift (fresh-clone finding,
2026-09-25: the gate previously diffed against the ref itself). The generated-tree
comparison is different from the pristine executable
manifest needed by LADDER Tier B row 10. That row documents
`ensure_independent_oracle.py` and its independently built runtime.
Neither `release.py` nor a green newcomer smoke check supplies all external
corpora or oracle manifests. Use `CERB_UPSTREAM_TREE` for the explicit
generated-tree path; absence is a gate failure. `CERB_FORK_DRIFT_DEV_SKIP=1`
is a labelled development escape hatch and is explicitly unset by row 1.
The totality gate enforces by default; `ENFORCE=0` is labelled report-only
and row 1 overrides it to enforce. No custom global Git config is required.
