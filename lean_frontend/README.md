# cerberus-lean: the Cerberus C semantics in Lean 4

> **Health warning — this is a research prototype; expect bugs.** Differential testing samples behaviour and does
> not prove agreement with the OCaml implementation, and some parts are tested much less than others.
> [CONTRACT.md](CONTRACT.md) says what is supported, what is refused, and how deeply each part is tested.

**Documentation check, 2026-09-25:** implementation `bb487dda7c56981e76d67f53ae16e874cfe5ed61`;
Lem `67ec5de70e02e280bb348a4ba826696b76116732` (the Lem pin has since moved to `2d3a492758cb23dc4e417f2961983d25b36ce130` by functional re-pins (via `77ad4fa` and `4e70bb5`, both merged; the current pin `2d3a492` itself is PROVISIONAL — the head of the unmerged lem-lean branch `arc/pnvi-switches`, not yet on `mdd/lean-backend`), generated OCaml byte-identical at each: [re-pin record](docs/2026-10-04_lem-repin-4e70bb5-record.md), [PNVI S1 record](docs/2026-10-05_pnvi-s1-switch-parameter-record.md)). Current follow-up gates and remaining
publication checks are in [the follow-up record](docs/2026-09-25_public-readiness-followup.md);
earlier baseline inventories are in [the remediation record](docs/2026-09-24_public-readiness-remediation.md).
Older dated measurements below remain historical evidence.

This directory contains a Lean 4 port of the [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/)
C semantics. Both targets are generated from shared Lem source, with
handwritten runtime seams. The Lean pipeline imports the OCaml parser's
Cabs JSON, elaborates it to Core, and executes Core inside Lean. Shared
source makes correspondence reviewable; it does not establish equivalent
failure behavior or a general conformance theorem by construction.

The execution definitions pass the repository's totality and axiom gates,
and differential lanes compare their printed observations with the fork's
OCaml engine. There are still explicit failure, fuel, representation and
runtime-boundary obligations. In particular, deliberate pure failures can
be erased by Lean evaluation (unused `let`s are forced by LemLib's temporary
`lemSeq` native seam since the 2026-09-30 lem re-pin; VALIDATION §3), and the digest seam retains ambient runtime
state behind a pure signature (the enum registry no longer does: since
program-data parameters E-A, 2026-09-20, the enum's compatible type is
program data — a reader parameter of the model). Zero added axiom
declarations does not prove
agreement between those declarations and their native implementations.
See the [supported profile](SUPPORTED.md) and
[VALIDATION.md](VALIDATION.md) for measured scope and remaining release exits.
The [validation-foundations delivery](docs/2026-09-06_validation-foundations-delivery.md)
is a historical record. `--switches=PNVI_ae_udi` is supported, with optional `permissive_pointer_arith`.
The original PNVI lane is `scripts/test_pnvi.sh`; focused arithmetic cases are in
`scripts/test_permissive_pointer_arith.py`. Other combinations remain refused
(CONTRACT §2).
Concurrency is not part of the supported product; the
announcement concerns the sequential port and its stated limits. The
replacement SC build is governed by the
[SC concurrency master plan](../SC-CONCURRENCY.md), which records its status;
no SC execution mode has landed. The operator reported customer
acceptance on 2026-09-24; this is distinct from complete release certification
or a general correspondence theorem (see SUPPORTED).

**Provenance.** This port was developed primarily by AI agents
(Claude, Anthropic) operating under the direction and review of a
human operator (Mike Dodds). The upstream Cerberus semantics is by
its own authors (see the top-level README); the dated records in
`docs/` are the working history of the port.

**Licensing.** The fork retains Cerberus's [LICENSE](../LICENSE) and its
listed exceptions. The LemLib dependency includes translated OCaml AVL
code with its own retained notices; consult Lem's [runtime NOTICE](https://github.com/OathTech/lem-lean/blob/2d3a492758cb23dc4e417f2961983d25b36ce130/lean-lib/NOTICE.md) and
[LICENSE](https://github.com/OathTech/lem-lean/blob/2d3a492758cb23dc4e417f2961983d25b36ce130/LICENSE) at the pinned revision. Neither the complete dependency closure nor LemLib
should be described as BSD-only.

Who this is for:

- You want to **run C** through an executable, rigorously defined
  semantics from inside Lean (undefined-behaviour verdicts included).
- You want to know **why you should trust it** — see
  [VALIDATION.md](VALIDATION.md) for the differential-validation
  story and the gate list.
- You want to understand **how the port works** — see
  [DESIGN.md](DESIGN.md).

## Five-minute orientation

```
lean_frontend/
├── generated/        # Lean code generated from the Lem model (do not edit)
├── *.lean            # hand-written "seam" files (memory model, ND runner,
│                     #   parsers, implementation-defined behaviour, ...)
├── speclab/          # harness-family differential lanes: models, codecs,
│                     #   and a C harness renderer (see speclab/README.md)
├── corpus/           # pinned differential-fixture programs (hash-frozen)
├── test/             # unit tests + gate executables
└── docs/             # dated design records and results (the port's history)
```

The C parser stays in OCaml: `cerberus --cabs-json` parses C and emits
a JSON AST; the Lean pipeline does everything after that (desugaring,
typing, elaboration to Core, execution).

## Build and run one differential test

Measured platform: Linux x86_64; other platforms are unverified.
Prerequisites: Git, Bash, GNU make/coreutils/findutils/diffutils, GNU time
(default `/usr/bin/time`), a C toolchain, opam 2, Python 3, and elan with Lean 4.32.2 installed (the committed `lean-toolchain`). The
measured OCaml toolchain is 5.4.0 with opam 2.1.5 and Dune 3.23.1; the
package files constrain Dune to `>= 3.21.0 & < 3.24.0`. Use the fork of Lem
at the **same revision as Lake's LemLib**; upstream `opam install lem` does
not supply this backend. No parent checkout or Git URL redirects are
required by the public recipe.

If opam has not been initialized, run `opam init --bare --no-setup` once
before the following commands.

```bash
git clone --branch mdd/cerberus-lean https://github.com/OathTech/cerberus-lean.git
cd cerberus-lean
opam switch create . ocaml-base-compiler.5.4.0 --no-switch --no-install
# Keep this revision equal to lean_frontend/lakefile.toml.
opam pin add --switch=. lem git+https://github.com/OathTech/lem-lean.git#2d3a492758cb23dc4e417f2961983d25b36ce130 --yes
opam install --switch=. --deps-only ./cerberus-lib.opam ./cerberus.opam --yes

opam exec --switch=. -- make prelude-src
opam exec --switch=. -- dune build backend/driver/main.exe cerberus-lib.install
opam exec --switch=. -- dune install --prefix "$PWD/_build/local-install" cerberus-lib
opam exec --switch=. -- dune build cerberus.install

# Generate the Lean model AND compile its native digest support before linking.
opam exec --switch=. -- make lean-prelude-src
CERB_MEM_MAX=32G opam exec --switch=. -- ./scripts/capped make lean-native-obj
(cd lean_frontend && CERB_MEM_MAX=32G ../scripts/capped lake build CerberusLean cerberus-lean)

# Run one C program through both implementations (expected return: 42).
LEAN_ABORT_ON_PANIC=1 CERB_MEM_MAX=32G opam exec --switch=. -- \
  ./scripts/test_exec.sh tests/minimal/001-return-literal.c
```

The local cold-source check used preinstalled dependencies and local Git
mirrors; public URL/revision availability and fresh downloads are still
**UNVERIFIED-OFFLINE** for Git transport/downloads, with current public web
observations and operator commands in the
[follow-up record](docs/2026-09-25_public-readiness-followup.md).
`scripts/capped` tries Linux cgroup v2, then a systemd user service. It
defaults to 64G unless `CERB_MEM_MAX` is set; the commands above request
32G. Enforcing a cap needs cgroup v2 delegation or a working systemd user
service. `CERB_MEM_MAX=none` explicitly opts out with a warning;
`CERB_JOB_CGROUP=/delegated/path` requests an owned subtree and fails if
that setup cannot be enforced. If
direct cgroup setup fails and `systemd-run` is absent, it warns and runs
uncapped; if `systemd-run` exists but its user service is unavailable,
the command fails. The limit is a ceiling,
not a stated minimum RAM requirement. Rebuild `lean-native-obj` after native
source changes. `LEAN_ABORT_ON_PANIC=1` stops reached native panics; it does
not prevent erasure of unused pure failure expressions.

Fork problems belong in [OathTech/cerberus-lean issues](https://github.com/OathTech/cerberus-lean/issues).
Include the source and Lem pins, toolchain, small C input and exact command.
Maintainers use the upstream tray for prepared upstream reports; newcomers
do not need to edit that tray to report a problem.

The full test surface — unit gates plus the per-corpus differential
scripts ("lanes") and their pinned baselines — is catalogued in
`scripts/LADDER.md` and summarized in [VALIDATION.md](VALIDATION.md);
the agent-facing operating manual with all build gotchas is
[CLAUDE.md](CLAUDE.md).

## Validation levels and prerequisites

The quickstart is a **smoke check**: one C program passes through the parser,
Lean pipeline and OCaml oracle. The small differential gates are separate:

```bash
# Repository root; provision fork drift as described in VALIDATION.md first.
opam exec --switch=. -- ./scripts/test_unit.sh
opam exec --switch=. -- ./scripts/test_exec.sh --check-baseline
opam exec --switch=. -- ./scripts/test_exec.sh --check-baseline=scripts/exec_coverage_baseline.txt tests/coverage
opam exec --switch=. -- ./scripts/test_exec.sh --check-baseline=scripts/exec_debug_baseline.txt tests/debug
opam exec --switch=. -- ./scripts/test_exec.sh --check-baseline=scripts/exec_float_baseline.txt tests/float
opam exec --switch=. -- ./scripts/test_bytes.sh
opam exec --switch=. -- ./scripts/test_libc_exec.sh
```

These are row 1 plus six fast lanes, not the entire release ladder.
[`scripts/LADDER.md`](../scripts/LADDER.md) lists the other lanes,
including multi-TU, address-space, independent upstream comparisons and
externally supplied CN/libxml2 corpora. Inspect selections before a run:

```bash
python3 scripts/release.py --list
# ALL Tier A rows and their prerequisites, beyond the small set above:
opam exec --switch=. -- ./scripts/ci_lean.sh --mode fast
# (Tier A row 14, the PNVI lane, needs the GPL-licensed pKVM case study at
# deps/CN-pKVM-buddy-allocator-case-study or $PKVM_CASE_STUDY, fetched separately;
# without it the row fails closed, so a fresh clone cannot pass full Tier A.)
# Tier A + Tier B, after provisioning every dependency in LADDER.md:
opam exec --switch=. -- ./scripts/ci_lean.sh --mode full
```

Reporting campaigns require `--mode reporting` and explicit `--lane`
selections; their classified failures are evidence, not a certification pass.
The inherited GitHub workflows and root badges cover upstream OCaml/CHERI.
No fork Lean certification workflow is wired up; dated manual gate
records linked from VALIDATION and SUPPORTED are the measured evidence.
A normal shell needs no `GIT_CONFIG_GLOBAL` setting or container env loader.
`_build/default/backend/driver/main.exe --version` retains a commit hash at an exact annotated Git tag;
source archives without Git metadata cannot attest that identity (opam may
supply a release watermark). `bash scripts/test_version.sh` checks the
production generator in an isolated scratch repository.

## What you can do with it

- **Batch execution with verdicts.** `cerberus-lean --batch
  --runtime=_build/install/default <cabs-json>` runs a program's `main`
  and reports the Cerberus verdict — a `Defined` value (with
  stdout/stderr), a specific undefined-behaviour code, or an error —
  exhaustively over the nondeterministic branch structure or as a single
  trace (`--first`). The runtime (`std.core`, the implementation file) is
  the oracle's: `--runtime DIR` or the `CERB_INSTALL_PREFIX` environment
  variable, runtime = `DIR/lib/cerberus-lib/runtime`, the same prefix the
  cabs-json was exported with (`cerberus --runtime=DIR --cabs-json`). The
  driver refuses to run without one; it never searches the working
  directory and does not use the oracle's `OPAM_SWITCH_PREFIX` fallback.
  The lanes export `CERB_INSTALL_PREFIX` from `scripts/common.sh`.
- **Function-level execution.** `--call <f> [--call-args <ints>]`
  calls an individual function with injected arguments (the caller
  protocol mirrors elaborated call sites; `CerbCall.lean`, a port-side
  harness entry over the generated driver — the oracle has no such
  mode, so the lanes run it on a rendered wrapper TU), used by the
  fixture lanes to compare individual functions against the oracle
  point-by-point.
- **Libc-linked and multi-TU programs.** The Lean pipeline links
  multiple translation units and can load the C standard library the
  oracle ships, so real multi-file programs (libxml2 slices, the CN
  corpus, csmith output) run under both implementations.
- **Semantics-level differential testing of C tooling.** The lanes in
  `scripts/` are reusable instruments: point them at a corpus and any
  divergence between the two implementations — or between either and
  a recorded expectation — fails loudly.

## The headline validation numbers

Committed baseline inventory and historical measurements (see
[VALIDATION.md](VALIDATION.md) for comparison projections and run tiers,
and the [cleanup record](docs/2026-09-24_public-readiness-remediation.md)
for the exact lanes rerun at the cleanup pins):

- 113 rows in `scripts/exec_baseline.txt` (derived 2026-09-24 at
  `e9f9d049f`): 90 MATCH + 18 UB_MATCH + 5 CERB_SKIP (rows the oracle itself
  cannot run: recorded, never counted as agreement) — plus the
  coverage, debug, and float suites at their pinned baselines;
- Historical measurement: 213/213 programs of the CN test corpus (multi-TU, libc proxies);
- Historical measurement: 16/16 URIs through libxml2's `xmlParseURISafe` (5 translation
  units, libc-linked, byte-identical output) plus a 1,354-point
  libxml2 `chvalid` boundary battery;
- a historical 1,669-program csmith classified baseline (not rerun by
  validation foundations; the separately owned legacy run is excluded);
- the 2026-09-06 CI measurement: 2,186 rows, comprising 1,205 MATCH,
  154 UB_MATCH, one UB_DIFF, three FS refusals, three Lean timeouts and
  820 oracle-side exclusions (766 rejects, 29 errors, 25 timeouts).
  Only the 1,359 MATCH/UB_MATCH rows are observation agreement;
  [the reporting record](docs/2026-09-06_ci-reporting-results.md) records
  classification movement and limitations;
- Historical measurement: ~2,000 rendered harness-program executions across the five
  spec-lab differential families;
- per-function call-point differentials over the `tests/verify` and
  `corpus/` fixture sets.

Start with [VALIDATION.md](VALIDATION.md) for the trust story;
[DESIGN.md](DESIGN.md) for architecture; [TODO.md](TODO.md) for the
backlog; `docs/` for the dated record of how everything got here;
[docs/upstream-tray/README.md](docs/upstream-tray/README.md) if you
maintain Cerberus or Lem and were sent here to triage our bug reports.
