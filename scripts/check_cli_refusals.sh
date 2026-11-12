#!/usr/bin/env bash
# check_cli_refusals.sh — contract enforcement witness (CONTRACT.md §4.1,
# 2026-09-28): every CLI-refused area has a pinned refusal. Each flag below
# must make the Lean driver exit 2 with `cerberus-lean: refused — <flag>:`
# and its named feature (Main.lean refuseFlag). Control: the same argv
# without the flag must NOT be refused (so a driver that refuses everything,
# or exits 2 for another reason, cannot pass). Fail-closed.
#
# CLASS [AGENT, per [USER 2026-10-07] "… we don't want our gates to be adversarially robust
# unless they are trust surfaces …"]: a SPEEDBUMP — it pins the CLI's refusal TEXTS and the
# acceptance of `--switches=PNVI_ae_udi` (PNVI arc S4) so an accidental change is loud. The
# trust property behind the acceptance — agreement with the oracle under the switch — is
# the lane's (scripts/test_pnvi.sh, a trust surface); the one-program agreement witness
# below only shows the accepted switch reaches the semantics.
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN="${CERB_LEAN_BIN_OVERRIDE:-$SCRIPT_DIR/../lean_frontend/.lake/build/bin/cerberus-lean}"
RT="${CERB_RUNTIME_OVERRIDE:-$SCRIPT_DIR/../_build/install/default}"
[[ -x "$BIN" ]] || { echo "check_cli_refusals: FAIL — driver not built: $BIN"; exit 1; }
INPUT=/nonexistent/cli-refusal-probe.json   # never read: flags are refused first
fails=0
expect_refused() {  # $1=flag $2=feature substring
    local out rc
    out=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" --batch "$1" "$INPUT" 2>&1); rc=$?
    if [[ $rc -ne 2 || "$out" != *"cerberus-lean: refused — $1:"* || "$out" != *"$2"* ]]; then
        echo "check_cli_refusals: FAIL — $1: expected exit 2 + refusal naming '$2'; got rc=$rc: ${out:0:200}"
        fails=$((fails + 1))
    fi
}
expect_refused "--concurrency" "concurrency is not supported"
expect_refused "--switches=strict_pointer_arith" "semantics switch set is not supported"
# PNVI arc S1 (2026-10-05; design §D.3, §F.4, §F.13), S4 (2026-10-07): `--switches` is PARSED
# in both of the oracle's cmdliner forms; `PNVI_ae_udi` is accepted alone or with permissive_pointer_arith
# (the acceptance witnesses below); every other value is refused, each element with its
# own reason. The `=` form, one row per oracle switch name (switches.ml:60-102) with its
# reason's distinguishing phrase, plus the oracle's two fail-OPEN cases (an unknown name and
# an override are ignored there, R-PNVI-12 / R-PNVI-11) and mixed sets:
expect_refused "--switches=PNVI" "\`PNVI\`: the PNVI-plain / PNVI-ae provenance variants"
expect_refused "--switches=PNVI_ae" "\`PNVI_ae\`: the PNVI-plain / PNVI-ae provenance variants"
expect_refused "--switches=permissive_pointer_arith" "supported only together with PNVI_ae_udi"
expect_refused "--switches=strict_reads" "rm_unspecs Core pass"
expect_refused "--switches=forbid_nullptr_free" "its arm is a loud kill in CerbMem"
expect_refused "--switches=zap_dead_pointers" "its arm is a loud kill in CerbMem"
expect_refused "--switches=strict_pointer_equality" "its arm is a loud kill in CerbMem"
expect_refused "--switches=strict_pointer_relationals" "its arm is a loud kill in CerbMem"
expect_refused "--switches=zero_initialised" "its arm is a loud kill in CerbMem"
expect_refused "--switches=inner_arg_temps" "std_inner_arg_temps.core"
expect_refused "--switches=permissive_printf" "permissive printf"
expect_refused "--switches=CHERI" "cerberus-cheri executable"
expect_refused "--switches=copy_prop" "no counterpart in this port's lem model"
expect_refused "--switches=bogus" "unknown switch name"
expect_refused "--switches=PNVI_ae_udi,PNVI" "would override a previous switch"
expect_refused "--switches=PNVI_ae_udi,strict_reads" "\`strict_reads\`: strict reads"
expect_refused "--switches=PNVI_ae_udi,strict_reads" "\`PNVI_ae_udi\`: PNVI-ae-udi (switches.ml:82-83, SW_PNVI \`AE_UDI) is supported alone or with permissive_pointer_arith"
expect_refused "--switches=PNVI_ae_udi,PNVI_ae_udi" "R-PNVI-11"
expect_refused "--switches=PNVI_ae_udi,bogus" "R-PNVI-12"
expect_refused "--switches=PNVI_ae_udi," "an empty switch name"
expect_refused "--switches=" "an empty switch name"
# the space form (`--switches V`, two argv words): the refusal names the flag as given
out=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" --batch --switches strict_reads "$INPUT" 2>&1); rc=$?
if [[ $rc -ne 2 || "$out" != *"cerberus-lean: refused — --switches strict_reads:"* || "$out" != *"semantics switch set is not supported"* ]]; then
    echo "check_cli_refusals: FAIL — --switches strict_reads (space form): expected exit 2 + refusal; got rc=$rc: ${out:0:200}"
    fails=$((fails + 1))
fi
# ACCEPTANCE (PNVI arc S4): `--switches=PNVI_ae_udi` and `--switches PNVI_ae_udi` are NOT
# refused — with the runtime given, the driver gets past the CLI and fails at the input read,
# exactly like the control below
for form in "--switches=PNVI_ae_udi" "--switches PNVI_ae_udi" \
    "--switches=PNVI_ae_udi,permissive_pointer_arith" \
    "--switches permissive_pointer_arith,PNVI_ae_udi"; do
    # shellcheck disable=SC2086
    out=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" --batch --runtime="$RT" $form "$INPUT" 2>&1); rc=$?
    if [[ "$out" == *"cerberus-lean: refused"* || "$out" != *"cli-refusal-probe.json"* ]]; then
        echo "check_cli_refusals: FAIL — $form must be ACCEPTED (reach the input read); got rc=$rc: ${out:0:200}"
        fails=$((fails + 1))
    fi
done

# --iso (switches.ml:144-151 sets five refused switches + PNVI_ae_udi; design §F.12): refused
expect_refused "--iso" "the ISO switch set"
# S1 review L5 (deferred to PNVI arc S4 Part 1): a `--switches` value is judged by the switch
# parser wherever it appears — under `--parse-core`, and before a misplaced mode flag — never
# the generic "unknown flag" / position text; and a repeated UNKNOWN name is "failed to parse"
# each time (switches.ml:140-141), never "would override" (only known names enter the list)
expect_switch_verdict() {  # $1=label $2=required substring $3=forbidden substring; argv after
    local label="$1" want="$2" forbid="$3" out rc; shift 3
    out=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" "$@" 2>&1); rc=$?
    if [[ $rc -ne 2 || "$out" != *"$want"* || ( -n "$forbid" && "$out" == *"$forbid"* ) ]]; then
        echo "check_cli_refusals: FAIL — $label: expected exit 2 with '$want'${forbid:+ and without '$forbid'}; got rc=$rc: ${out:0:200}"
        fails=$((fails + 1))
    fi
}
expect_switch_verdict "--parse-core --switches=bogus" "\`bogus\`: unknown switch name" "unknown flag" --parse-core --switches=bogus "$INPUT"
expect_switch_verdict "--parse-core --switches bogus" "\`bogus\`: unknown switch name" "unknown flag" --parse-core --switches bogus "$INPUT"
expect_switch_verdict "--switches=bogus before --batch" "\`bogus\`: unknown switch name" "canonical position" --switches=bogus --batch "$INPUT"
expect_switch_verdict "--switches=bogus,bogus" "\`bogus\`: unknown switch name" "would override" --batch --switches=bogus,bogus "$INPUT"
expect_switch_verdict "--parse-core --switches=PNVI_ae_udi" "reads no switch set" "unknown flag" --parse-core --switches=PNVI_ae_udi "$INPUT"
expect_switch_verdict "--switches=PNVI_ae_udi before --batch" "canonical position" "semantics switch set" --switches=PNVI_ae_udi --batch "$INPUT"
# control: no refused flag → not a refusal. The runtime is given explicitly
# (the driver refuses without one since bug-hunt BUG-2, 2026-09-29), so the
# control reaches the input read and fails there, unrefused.
out=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" --batch --runtime="$RT" "$INPUT" 2>&1); rc=$?
if [[ "$out" == *"cerberus-lean: refused"* ]]; then
    echo "check_cli_refusals: FAIL — control refused without a refused flag (rc=$rc): ${out:0:200}"
    fails=$((fails + 1))
fi
# repeated single-valued options the oracle's command line rejects (bug-hunt
# fixes pre-merge audit L3, 2026-09-30): exit 2 with the "cannot be repeated"
# message, never silently the last value
for pair in "--runtime=$RT --runtime=$RT" "--args a --args b" "--switches=PNVI_ae_udi --switches=PNVI_ae_udi" "--switches PNVI_ae_udi --switches=strict_reads"; do
    # shellcheck disable=SC2086
    out=$(env LEAN_ABORT_ON_PANIC=1 CERB_INSTALL_PREFIX="$RT" "$BIN" --batch $pair "$INPUT" 2>&1); rc=$?
    if [[ $rc -ne 2 || "$out" != *"cannot be repeated"* ]]; then
        echo "check_cli_refusals: FAIL — repeated option ($pair): expected exit 2 + 'cannot be repeated'; got rc=$rc: ${out:0:200}"
        fails=$((fails + 1))
    fi
done
# AGREEMENT WITNESS (PNVI arc S4): one small program on which the switch changes the answer
# (a pointer rebuilt from an exposed address bit by bit: PVI loses the provenance, UB043;
# PNVI-ae-udi finds the exposed allocation) — Lean under --switches=PNVI_ae_udi must equal the
# oracle under the same switch, and Lean without the switch must equal the oracle without it
# and DIFFER from the switched answer (so the witness cannot pass with the switch ignored).
# A pinned installed oracle can supply the witness without a local OCaml build.
ORACLE="${CERB_ORACLE_BIN_OVERRIDE:-$SCRIPT_DIR/../_build/default/backend/driver/main.exe}"
if [[ ! -x "$ORACLE" ]]; then
    echo "check_cli_refusals: FAIL — oracle not built (agreement witness): $ORACLE"; fails=$((fails + 1))
else
    W=$(mktemp -d "$SCRIPT_DIR/../.tmp/cli-refusals.XXXXXXXX") || { echo "check_cli_refusals: FAIL — mktemp"; exit 1; }
    trap 'rm -rf "$W"' EXIT
    cat > "$W/w.c" <<'CEOF'
#include <stdint.h>
int x = 7;
int main(void) {
  uintptr_t i = (uintptr_t)&x, j = 0;
  for (int k = 0; k < 64; k++)
    if (i & ((uintptr_t)1 << k)) j |= (uintptr_t)1 << k;
  return *(int *)j;
}
CEOF
    if ! env NO_COLOR=1 TERM=dumb "$ORACLE" --runtime="$RT" --cabs-json "$W/w.c" > "$W/w.json" 2> "$W/w.json.err"; then
        echo "check_cli_refusals: FAIL — oracle --cabs-json failed: $(head -c 200 "$W/w.json.err")"; fails=$((fails + 1))
    else
        osw=$(env NO_COLOR=1 TERM=dumb "$ORACLE" --runtime="$RT" --nolibc --exec --batch --mode=exhaustive --switches=PNVI_ae_udi "$W/w.c" 2>/dev/null)
        odf=$(env NO_COLOR=1 TERM=dumb "$ORACLE" --runtime="$RT" --nolibc --exec --batch --mode=exhaustive "$W/w.c" 2>/dev/null)
        lsw=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" --batch --runtime="$RT" --switches=PNVI_ae_udi "$W/w.json" 2>&1)
        ldf=$(env LEAN_ABORT_ON_PANIC=1 "$BIN" --batch --runtime="$RT" "$W/w.json" 2>&1)
        if [[ -z "$osw" || "$lsw" != "$osw" || "$ldf" != "$odf" || "$lsw" == "$ldf" || "$osw" != Defined* ]]; then
            echo "check_cli_refusals: FAIL — PNVI_ae_udi agreement witness: oracle(sw)=${osw:0:120} lean(sw)=${lsw:0:120} oracle(default)=${odf:0:120} lean(default)=${ldf:0:120}"
            fails=$((fails + 1))
        fi
    fi
fi
[[ $fails -eq 0 ]] || exit 1
echo "check_cli_refusals: OK (24 refusals pinned: --concurrency, --iso, 21 --switches= values (every unsupported standalone oracle switch-name class, an unknown name, overrides, mixed sets, the empty value and a trailing empty element) and the --switches space form; PNVI_ae_udi alone and with permissive_pointer_arith ACCEPTED in both CLI forms; on one program PNVI_ae_udi runs, agrees with the oracle under the same switch and differs from the default; 6 switch-placement verdicts (--parse-core =/space/accepted, before a misplaced --batch refused and accepted, a repeated unknown name not an override); 4 repeated options refused: --runtime, --args, --switches twice (=/= and space/=); control not refused)"
