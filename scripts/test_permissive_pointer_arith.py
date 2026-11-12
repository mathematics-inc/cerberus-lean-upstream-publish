#!/usr/bin/env python3
"""Compare eight pointer cases under PNVI and PNVI with permissive arithmetic.

Run under scripts/capped. Keep --out for commands, source, ASTs and observations.
The oracle and Lean must agree on the complete verdict, including UB locations;
independent expected outcomes prevent agreement on a shared, wrong result.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PNVI = "PNVI_ae_udi"
PERMISSIVE = PNVI + ",permissive_pointer_arith"
DEFINED = b'Defined {value: "Specified(0)", stdout: "", stderr: "", blocked: "false"}\n'
EXPECTED = [
    ("UB046_array_pointer_outside", None),
    ("UB048_disjoint_array_pointers_subtraction", None),
    ("UB048_disjoint_array_pointers_subtraction", "UB048_disjoint_array_pointers_subtraction"),
    ("UB046_array_pointer_outside", "UB_CERB002a_out_of_bound_load"),
    ("UB046_array_pointer_outside", None),
    ("UB046_array_pointer_outside", "UB046_array_pointer_outside"),
    (None, None),
    ("UB046_array_pointer_outside", None),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oracle", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    runtime = "--runtime=" + str(args.runtime.resolve())

    def run(name, argv):
        argv = list(map(str, argv))
        (out / (name + ".argv.json")).write_text(json.dumps(argv) + "\n")
        result = subprocess.run(argv, capture_output=True, timeout=30,
                                env={**os.environ, "LEAN_ABORT_ON_PANIC": "1", "NO_COLOR": "1", "TERM": "dumb"})
        (out / (name + ".stdout")).write_bytes(result.stdout)
        (out / (name + ".stderr")).write_bytes(result.stderr)
        return result

    source = (ROOT / "tests/permissive_pointer_arith.c").read_text()
    for case, expected in enumerate(EXPECTED):
        program = out / f"case{case}.c"
        program.write_text(f"#define CASE {case}\n" + source)
        parsed = run(f"{case}-parse", [args.oracle, runtime, "--nolibc", "--cabs-json", program])
        if parsed.returncode or parsed.stderr:
            raise SystemExit(f"FAIL case {case}: parser; see {out}")
        ast = out / f"case{case}.json"
        ast.write_bytes(parsed.stdout)
        for index, switches in enumerate([PNVI, PERMISSIVE]):
            prefix = f"{case}-{index}"
            oracle = run(prefix + "-oracle", [args.oracle, runtime, "--nolibc", "--exec", "--batch", "--switches=" + switches, program])
            lean = run(prefix + "-lean", [args.lean, "--batch", "--first", "--fuel", "100000", runtime, "--switches=" + switches, ast])
            ub = expected[index]
            valid = (oracle.stdout == DEFINED if ub is None else
                     re.fullmatch(rb'Undefined \{ub: "' + ub.encode() + rb'", stderr: "", loc: "[^"]+"\}\n', oracle.stdout))
            # OCaml emits only a timing line outside the batch verdict.
            timing_only = re.fullmatch(rb'Time spent: [0-9.]+ seconds\n', oracle.stderr)
            if not (valid and oracle.returncode == (1 if ub else 0) and timing_only
                    and lean.returncode == oracle.returncode and lean.stdout == oracle.stdout and not lean.stderr):
                raise SystemExit(f"FAIL case {case}, {switches}; see {out}")
            print(f"PASS case {case}, {switches}: {ub or 'defined zero'}")


if __name__ == "__main__":
    main()
