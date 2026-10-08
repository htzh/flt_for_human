#!/usr/bin/env python3
"""Re-measure the typeclass-instance captures recorded in the friction register.

An instance brick (`haveI`/`letI`/`private instance`) is a cache of a synthesis
result: its key is the goal's exact spelling and its value is the term search would
have built. Two failures are silent in the ordinary build:

* a **stale key** — the goal's spelling moved, or a mathlib bump changed what the
  head unfolds to, so search no longer reaches the brick. It does not error; it
  quietly falls through to the wall the brick was meant to remove.
* a **wrong value** — for a data-valued class, a brick that names a different term
  of the same type still type-checks, and the mismatch surfaces much later as a hard
  `Type mismatch` (the D-6 §2.3 failure).

`spec/InstanceProbe.lean` prints what search picks, labelled, for every register
entry (`#probe IF003_map : …` -> `PROBE IF003_map => OK <term>`, or `=> FAIL` when it
picks nothing). This script runs it and compares the labelled lines against the
recorded expectations below, so the reading is mechanical rather than re-derived:

    python3 spec/check_instance_probes.py            # compare, report drift
    python3 spec/check_instance_probes.py --update   # re-capture into this file

Exit status is 0 when every probe matches, 1 otherwise. Re-run after a mathlib bump
and after any change to an entry's home module — the same cadence as
`instance-friction.md`.

Run serially with other Lean work (the port's build discipline: one `lake env lean`
at a time).
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent  # lean/
PROBE = "spec/InstanceProbe.lean"

# One row per register entry (instance-friction.md IF-NNN): name -> ("OK", the term
# search picks) | ("FAIL", None). A FAIL is a real measurement, not a placeholder: it
# is a spelling the brick exists to bridge, and if it ever starts to synthesize the
# entry can be retired. `--update` rewrites only the marked block.
# BEGIN EXPECTED
EXPECTED = {
    "IF001_naive": ("FAIL", None),
    "IF003_goal": ("FAIL", None),
    "IF003_map": ("OK", "instIsEllipticMap E (algebraMap R R)"),
}
# END EXPECTED

LINE = re.compile(r"^PROBE (\S+) => (?:(OK) (.*)|(FAIL))\s*$")


def run_probe(timeout: int) -> tuple[str, float]:
    t0 = time.time()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", PROBE],
            cwd=LEAN,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except FileNotFoundError:
        sys.exit("error: `lake` not found on PATH (run from the lean/ project)")
    except subprocess.TimeoutExpired:
        sys.exit(f"error: `lake env lean {PROBE}` exceeded {timeout}s")
    wall = time.time() - t0
    return proc.stdout + proc.stderr, wall


def parse(output: str) -> tuple[dict[str, tuple[str, str | None]], list[str]]:
    seen: dict[str, tuple[str, str | None]] = {}
    errors: list[str] = []
    for line in output.splitlines():
        m = LINE.match(line)
        if m:
            name, ok, term, fail = m.groups()
            seen[name] = ("OK", term) if ok else ("FAIL", None)
        elif re.match(r"^\S+:\d+:\d+: error", line):
            errors.append(line)
    return seen, errors


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--timeout", type=int, default=600,
                    help="wall bound for the probe run, seconds (default 600)")
    ap.add_argument("--update", action="store_true",
                    help="rewrite the EXPECTED table in this file from the capture")
    args = ap.parse_args()

    output, wall = run_probe(args.timeout)
    seen, errors = parse(output)

    print(f"# {PROBE}: captured in {wall:.1f}s, {len(seen)} probe(s)")

    if args.update:
        def q(s: str) -> str:
            return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

        body = ["EXPECTED = {"]
        for name in sorted(seen):
            kind, term = seen[name]
            row = f'("{kind}", {q(term)})' if term is not None else f'("{kind}", None)'
            body.append(f'    "{name}": {row},')
        body.append("}")
        src = Path(__file__).read_text()
        src = re.sub(r"# BEGIN EXPECTED\n.*?# END EXPECTED",
                     "# BEGIN EXPECTED\n" + "\n".join(body) + "\n# END EXPECTED",
                     src, flags=re.S)
        Path(__file__).write_text(src)
        print("\n".join(body))
        print("-- EXPECTED table rewritten")
        return 0 if not errors else 1

    failed = False

    if errors:
        failed = True
        print(f"\n{len(errors)} elaboration error(s) — the probe file must stay green:")
        for line in errors[:10]:
            print("  " + line)

    for name, (want_kind, want_term) in EXPECTED.items():
        if name not in seen:
            failed = True
            print(f"  MISSING  {name}: no PROBE line (probe removed or renamed?)")
            continue
        kind, term = seen[name]
        if (kind, term) == (want_kind, want_term):
            shown = term if kind == "OK" else "FAIL"
            print(f"  ok       {name}: {shown}")
        elif want_kind == "OK" and kind == "FAIL":
            failed = True
            print(f"  REGRESS  {name}: expected OK {want_term!r}, now FAIL "
                  f"— search no longer reaches this spelling")
        elif want_kind == "FAIL" and kind == "OK":
            failed = True
            print(f"  RETIRE?  {name}: expected FAIL, now OK {term!r} "
                  f"— re-measure and retire the register entry")
        else:
            failed = True
            print(f"  RECAPTURE {name}: term changed\n"
                  f"             was {want_term!r}\n"
                  f"             now {term!r}\n"
                  f"           update the register and any brick naming it")

    for name in sorted(set(seen) - set(EXPECTED)):
        failed = True
        print(f"  UNKNOWN  {name}: probe has no EXPECTED row")

    print("\ninstance probe capture: " + ("drift" if failed else "all entries match"))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
