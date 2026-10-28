#!/usr/bin/env python3
"""gate_scan.py — the declaration-level definition gate of a ready set.

Why this file exists
--------------------
`port_advise --with-defs` answers "which pin `Definitions/Def_*.lean` modules are in the
set's wrapper closure", and the shelf briefs price a definition gate per *module*.  That is
the wrong unit for a ready set: the readiness test is premise-based, so a row reads ready and
a module of the closure may sit in it with one declaration the row names and twenty it does
not.  The MC definition wave
(`topics/modularCurve/WORKORDER-MCDEF-definition-wave.md` §0.1) is the worked case: the
shelf priced `CohCarrier_Fricke` at 164 lines for story M9, while the row
`exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` names seven of its 28 declarations.

This tool computes the gate at the unit the work is written in — the declaration:

  1. the pin `Def_` module's public declarations (`spec/lean_parser.py`'s `declarations`);
  2. the declarations whose *last name* occurs as a word in the row's `S_` file text (import
     lines stripped), plus the **intra-module closure** of the declarations those bodies call
     (`declaration_bodies`), because using `diamondHBar` pulls in `diamondAutHBar`;
  3. which of the used declarations are **already in the port** (a last-name index over the
     port tree), so the gate is the used-and-missing set, with its pin line span.

Not a substitute for the recipe's hand read: the scan is name-anchored (a port copy under
another name reads as missing — `port_advise`'s documented false negative), it does not read
mathlib, and a row can need a definition that appears only in a *premise's* proof.  It is the
first cut that turns "this module is a gate" into "these declarations are the gate".

Two mechanical discounts, both learned on the MC wave.  `import` lines are stripped.  So are
`attribute [ … ]` lines: the pin's wrappers and `S_` files list every relevant `-simp` /
`-instance` lemma globally to normalise the environment for `p2m_exact_reverting`, and the port
deliberately does not reproduce those lists (`ModularForms/CohCarrier/CommTriplet.lean`'s
header) — without the strip, the `exists_slash_fricke_eq_sum_smul_…` wrapper "uses" eleven
declarations of `Def_CohCarrier_HeckeData` that it only un-`simp`s.

Usage
-----
    python3 spec/gate_scan.py --pin Definitions/Def_CohCarrier_Fricke.lean \\
        --rows S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion

    python3 spec/gate_scan.py --pin Definitions/Def_ModularCurve_X1HeckeModule.lean \\
        --rows Theorems/Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean --json

`--rows` entries are paths relative to the pin root; a bare name is looked up under
`Theorems/`, then `P2M/Sol/`.  `--pin-root` and `--port-root` override the defaults
(`~/proj/fermats-last-theorem` and `FLTForHuman`).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_parser as lp  # noqa: E402

DEFAULT_PIN_ROOT = Path.home() / "proj" / "fermats-last-theorem"
PIN_SEARCH = ("Theorems", "P2M/Sol", "Definitions")


def resolve(pin_root: Path, name: str) -> Path:
    """A pin file by path relative to the pin root, or by bare name."""
    name = name if name.endswith(".lean") else name + ".lean"
    direct = pin_root / name
    if direct.exists():
        return direct
    for d in PIN_SEARCH:
        p = pin_root / d / name
        if p.exists():
            return p
    raise SystemExit(f"gate_scan: not found in the pin: {name}")


def decl_index(text: str) -> dict[str, tuple[str, int, int]]:
    """last name -> (kind, start line, span) for a pin file's declarations."""
    lines = text.splitlines()
    stripped = lp.strip_comments(text)
    # strip_comments preserves line structure for the block comments the pin uses
    matches = list(lp.DECL_RE.finditer(stripped))
    out: dict[str, tuple[str, int, int]] = {}
    for i, m in enumerate(matches):
        start = text[: m.start()].count("\n") + 1 if len(stripped) == len(text) else None
        end = (
            text[: matches[i + 1].start()].count("\n")
            if i + 1 < len(matches) and len(stripped) == len(text)
            else len(lines)
        )
        if start is None:  # line numbers are only available when nothing was removed
            start, end = 0, 0
        name = m.group("name").rsplit(".", 1)[-1]
        out.setdefault(name, (m.group("kind"), start, end - start))
    return out


def word_hit(name: str, text: str) -> bool:
    return re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text) is not None


def strip_non_uses(text: str) -> str:
    """Drop the lines that name declarations without using them: `import` and `attribute`."""
    return "\n".join(
        line
        for line in text.splitlines()
        if not line.startswith("import ") and not line.startswith("attribute ")
    )


def body_index(text: str) -> dict[str, str]:
    return {
        raw.rsplit(".", 1)[-1]: body
        for raw, _kind, _stmt, body in lp.declaration_bodies(text, include_private=True)
    }


def port_index(port_root: Path) -> dict[str, str]:
    """last name -> the first port module declaring it."""
    out: dict[str, str] = {}
    for p in sorted(port_root.rglob("*.lean")):
        try:
            text = p.read_text(errors="ignore")
        except OSError:
            continue
        for raw, _kind, _stmt in lp.raw_declarations(text):
            out.setdefault(raw.rsplit(".", 1)[-1], str(p))
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--pin", required=True, help="the pin Def_ module, path relative to the pin root")
    ap.add_argument("--rows", nargs="+", required=True, help="row S_/wrapper files (paths or bare names)")
    ap.add_argument("--pin-root", default=str(DEFAULT_PIN_ROOT))
    ap.add_argument("--port-root", default="FLTForHuman")
    ap.add_argument("--json", default=None, help="write the scan as JSON to this file")
    args = ap.parse_args()

    pin_root = Path(args.pin_root).expanduser()
    pin_path = resolve(pin_root, args.pin)
    pin_text = pin_path.read_text()
    pin_decls = decl_index(pin_text)
    bodies = body_index(pin_text)
    public = lp.declarations(pin_text)  # last name -> (kind, statement); public only
    port = port_index(Path(args.port_root))

    report = {"pin": str(pin_path.relative_to(pin_root)), "declarations": len(public), "rows": {}}
    print(f"{report['pin']}: {len(public)} public declarations")
    for row in args.rows:
        row_path = resolve(pin_root, row)
        text = strip_non_uses(row_path.read_text())
        used = {n for n in public if word_hit(n, text)}
        changed = True
        while changed:
            changed = False
            for d in list(used):
                for n in public:
                    if n not in used and word_hit(n, bodies.get(d, "")):
                        used.add(n)
                        changed = True
        rows = []
        for name in sorted(used):
            kind, start, span = pin_decls.get(name, ("", 0, 0))
            where = port.get(name)
            rows.append(
                {
                    "name": name,
                    "kind": kind,
                    "pin_line": start,
                    "pin_span": span,
                    "in_port": where,
                }
            )
        report["rows"][row_path.name] = rows
        missing = [r for r in rows if not r["in_port"]]
        print(
            f"\n## {row_path.name}: uses {len(used)}/{len(public)} — "
            f"{len(missing)} missing from the port, {sum(r['pin_span'] for r in missing)} pin lines"
        )
        for r in rows:
            mark = f"IN  {r['in_port']}" if r["in_port"] else "MISS"
            print(f"  {mark:40s} {r['name']:38s} pin:{r['pin_line']} +{r['pin_span']}")
    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=1))
        print(f"\njson -> {args.json}")


if __name__ == "__main__":
    main()
