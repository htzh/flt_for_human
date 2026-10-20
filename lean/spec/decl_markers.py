#!/usr/bin/env python3
"""decl_markers.py — the central declaration-level exceptions for `check_port.py`.

`spec-pin:` stays in the module header (it is the module's wire).  The
*declaration-level* exceptions — a `pin:` rename/extra-source marker or an `own:`
tier-2 reason — can now live here instead of above the declaration in the source,
so the Lean files stay free of checker metadata.  Existing in-source markers keep
working; an entry here takes precedence over one in the source.

Format (TSV, `#` comments and blank lines allowed):

    module                          declaration                       directive
    FLTForHuman/X.lean              ModularCurve.foo                  pin: KwFoo (P2M/Sol/S_X.lean:12)
    FLTForHuman/X.lean              ModularCurve.bar                  own: port-own helper

`declaration` is the full importable name the checker parses (namespace prefix
included).  `directive` uses the same `pin:` / `own:` syntax as the source
comment, with or without the leading `--`.  A `pin:` file is added to the
module's wire, exactly as an in-source marker is; `own:` is tier 2.  Write the
pin file as the corpus-relative path (`P2M/Sol/...`), not a bare basename.

Changing this file never affects a Lean build.  The checker reports entries that
no longer match a declaration as `STALE MARKER` (a warning; `--strict-markers`
turns it into a failure).
"""
from __future__ import annotations

import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT = HERE / "decl_markers.tsv"

PIN_DIRECTIVE = re.compile(
    r"^pin:\s*`?([\w.'\u2080-\u209c]+)`?(?:\s*\(([^):\s]+)(?::(\d+))?\))?\s*$")
OWN_DIRECTIVE = re.compile(r"^own:\s*(.+?)\s*$")


def parse_directive(text: str) -> tuple[str, dict]:
    """('pin', {name,file,line}) or ('own', {reason}) from a directive string."""
    text = text.strip()
    if text.startswith("--"):
        text = text[2:].strip()
    m = PIN_DIRECTIVE.match(text)
    if m:
        return "pin", {"name": m.group(1), "file": m.group(2),
                       "line": int(m.group(3)) if m.group(3) else None}
    m = OWN_DIRECTIVE.match(text)
    if m:
        return "own", {"reason": m.group(1)}
    raise ValueError(f"not a pin:/own: directive: {text!r}")


def load(path: Path | str = DEFAULT) -> dict[str, dict[str, tuple[str, dict]]]:
    """module -> full declaration name -> (kind, parsed directive)."""
    path = Path(path)
    if not path.exists():
        return {}
    out: dict[str, dict[str, tuple[str, dict]]] = {}
    with path.open(encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            if line.startswith("module\t"):
                continue
            parts = line.split("\t")
            if len(parts) != 3:
                raise ValueError(f"{path}:{lineno}: expected 3 tab-separated "
                                 f"columns (module, declaration, directive)")
            module, decl, directive = (p.strip() for p in parts)
            if not module or not decl:
                raise ValueError(f"{path}:{lineno}: empty module or declaration")
            if module not in out:
                out[module] = {}
            if decl in out[module]:
                raise ValueError(f"{path}:{lineno}: duplicate marker for "
                                 f"{module} :: {decl}")
            out[module][decl] = parse_directive(directive)
    return out


def marker_files(entries: dict[str, tuple[str, dict]]) -> list[str]:
    """Pin files named by the markers of one module, in first-seen order."""
    files = []
    for kind, payload in entries.values():
        if kind == "pin" and payload.get("file"):
            files.append(payload["file"])
    return list(dict.fromkeys(files))
