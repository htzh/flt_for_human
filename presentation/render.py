#!/usr/bin/env python3
"""Render a semi-formal presentation (JSON) into a Lean worksheet.

The JSON is the source of truth; see presentation/README.md for the format and
schema.json for the machine-readable contract. The generated sheet contains:

  * the module import and the opens;
  * ``#print`` for definitions, ``#check`` for statements (``#print`` when the
    presentation asks for the proof term, ``#check (… : Prop)`` for private
    declarations whose names are not accessible outside their module);
  * every narrative — math restatement, hypotheses, proof steps, citations,
    requirements, formal notes — in comments.

Nothing in the generated sheet proves anything: it exhibits the definitions and
statements the module already has, and tells the mathematics around them.

Usage:
    python3 presentation/render.py presentation/function-field-generation/capstone.json
    python3 presentation/render.py --check-only <presentation.json>
    python3 presentation/render.py --stdout <presentation.json>
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    import jsonschema
except ImportError:  # pragma: no cover - jsonschema is present in the dev env
    jsonschema = None

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = Path(__file__).resolve().parent / "schema.json"
WIDTH = 94


class PresentationError(Exception):
    pass


# --------------------------------------------------------------------------- #
# loading and validation
# --------------------------------------------------------------------------- #


def load(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise PresentationError(f"{path}: invalid JSON: {exc}") from exc
    if data.get("format") != "flt-semiformal/1":
        raise PresentationError(
            f"{path}: unsupported format {data.get('format')!r} (want 'flt-semiformal/1')"
        )
    return data


def validate_schema(data: dict) -> None:
    if jsonschema is None:
        return
    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    validator = jsonschema.Draft202012Validator(schema)
    errors = sorted(validator.iter_errors(data), key=lambda e: list(e.path))
    if not errors:
        return
    lines = []
    for err in errors[:20]:
        where = "/".join(str(p) for p in err.path) or "<root>"
        lines.append(f"  {where}: {err.message}")
    raise PresentationError("schema validation failed:\n" + "\n".join(lines))


def index(items: list[dict], what: str) -> dict[str, dict]:
    out: dict[str, dict] = {}
    for item in items:
        ident = item.get("id")
        if not ident:
            raise PresentationError(f"{what}: item without an id")
        if ident in out:
            raise PresentationError(f"{what}: duplicate id {ident!r}")
        out[ident] = item
    return out


def check_presentation(data: dict) -> None:
    defs = index(data["definitions"], "definitions")
    prems = index(data["premises"], "premises")
    decls = index(data["declarations"], "declarations")
    group_ids = {p["group"] for p in data["premises"]}

    text_fields(data, _scan_delimiters)

    cited_premises: set[str] = set()

    def resolve(cite: dict, where: str, decl: dict, at_step: int | None = None) -> None:
        kind, ref = cite["kind"], cite["ref"]
        if kind == "premise":
            if ref not in prems:
                raise PresentationError(f"{where}: unknown premise {ref!r}")
            cited_premises.add(ref)
        if kind == "definition" and ref not in defs:
            raise PresentationError(f"{where}: unknown definition {ref!r}")
        if kind == "declaration" and ref not in decls:
            raise PresentationError(f"{where}: unknown declaration {ref!r}")
        if kind == "hypothesis":
            owned = {h["id"] for h in decl.get("hypotheses", [])}
            if ref not in owned:
                raise PresentationError(f"{where}: unknown hypothesis {ref!r}")
        if kind == "step":
            order = {s["id"]: i for i, s in enumerate(decl["proof"]["steps"])}
            if ref not in order:
                raise PresentationError(f"{where}: unknown step {ref!r}")
            if at_step is not None and order[ref] >= at_step:
                raise PresentationError(
                    f"{where}: cites step {ref!r}, which does not come earlier"
                )
        # trivial/computation/goal carry a free-form ref; nothing to resolve

    for decl in data["declarations"]:
        where = f"declaration {decl['id']}"
        if decl.get("private") and not decl.get("lean_goal"):
            raise PresentationError(f"{where}: private declaration needs lean_goal")
        proof = decl["proof"]
        if not proof["steps"]:
            raise PresentationError(f"{where}: empty proof")
        steps_seen: set[str] = set()
        for at, st in enumerate(proof["steps"]):
            sid = st["id"]
            if sid in steps_seen:
                raise PresentationError(f"{where}: duplicate step id {sid!r}")
            steps_seen.add(sid)
            for cite in st.get("cites", []):
                resolve(cite, f"{where}/{sid}/cites", decl, at)
            # a requirement may be met by a later step: the case split is stated
            # first and its cases are discharged afterwards, so no order check.
            for rq in st.get("requires", []):
                resolve(rq["met_by"], f"{where}/{sid}/requires", decl)

    for sec in data["sections"]:
        for ref in sec.get("definitions", []):
            if ref not in defs:
                raise PresentationError(f"section {sec['id']}: unknown definition {ref!r}")
        for ref in sec.get("declarations", []):
            if ref not in decls:
                raise PresentationError(f"section {sec['id']}: unknown declaration {ref!r}")
        for g in sec.get("premise_groups", []):
            if g not in group_ids:
                raise PresentationError(f"section {sec['id']}: unknown premise group {g!r}")

    # Every declaration and definition must be reachable from some section,
    # otherwise the generated sheet silently loses it.
    seen_defs = {r for s in data["sections"] for r in s.get("definitions", [])}
    seen_decls = {r for s in data["sections"] for r in s.get("declarations", [])}
    for ident in defs:
        if ident not in seen_defs:
            raise PresentationError(f"definition {ident!r} is not in any section")
    for ident in decls:
        if ident not in seen_decls:
            raise PresentationError(f"declaration {ident!r} is not in any section")
    for ident in prems:
        if ident not in cited_premises:
            raise PresentationError(
                f"premise {ident!r} is never cited by a proof step (drop it or cite it)"
            )


def text_fields(data: dict, fn) -> None:
    """Apply fn to every narrative string (schema-independent safety net)."""
    def walk(node):
        if isinstance(node, dict):
            for key, value in node.items():
                if key in {
                    "math", "math_statement", "claim", "why", "goal", "strategy",
                    "conclusion", "what", "note", "prose", "intro", "heading",
                    "role", "lean", "lean_goal", "regeneration", "formal_notes",
                    "symbol", "title", "tagline",
                }:
                    if isinstance(value, str):
                        fn(value)
                    elif isinstance(value, list):
                        for v in value:
                            if isinstance(v, str):
                                fn(v)
                else:
                    walk(value)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    walk(data)


def _scan_delimiters(text: str) -> None:
    if "/-" in text or "-/" in text:
        raise PresentationError(
            "narrative contains a Lean comment delimiter ('/-' or '-/'): " + text[:80]
        )
    if text.count("`") % 2:
        raise PresentationError(
            "narrative has an unbalanced backtick (a code span would be split): " + text[:80]
        )


# --------------------------------------------------------------------------- #
# rendering helpers
# --------------------------------------------------------------------------- #


CODE_OR_BOLD = re.compile(r"(`[^`]*`|\*\*[^*]*\*\*)([.,;:!?)\]]*)")


def _wrap_paragraph(para: str, width: int, indent: str) -> list[str]:
    """Wrap one paragraph without breaking inside a code span or a bold span.

    A span longer than the width is placed on its own line: an intact span is
    worth more than a short line, because a split span breaks the markdown.
    """
    tokens: list[str] = []
    pos = 0
    for m in CODE_OR_BOLD.finditer(para):
        if m.start() > pos:
            tokens.extend(para[pos:m.start()].split())
        tokens.append(m.group(0))
        pos = m.end()
    if pos < len(para):
        tokens.extend(para[pos:].split())
    if not tokens:
        return [indent.rstrip()]
    out: list[str] = []
    cur = indent
    for tok in tokens:
        if not cur.strip():
            cur = indent + tok
        elif len(cur) + 1 + len(tok) <= width:
            cur += " " + tok
        else:
            out.append(cur)
            cur = indent + tok
    if cur.strip():
        out.append(cur)
    return out


def wrap(text: str, width: int = WIDTH, indent: str = "") -> list[str]:
    """Wrap prose, preserving blank lines and pre-indented (display) lines."""
    lines: list[str] = []
    for para in text.split("\n"):
        if not para.strip():
            lines.append("")
            continue
        if para.startswith("    "):
            lines.append(indent + para)
            continue
        lines.extend(_wrap_paragraph(para, width, indent))
    return lines


def comment(body: list[str], indent: int = 0) -> list[str]:
    """A Lean block comment.

    Prose is emitted at column 0 so the Play reader's Markdown parser does not
    mistake a 2+-space-indented run for an indented code block (which would kill
    the links in the citations). The header is the exception: its metadata lines
    must start with two spaces for the worksheet parser.
    """
    pad = " " * indent
    out = ["/-"]
    for line in body:
        out.append((pad + line).rstrip() if line else "")
    out.append("-/")
    return out


def indent_lines(lines: list[str], prefix: str = "  ") -> list[str]:
    return [prefix + line if line else line for line in lines]


def bullet(lines: list[str], marker: str = "- ") -> list[str]:
    """Turn wrapped text into a bullet item with hanging indent."""
    out = []
    for i, line in enumerate(lines):
        if i == 0:
            out.append(marker + line)
        elif line:
            out.append(" " * len(marker) + line)
        else:
            out.append("")
    return out


def para(text: str, width: int = WIDTH) -> list[str]:
    """Wrapped paragraph lines."""
    return wrap(text, width=width)


def render_header(data: dict) -> list[str]:
    w = data["worksheet"]
    body: list[str] = []
    title = w.get("title", data["subject"])
    tagline = w.get("tagline", "")
    body.append(f"PLAY · {title}" + (f" — {tagline}" if tagline else ""))
    body.append("=" * 76)
    body.append("")
    source_json = w.get("source_json", "<presentation.json>")
    meta = [
        ("Subject", data["subject"]),
        ("Reads", w.get("reads", data["module"])),
        ("Pin", w.get("pin", "")),
        ("Check", w.get("check", "")),
        ("Status", f"generated — do not edit; edit {source_json}"),
        ("Date", w.get("date", "")),
        ("Intro", w.get("intro", "")),
    ]
    for label, value in meta:
        if not value:
            continue
        lines = wrap(value, width=WIDTH - 13)
        if not lines:
            continue
        body.append(f"{label:<9} {lines[0]}" if lines[0] else f"{label:<9}")
        for line in lines[1:]:
            body.append(f"{'':10}{line}")
    body.append("")
    body.append("Zones")
    for sec in data["sections"]:
        tag = sec.get("tagline", "")
        body.append(f"  {sec['id']:<3}{sec['title']}" + (f"   ({tag})" if tag else ""))
    body.append("")
    for line in para(
        "This sheet is generated. Everything below is a comment except for the import, "
        "the opens, the `#check`s and the `#print`s; those exhibit the definitions and "
        "statements of the module and compile against it. The mathematics is the "
        "presentation: what is to be proved, what each hypothesis supplies, and which "
        "proven theorem or earlier step meets each premise."
    ):
        body.append(line)
    body.append("")
    body.append(f"Regenerate with: python3 presentation/render.py {source_json}")
    return comment(body, indent=2)


def render_preamble(data: dict) -> list[str]:
    w = data["worksheet"]
    out = [f"import {w['import']}", ""]
    for key, value in (w.get("options") or {}).items():
        out.append(f"set_option {key} {str(value).lower() if isinstance(value, bool) else value}")
    out += ["", "noncomputable section", ""]
    if w.get("opens"):
        out.append("open " + " ".join(w["opens"]))
    if w.get("scoped"):
        out.append("open scoped " + " ".join(w["scoped"]))
    if w.get("opens") or w.get("scoped"):
        out.append("")
    return out


def cite_label(cite: dict, decl: dict, defs: dict, prems: dict, decls: dict) -> str:
    kind, ref = cite["kind"], cite["ref"]
    if kind == "hypothesis":
        for h in decl.get("hypotheses", []):
            if h["id"] == ref:
                return f"`{h['lean']}`"
        return f"hypothesis {ref}"
    if kind == "premise":
        p = prems[ref]
        # The Lean name is the link target in the Play reader (a backticked code
        # span opens the declaration's card in the side panel). The mnemonic
        # label is kept only when it is not just the short name.
        suffix = "" if p["name"].endswith(p["label"]) else f" ({p['label']})"
        return f"`{p['name']}`{suffix}"
    if kind == "step":
        return f"step {ref}"
    if kind == "definition":
        return f"`{defs[ref]['name']}`"
    if kind == "declaration":
        d = decls[ref]
        return f"`{d['name']}`"
    if kind == "trivial":
        return f"trivial ({ref})"
    if kind == "computation":
        return f"computation ({ref})"
    if kind == "goal":
        return "the goal"
    return f"{kind} {ref}"


def render_conventions(data: dict) -> list[str]:
    body: list[str] = ["## Conventions", "", "The notation shared by every proof below."]
    for c in data.get("conventions", []):
        line = f"**{c['symbol']}** — {c['math']}"
        if c.get("lean"):
            line += f" Lean: `{c['lean']}`."
        body += ["", *bullet(para(line, width=WIDTH - 6), "  - ")]
    return comment(body)


def render_definition(d: dict) -> list[str]:
    body: list[str] = [f"### {d.get('heading', d['name'])}", "",
                       f"**Lean.** `{d['name']}` ({d['kind']})", ""]
    body += para(d["math"])
    if d.get("note"):
        body += ["", *para(d["note"])]
    if d.get("file"):
        body += ["", f"Source: `{d['file']}:{d.get('line', 0)}`."]
    out = comment(body)
    mode = d.get("render", "print")
    if mode == "check":
        out.append(f"#check @{d['name']}")
    elif mode == "print":
        out.append(f"#print {d['name']}")
    out.append("")
    return out


def render_declaration(decl: dict, defs, prems, decls) -> list[str]:
    out: list[str] = []
    head: list[str] = [
        f"### {decl['heading']}",
        "",
        f"**Lean name.** `{decl['name']}` ({decl['kind']})",
        "",
    ]
    head += para("**Mathematically.** " + decl["math_statement"])
    head += ["", *para("**Role.** " + decl["role"])]
    if decl.get("provenance", {}).get("flt"):
        head += ["", *para("**Provenance.** " + decl["provenance"]["flt"])]
    if decl.get("hypotheses"):
        head += ["", "**Hypotheses.**"]
        for h in decl["hypotheses"]:
            head += bullet(para(f"`{h['lean']}` — {h['math']}", width=WIDTH - 4), "  - ")
    out += comment(head)

    if decl.get("private"):
        # The Play parser reads a `#check` as a single line; keep the closed
        # proposition on one line so the app builder sees the whole expression.
        goal = " ".join(decl["lean_goal"].split())
        out.append("#check (" + goal + ")")
    elif decl.get("print"):
        out.append(f"#print {decl['name']}")
    else:
        out.append(f"#check @{decl['name']}")
    out.append("")

    sig: list[str] = ["**Lean statement.**", "", "```lean", *decl["lean"].split("\n"), "```", ""]
    sig += para("**To prove (mathematical restatement).** " + decl["proof"]["goal"])
    sig += ["", *para("**Strategy.** " + decl["proof"]["strategy"])]
    out += comment(sig)

    for st in decl["proof"]["steps"]:
        body: list[str] = [f"**Step {st['id']} ({st['kind']}).** {st['claim']}"]
        if st.get("math"):
            body += ["", *para(st["math"], width=WIDTH - 2)]
        if st.get("why"):
            body += ["", *para("*Why.* " + st["why"], width=WIDTH - 2)]
        if st.get("cites"):
            body += ["", "*Cites.*"]
            for c in st["cites"]:
                line = cite_label(c, decl, defs, prems, decls)
                if c.get("math"):
                    line += " — " + c["math"]
                body += bullet(para(line, width=WIDTH - 6), "  - ")
        if st.get("requires"):
            body += ["", "*Requires.*"]
            for rq in st["requires"]:
                met = cite_label(rq["met_by"], decl, defs, prems, decls)
                body += bullet(para(f"{rq['what']} — met by {met}", width=WIDTH - 6), "  - ")
        if st.get("lean"):
            body += ["", "  ```lean", "  " + st["lean"], "  ```"]
        out += comment(body)

    tail: list[str] = para("**Conclusion.** " + decl["proof"]["conclusion"])
    if decl["proof"].get("regeneration"):
        tail += ["", "**For a regenerating reader.**"]
        for hint in decl["proof"]["regeneration"]:
            tail += bullet(para(hint, width=WIDTH - 6), "  - ")
    if decl["proof"].get("formal_notes"):
        tail += ["", "**Formal notes (not mathematics).**"]
        for note in decl["proof"]["formal_notes"]:
            tail += bullet(para(note, width=WIDTH - 6), "  - ")
    out += comment(tail)
    return out


def render_premise(p: dict) -> list[str]:
    body: list[str] = [f"### `{p['label']}` — {p['name']}", ""]
    body += para(p["math"])
    if p.get("note"):
        body += ["", *para(p["note"])]
    if p.get("url"):
        body += ["", f"Source: <{p['url']}>."]
    elif p.get("file"):
        loc = p["file"] + (f":{p['line']}" if p.get("line") else "")
        body += ["", f"Source: `{loc}`."]
    if p.get("pin"):
        body += ["", f"Pinned FLT: `{p['pin']}`."]
    out = comment(body)
    if p["kind"] == "def":
        out.append(f"#print {p['name']}")
    else:
        out.append(f"#check @{p['name']}")
    out.append("")
    return out


def render(data: dict) -> str:
    defs = {d["id"]: d for d in data["definitions"]}
    prems = {p["id"]: p for p in data["premises"]}
    decls = {d["id"]: d for d in data["declarations"]}
    lines: list[str] = []
    lines += render_header(data)
    lines.append("")
    lines += render_preamble(data)
    if data.get("conventions"):
        lines += render_conventions(data)
        lines.append("")

    for sec in data["sections"]:
        zbody: list[str] = [f"## Zone {sec['id']} — {sec['title']}"]
        if sec.get("tagline"):
            zbody += ["", *para(sec["tagline"]), ""]
        if sec.get("prose"):
            for i, chunk in enumerate(sec["prose"].split("\n\n")):
                if i:
                    zbody.append("")
                zbody += para(chunk)
        lines += comment(zbody)
        lines.append("")
        for ref in sec.get("definitions", []):
            lines += render_definition(defs[ref])
        for ref in sec.get("declarations", []):
            lines += render_declaration(decls[ref], defs, prems, decls)
        for group in sec.get("premise_groups", []):
            titles = {
                "port": "port theorems cited",
                "mathlib": "mathlib lemmas used",
            }
            lines += comment(["### " + titles.get(group, group), "",
                              "The statement below is the compiler's, via `#check`."])
            lines.append("")
            for p in data["premises"]:
                if p["group"] == group:
                    lines += render_premise(p)

    lines += [""]
    lines += comment(
        [
            "End of the presentation.",
            "",
            "Every mathematical claim above is either the statement of a declaration in the",
            "imported module (exhibited by #check/#print) or a step of the semi-formal proof",
            "that cites such a declaration. The JSON source is the document; this sheet is a",
            "projection of it.",
        ]
    )
    lines += ["", "end", ""]
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("presentation", type=Path)
    ap.add_argument("--out", type=Path, default=None, help="output path (default: worksheet.output)")
    ap.add_argument("--stdout", action="store_true", help="print the sheet instead of writing")
    ap.add_argument("--check-only", action="store_true", help="validate, do not render")
    args = ap.parse_args(argv)

    try:
        data = load(args.presentation)
        validate_schema(data)
        check_presentation(data)
        if args.check_only:
            print(f"ok: {args.presentation} ({len(data['declarations'])} declarations, "
                  f"{len(data['definitions'])} definitions, {len(data['premises'])} premises)")
            return 0
        text = render(data)
        if args.stdout:
            sys.stdout.write(text)
            return 0
        # The default output is repository-relative, so the renderer works from
        # any cwd (publish.sh may be invoked from outside the repo).
        out = args.out or (ROOT / data["worksheet"]["output"])
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding="utf-8")
        print(f"wrote {out} ({len(text.splitlines())} lines)")
        return 0
    except PresentationError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
