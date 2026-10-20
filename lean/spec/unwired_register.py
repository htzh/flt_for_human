#!/usr/bin/env python3
"""unwired_register.py — the port's public-but-unchecked surface, with pin provenance.

Why this file exists
--------------------
The port has three tiers of public declaration:

  1. **checked**  -- the module is in the checker's `PORT_FILES`, or carries its
     own `spec-pin:` header (the per-module wire `spec/check_port.py` reads), so
     the declaration is diffed against the pinned FLT source;
  2. **own**      -- listed in `OWN_PROOFS`: the port's own statement, no pin
     source, deliberately not diffed;
  3. **unwired**  -- public in the port tree, in a module that has *neither* a
     `PORT_FILES` entry nor a `spec-pin:` header: built, importable, and with no
     statement diff at all.

Tier 3 is a deliberate economy, not an oversight.  A module can hold a whole
development whose API no consumer has needed yet -- `Elliptic/TorsionCard.lean` is
the `card_torsion_of_isAlgClosed` home, kept out while only its two aliases are
diffed -- and wiring it costs a `spec-pin:` header plus a review of the delta,
which is verification nobody asked for until a consumer exists.

The cost of that economy is discoverability: a future proof looking for a
substitute cannot see what tier 3 holds, and the reason a module is unlisted lives
in a comment in the checker.  This tool emits the register --

    lean/spec/UNWIRED-PUBLIC.md

-- one row per public declaration of every unlisted module, and, in a listed
module, per declaration the checker exempts as tier 3 (a `-- pin:` marker into a pin
file `SOURCES` does not read, with no `SOURCES` counterpart), each with the **pin
original** (the name and file the statement must be diffed against when it is
wired).  A consumer greps the register for the mathematics it wants, reads the pin
file for the signature, and the manager wires that module (or that declaration) on
demand.

This file is published: it lives next to the checker it reads, and it depends on
nothing outside this directory except the pin clone.  (The same provenance read
also backs `registry()`, the pin<->port map the unpublished `tools/deps/` node
walkers consult; they load this file, not a copy of it.)  The register it writes
is generated data and is git-ignored.

The pin side is read from the statement corpus (`spec/statement_db.py`,
`tmp/flt-statements/`), not from a cache of this tool's own: the corpus is the
one scan of the pin, it carries the normalised statement hash this tool matches
on, and its `.idx` gives each `SOURCES` file's declarations as a byte range.  The
port side is re-read on every run, because that is what `--check` is for.  The
statement checker is untouched by this: it stays published and does its own live
scan.

Usage
-----
    python3 spec/statement_db.py build             # once, after a re-pin
    python3 spec/unwired_register.py                # write the register
    python3 spec/unwired_register.py --check        # exit 1 if it is stale
    python3 spec/unwired_register.py --json tmp/flt-statements/unwired.json
    python3 spec/unwired_register.py --rebuild      # rebuild the corpus first
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent          # lean/spec/
LEAN = HERE.parent                              # lean/
REPO = LEAN.parent
CHECKER_PATH = HERE / "old_check_stmts.py"   # frozen; read, never edited as a registry
REGISTER = HERE / "UNWIRED-PUBLIC.md"
PIN = Path.home() / "proj" / "fermats-last-theorem"
LIBS = ("FLTForHuman", "Reserve")
PIN_SHA = "aa2d8b3"
# Generated data lives only in the repo's scratch tree, never next to the sources.
sys.path.insert(0, str(HERE))
import statement_db  # noqa: E402  (the one scan of the pin; see its docstring)

JSON_DEFAULT = statement_db.CACHE / "unwired.json"

CHECKER = None  # set in main() / registry()


def load_checker(path: Path = CHECKER_PATH):
    if not path.exists():
        sys.exit(f"unwired_register: cannot find the statement checker at {path}")
    spec = importlib.util.spec_from_file_location("_unwired_checker", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def source_list(checker) -> list[str]:
    """The pin files `SOURCES` reads, in the checker's order (first occurrence).

    Order matters: `pin original` takes the first candidate whose kind and
    statement match, and the checker's `SOURCES` order is what decides between two
    pin files that carry the same statement.
    """
    text = CHECKER_PATH.read_text(encoding="utf-8")
    m = re.search(r"^SOURCES = \[(.*?)^\]", text, re.S | re.MULTILINE)
    if not m:
        sys.exit("unwired_register: cannot find SOURCES in the checker")
    return list(dict.fromkeys(re.findall(r'"([^"]+)"', m.group(1))))


def port_files(checker) -> set[str]:
    """The checker's own list, read from the file so the register cannot drift."""
    text = CHECKER_PATH.read_text(encoding="utf-8")
    m = re.search(r"^PORT_FILES = \[(.*?)^\]", text, re.S | re.MULTILINE)
    if not m:
        sys.exit("unwired_register: cannot find PORT_FILES in the checker")
    return set(re.findall(r'^\s*"([^"]+)"', m.group(1), re.MULTILINE))


def flat_code(text: str) -> str:
    """`text` with block comments blanked, newlines kept, so line numbers survive.

    The checker's `raw_declarations` drops block comments before matching, so a
    `theorem` inside a docstring is not a declaration there; the register needs
    the same judgement *and* the original line numbers, which a plain
    `re.sub(..., " ", ...)` would destroy.  Replacing each comment by its own
    newlines keeps both.  (Nested `/- -/` is beyond the checker too.)
    """
    return re.sub(
        r"/-.*?-/",
        lambda m: "\n" * m.group(0).count("\n"),
        text,
        flags=re.DOTALL,
    )


def scan_declarations(text: str) -> list[dict]:
    """(name, kind, line, private) for every declaration, with its line number.

    Uses the checker's own `DECL_RE`/`ENCLOSE_RE`, so the register and the
    checker cannot disagree about *which* declarations exist -- the older
    `tools/deps/port_graph.py` scanner could (it sees `protected`/`inductive`,
    which the checker does not, and that mismatch forced a fallback path).

    Only the frame stack differs from `raw_declarations`: this walk is
    line-oriented because a declaration's *line* is what attaches a `-- pin:`
    comment to it.
    """
    code = flat_code(text)
    stack: list[str | None] = []
    out: list[dict] = []
    for i, line in enumerate(code.split("\n"), 1):
        m = CHECKER.ENCLOSE_RE.match(line)
        if m:
            if m.group("ns"):
                stack.append(m.group("nsname"))
            elif m.group("mut") or m.group("sec"):
                # a `section`/`mutual` opens a frame that a later `end` closes,
                # but contributes nothing to a declaration's name
                stack.append(None)
            elif stack:
                stack.pop()
        d = CHECKER.DECL_RE.match(line)
        if not d:
            continue
        prefix = ".".join(n for n in stack if n)
        name = d.group("name").rsplit(".", 1)[-1]
        out.append({
            "name": name,
            "qual": f"{prefix}.{name}" if prefix else name,
            "kind": d.group("kind"),
            "line": i,
            "private": "private" in d.group("mods"),
        })
    return out


def corpus_tables(db, sources: list[str]):
    """The checker's pin lookup tables, built from the statement corpus.

    `(maps, provided)` where `maps = (source, dotted, stripped)` and every candidate
    is `(kind, nhash, pin_file, line)`:

    * `source[last]`  -- first *public* declaration of that last name in each file,
      in `SOURCES` order (the checker's own `declarations()` rule);
    * `dotted[key]`   -- every declaration under its `promoted_key`, and under the
      bare last name (the checker's dotted fallback registers both);
    * `stripped[key]` -- every `kw_`-stripped last name;
    * `provided[last]` -- the statement hashes of every declaration of that name,
      public *and* private (a private counterpart still counts as provided).

    Matching is by `nhash`, the corpus's hash of the checker-normalised statement,
    which is exactly what `pin_original` compares; the port side hashes its own
    normalised statement with `statement_db.nhash`.
    """
    origin: dict[str, list] = defaultdict(list)
    dotted: dict[str, list] = defaultdict(list)
    stripped: dict[str, list] = defaultdict(list)
    provided: dict[str, set] = defaultdict(set)
    for rel in sources:
        seen: set[str] = set()
        for row in db.file(rel):
            last = row["last"]
            if not last:                       # an anonymous instance has no name
                continue
            h, kind = row["nhash"], row["kind"]
            provided[last].add(h)
            if not row["private"] and last not in seen:
                seen.add(last)
                origin[last].append((kind, h, rel, row["line"]))
            for key in (CHECKER.promoted_key(row["name"]), CHECKER.promoted_key(last)):
                dotted[key].append((kind, h, rel, row["line"]))
            s = CHECKER.strip_pin_prefix(last)
            if s:
                stripped[s].append((kind, h, rel, row["line"]))
    return (origin, dotted, stripped), provided


def pin_original(name, kind, hsh, maps):
    """(pin file, pin name, how, line) for a port declaration, or None."""

    def find(cands):
        for c in cands or ():
            if c[0] == kind and c[1] == hsh:
                return c
        return None

    hit = find(maps[0].get(name))
    if hit:
        return hit[2], name, "direct name", hit[3]
    for key in (CHECKER.promoted_key(name), name):
        hit = find(maps[1].get(key))
        if hit:
            return hit[2], name, "dotted", hit[3]
    hit = find(maps[2].get(name))
    if hit:
        return hit[2], CHECKER.strip_pin_prefix(name) or name, "prefix-stripped", hit[3]
    return None


def pin_rel(pin: Path, rel: str) -> str:
    """A provenance comment names the file by basename; find where it lives."""
    for sub in ("P2M/Sol", "Theorems", "Definitions", ""):
        cand = f"{sub}/{rel}" if sub else rel
        if (pin / cand).exists():
            return cand
    return rel


def pin_line(db, rel: str, name: str) -> int | None:
    """The line of a pin declaration, for a marker that names its file and not its line."""
    for row in db.file(rel):
        if row["name"] == name or row["last"] == name:
            return row["line"]
    return None


# The new wire: a module with `spec-pin:` lines is checked by `spec/check_port.py`,
# whether or not the frozen checker still lists it.  Such a module has no tier-3
# declarations -- the new checker requires every public one to be accounted for.
SPEC_PIN = re.compile(r"^[ \t]*spec-pin:", re.M)

PIN_COMMENT = re.compile(
    r"--\s*pin:\s*([\w.'\u2080-\u209c]+)(?:\s*\(([^):\s]+)(?::(\d+))?\))?")


def dotted_names(text: str) -> list[tuple[int, str]]:
    """(line, enclosing namespace) for every namespace/section frame change.

    The register must give the *importable* name, so the enclosing frame at each
    declaration line is tracked -- a bare `theorem foo` inside `namespace X` is
    `X.foo` to a consumer.  Uses the checker's `ENCLOSE_RE` (so `mutual` closes
    the frame it opened) on the comment-blanked text (so a docstring cannot
    invent a namespace).
    """
    out: list[tuple[int, str]] = []
    stack: list[str] = []
    for i, line in enumerate(flat_code(text).split("\n"), 1):
        m = CHECKER.ENCLOSE_RE.match(line)
        if not m:
            continue
        if m.group("ns"):
            stack.append(m.group("nsname"))
        elif m.group("mut") or m.group("sec"):
            # a `section` -- named or not -- never contributes to a declaration's
            # name, but some later `end` closes its frame: push a placeholder so the
            # pop/push balance holds and the real namespace survives
            stack.append("")
        elif stack:
            stack.pop()
        out.append((i, ".".join(n for n in stack if n)))
    return out


def dotted_at(events: list[tuple[int, str]], line: int) -> str:
    cur = ""
    for ln, ns in events:
        if ln < line:
            cur = ns
        else:
            break
    return cur


def survey(lean: Path, db):
    listed = port_files(CHECKER)
    sources = source_list(CHECKER)
    maps, provided = corpus_tables(db, sources)
    unlisted: dict[str, list] = {}
    for lib in LIBS:
        for p in sorted((lean / lib).rglob("*.lean")):
            if ".lake" in p.parts:
                continue
            rel = p.relative_to(lean).as_posix()
            text = p.read_text(encoding="utf-8")
            wired_here = bool(SPEC_PIN.search(text))
            is_listed = rel in listed or wired_here
            decls = CHECKER.raw_declarations(text)
            if not decls:
                continue
            meta = scan_declarations(text)
            events = dotted_names(text)
            # Index by (bare name, kind) and consume in source order. A bare name
            # can repeat across namespaces -- a pin-named declaration and its
            # promoted alias, e.g. `BridgeX.foo` / `TateCurve.foo` -- and
            # `raw_declarations` returns a bare `raw` for the alias, so a
            # name-keyed dict hands the alias the other copy's line and namespace.
            by_nk: dict[tuple[str, str], list] = defaultdict(list)
            for d in meta:
                if not d["private"]:
                    by_nk[(d["name"], d["kind"])].append(d)
            cursor: dict[tuple[str, str], int] = defaultdict(int)
            src = text.split("\n")
            rows = []
            for raw, kind, stmt in decls:
                nm = raw.rsplit(".", 1)[-1]
                lst = by_nk.get((nm, kind), [])
                i = cursor[(nm, kind)]
                cursor[(nm, kind)] = i + 1
                d = lst[i] if i < len(lst) else (lst[-1] if lst else None)
                ns = dotted_at(events, d["line"]) if d and d.get("line") else ""
                # A declaration written `theorem _root_.A.B.foo` inside a namespace
                # is *absolutely* named `A.B.foo`; the enclosing frame must not be
                # prefixed (the checker's own `promoted_key` strips `_root_.` the
                # same way).  Without this the register lists a name no consumer
                # can resolve.
                if "_root_." in raw:
                    # `raw_declarations` prefixes the enclosing namespace, so
                    # `A.B._root_.C.D.foo` is absolutely named `C.D.foo` -- take the
                    # name after `_root_.`, do not substitute in place (that would
                    # double the prefix: `A.B.C.D.foo`).
                    dotted = raw.rsplit("_root_.", 1)[-1]
                else:
                    dotted = f"{ns}.{nm}" if ns else nm
                hsh = statement_db.nhash(stmt)
                pin = pin_original(nm, kind, hsh, maps)
                if d and d.get("line"):
                    # Nearest comment first: a declaration directly under its own
                    # `-- pin:` line must not inherit the previous declaration's.
                    for prev in reversed(src[max(0, d["line"] - 4):d["line"] - 1]):
                        m = PIN_COMMENT.search(prev)
                        if m:
                            pin = (m.group(2) or (pin[0] if pin else ""),
                                   m.group(1),
                                   "provenance comment",
                                   int(m.group(3)) if m.group(3) else None)
                            break
                rows.append({
                    "name": nm, "qual": raw, "kind": kind,
                    "dotted": dotted, "pin": pin,
                    "provided": hsh in provided.get(nm, ()),
                })
            if is_listed and wired_here:
                # Owned by `spec/check_port.py`: it diffs every public declaration
                # against the module's own `spec-pin:` wire (or a marker, or an
                # `-- own:` exemption), so nothing here is tier 3.
                continue
            if is_listed:
                # A listed module's wire is what the checker diffs.  A public declaration that
                # carries a `-- pin:` marker naming a pin file `SOURCES` does *not* read is
                # exempted by the checker (its `UNWIRED` tier 3, reported as
                # "registered-unwired declarations exempted") and belongs here; a marker into a
                # file `SOURCES` does read is a diff, and a marker-less declaration is either
                # diffed by name or an `OWN_PROOFS` statement -- neither belongs in tier 3.
                rows = [r for r in rows
                        if r["pin"] and r["pin"][2] == "provenance comment"
                        and r["pin"][1] not in sources
                        and not r["provided"]]
                if not rows:
                    continue
            unlisted[rel] = rows
    importers: dict[str, int] = defaultdict(int)
    consumers: dict[str, int] = defaultdict(int)
    every = [p for lib in LIBS for p in sorted((lean / lib).rglob("*.lean"))
             if ".lake" not in p.parts]
    every += sorted((lean / "spec").rglob("*.lean"))
    for p in every:
        text = p.read_text(encoding="utf-8", errors="replace")
        here = p.relative_to(lean).as_posix()
        for rel in unlisted:
            if here == rel:
                continue
            dotted = rel[:-len(".lean")].replace("/", ".")
            if f"import {dotted}" in text:
                (consumers if here.startswith("spec/") else importers)[rel] += 1
    return unlisted, importers, consumers


def registry(lean: Path, pin: Path, rebuild: bool = False, tsv=None):
    """The tier-3 pin<->port provenance map, for the node-walking tools.

    `survey` already computes, for every public declaration of an unlisted module,
    the pin declaration it was transcribed from.  This exposes that mapping in the
    two directions the other tools want:

    * ``by_port[port_dotted] -> {pin_name, pin_file, pin_line, module, how}`` — what
      a port declaration found in the tree is, and where it came from;
    * ``by_pin[pin_name] -> port_dotted`` — whether a pin declaration is already in
      the port at tier 3, including copies whose *port* name differs from the pin's.

    It is deliberately derived from the same `survey` as `UNWIRED-PUBLIC.md`, so the
    tools and the register cannot disagree about the tier-3 surface.
    """
    global CHECKER
    if CHECKER is None:
        CHECKER = load_checker()
    db = statement_db.Statements(tsv or statement_db.TSV_DEFAULT)
    unlisted, _, _ = survey(lean, db)
    by_port: dict[str, dict] = {}
    by_pin: dict[str, str] = {}
    for rel, rows in unlisted.items():
        for r in rows:
            p = r.get("pin")
            if not p:
                continue
            pin_file, pin_name, how, pin_line = (list(p) + [None] * 4)[:4]
            by_port[r["dotted"]] = {
                "pin_name": pin_name,
                "pin_file": pin_file,
                "pin_line": pin_line,
                "how": how,
                "module": rel,
            }
            if pin_name:
                by_pin.setdefault(pin_name, r["dotted"])
    return by_port, by_pin


def render(unlisted, importers, consumers, lean: Path, pin: Path, db) -> str:
    total = sum(len(v) for v in unlisted.values())
    with_pin = sum(1 for v in unlisted.values() for d in v if d["pin"])
    out = [
        "# The unwired public surface",
        "",
        "Public declarations of the port that the statement checker does not cover:",
        "those of a module that is neither listed in the frozen checker's `PORT_FILES`",
        "nor wired by its own `spec-pin:` lines (the new checker owns those),",
        "and, in a listed module, those that carry a `-- pin:` marker into a pin file",
        "`SOURCES` does not read and that no `SOURCES` counterpart provides (the",
        "checker's `UNWIRED` exemption).  They are built and importable — this register",
        "is so that a future proof can *find* them, and so that their statements are one",
        "step from being diffed.",
        "",
        "Generated by `spec/unwired_register.py` (git-ignored; run it with `--check` to",
        "see whether the tree has drifted).  Nothing here is verified against the pin:",
        "the `pin original` column names the declaration (and the file holding it) that",
        "carries the statement to diff when the entry is wired.",
        "",
        f"`{total}` public declarations in `{len(unlisted)}` unlisted modules; "
        f"`{with_pin}` of them have a pin counterpart by name and statement.",
        "",
        "This is tier 3 only.  Tier 2 — a declaration in a *listed* module that the",
        "checker skips for another reason — is `OWN_PROOFS` in the checker itself, each",
        "entry carrying its reason; tier 1 is the checked surface.",
        "",
        "**To wire one** (or a whole module): give the module a leading `/- … -/` header with",
        "one `spec-pin: <pin file>` line per pin source — the `Theorems/` wrapper for a",
        "headline, the `P2M/Sol/S_` file for a transcribed proof — and run",
        "`python3 spec/check_port.py --force <module>`; reconcile its `ok` delta against the",
        "new public surface.  A port name that is not the pin's is matched through a",
        "`pin:`/`own:` entry in `spec/decl_markers.tsv`, the `kw_` prefix strip or the dotted",
        "fallback; if none of them reaches it the checker reports it and the entry records",
        "the pin original.  Then delete the entry here.  (`PORT_FILES`/`SOURCES` in",
        "`spec/old_check_stmts.py` are the grandfathered registry: do not append to them.)",
        "",
        "Names are the port's own (mathlib style); the pin original is recovered from",
        "a `-- pin: <name> (<file>:<line>)` comment above a transcribed declaration,",
        "falling back to the checker's own name/statement lookup for declarations that",
        "still carry the pin's name.",
        "",
        "**To use one**: read its `pin original` file for the signature.  The pin clone",
        f"is public at `github.com/anthropics/fermats-last-theorem` pinned `{PIN_SHA}`",
        "(raw URLs stay correct when the content is quoted; `Theorems/` pages carry the",
        "wrappers whose statements the checker diffs).",
        "",
    ]
    # summary first: which modules are transcribed-but-unwired, and which are the
    # port's own; the first kind is the substitute list the register exists for
    out += [
        "## Summary",
        "",
        "| module | lines | public | transcribed | own | imported by | in `spec/` |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for rel in sorted(unlisted):
        decls = unlisted[rel]
        n = len((lean / rel).read_text(encoding="utf-8").split("\n"))
        tr = sum(1 for d in decls if d["pin"])
        out.append(f"| [`{rel}`](#{rel.lower().replace('/', '').replace('.', '').replace('_', '-')}) "
                   f"| {n:,} | {len(decls)} | {tr} | {len(decls) - tr} "
                   f"| {importers.get(rel, 0)} | {consumers.get(rel, 0)} |")
    out.append("")
    for rel in sorted(unlisted):
        decls = unlisted[rel]
        n = len((lean / rel).read_text(encoding="utf-8").split("\n"))
        tr = sum(1 for d in decls if d["pin"])
        kind = ("transcribed from the pin, not wired" if tr
                else "the port's own, no pin source")
        out += [
            f"## `{rel}`",
            "",
            f"{n:,} lines, {len(decls)} public declarations — {kind}. Imported by "
            f"{importers.get(rel, 0)} port module(s)"
            + (f", and used by {consumers[rel]} `spec/` consumer(s)" if consumers.get(rel) else "")
            + ".",
            "",
            "| importable name | kind | pin original | pin file |",
            "|---|---|---|---|",
        ]
        for d in sorted(decls, key=lambda d: d["dotted"]):
            if d["pin"]:
                pinrel, pinname, how = d["pin"][:3]
                if how == "provenance comment":
                    pinrel = pin_rel(pin, pinrel)
                ln = (d["pin"][3] if len(d["pin"]) > 3 and d["pin"][3] else None) \
                    or pin_line(db, pinrel, pinname)
                label = Path(pinrel).name + (f":{ln}" if ln else "")
                url = (f"https://github.com/anthropics/fermats-last-theorem/blob/{PIN_SHA}/{pinrel}"
                       + (f"#L{ln}" if ln else ""))
                where = f"[`{label}`]({url})"
                out.append(f"| `{d['dotted']}` | {d['kind']} | `{pinname}` ({how}) | {where} |")
            else:
                out.append(f"| `{d['dotted']}` | {d['kind']} | — | the port's own |")
        out.append("")
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean", default=str(LEAN), help="port Lean root")
    ap.add_argument("--pin", default=str(PIN), help="pinned FLT clone")
    ap.add_argument("--check", action="store_true", help="exit 1 if the register is stale")
    ap.add_argument("--tsv", default=str(statement_db.TSV_DEFAULT),
                    help="the statement corpus to read")
    ap.add_argument("--rebuild", action="store_true",
                    help="rebuild the statement corpus first (statement_db.py build)")
    ap.add_argument("--json", default=str(JSON_DEFAULT))
    ap.add_argument("--no-json", action="store_true")
    a = ap.parse_args()

    global CHECKER
    CHECKER = load_checker()
    lean, pin = Path(a.lean), Path(a.pin)
    if not pin.is_dir():
        sys.exit(f"unwired_register: pin clone not found at {pin}")

    tsv = Path(a.tsv)
    if a.rebuild:
        statement_db.build(pin, tsv, jobs=min(16, os.cpu_count() or 4))
    db = statement_db.Statements(tsv)
    stale = db.stale(pin)
    if stale:
        print("unwired_register: warning — the corpus is stale ("
              + "; ".join(stale) + "); run `python3 spec/statement_db.py build`",
              file=sys.stderr)
    unlisted, importers, consumers = survey(lean, db)
    text = render(unlisted, importers, consumers, lean, pin, db)
    if a.check:
        old = REGISTER.read_text(encoding="utf-8") if REGISTER.exists() else ""
        if old != text:
            print("unwired_register: STALE — re-run without --check", file=sys.stderr)
            return 1
        print("unwired_register: register is current")
        return 0
    REGISTER.parent.mkdir(parents=True, exist_ok=True)
    REGISTER.write_text(text, encoding="utf-8")
    total = sum(len(v) for v in unlisted.values())
    print(f"wrote {REGISTER.relative_to(REPO)} — {len(unlisted)} modules, "
          f"{total} public declarations, "
          f"{sum(1 for v in unlisted.values() for d in v if d['pin'])} with a pin original")
    if not a.no_json:
        jp = Path(a.json)
        jp.parent.mkdir(parents=True, exist_ok=True)
        jp.write_text(json.dumps({"modules": unlisted, "importers": importers,
                                  "consumers": consumers},
                                 ensure_ascii=False, indent=1), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
