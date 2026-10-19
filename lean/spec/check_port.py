#!/usr/bin/env python3
"""check_port.py — check the statements of one ported module against the pinned corpus.

Why this file exists
--------------------
`spec/old_check_stmts.py` (frozen) decides what is checked from two hand-maintained
global lists (`PORT_FILES`, `SOURCES`) and resolves every module against all of
them.  At 5 % of the pin that is 618 modules and 1,513 sources; at 10 % it is
thousands of entries in one file, ordered by hand ("append last so nothing
flips"), and every agent's wiring diff lands in it.

This checker moves the wire into the module and checks **one file at a time**:

    python3 spec/check_port.py lean/FLTForHuman/X.lean     # one module
    python3 spec/check_port.py --changed                   # only what changed
    python3 spec/check_port.py --all                       # re-check every wired module
    python3 spec/check_port.py --force lean/…/X.lean       # re-check one module
    python3 spec/check_port.py --timestamps                # per-module stamp

An explicit file is cache-aware too: an unchanged module replays its stored
verdict, and `--force` re-checks it.

The module says which pin files verify it, in its leading `/- ... -/` block:

    spec-pin: Theorems/Thm_CohCarrier_heckeT_diamondRaw_comm.lean
    spec-pin: P2M/Sol/S_CohCarrier_heckeT_diamondRaw_comm.lean   -- comparable copy

A public declaration that is not found in those files is an error; the three
ways to account for one are the register's existing per-declaration markers:

    -- pin: CohCarrier.heckeT_diamondRaw_comm (Theorems/…:9)   rename / extra file
    -- own: restated against the port's `Inputs` bundle       tier 2, not diffed

(backticks around the pin name are tolerated, since one module writes them so).
A module with no `spec-pin:` line is not wired at all — tier 3, as an unlisted
module is today.

Matching.  The pin side comes from `spec/statement_db.py`'s corpus: each
`spec-pin:` file's declarations are a byte range in `statements.tsv`, and every
row carries `nhash`, the hash of the checker-normalised statement.  A port
declaration is hashed the same way (`statement_db.nhash(checker.norm(…))`), so
the comparison is on the statement, not on the name.  In order:

    marker name (if any) → exact last name → promoted key → `kw_` strip
                        → content hash anywhere in the wire → mismatch / missing

The hash tier is what a name-based checker cannot do: a statement that is
faithful but renamed verifies, and a same-name statement that differs is still a
`MISMATCH` (with the identical statement elsewhere reported as a hint).

Incremental by construction.  Every checked module gets a state entry
(`tmp/check-port/state.json`) keyed by the module's content sha1 and the corpus
stamp (pin commit + builder digest + format).  `--changed` skips a module whose
key is unchanged and replays its stored verdict; a corpus rebuild invalidates
every entry.  Content hashing, not mtime: `git checkout` and editors lie about
timestamps, and a text checker costs ~10 ms per module anyway.

Policy.  Legacy modules stay on `spec/check_flt_statements.py` and its lists
until they are edited for another reason; a module is migrated by adding its
`spec-pin:` lines (the old checker ignores them and keeps working).  The aim is
that no central file needs an entry per module again.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent          # lean/spec/
LEAN = HERE.parent                              # lean/
REPO = LEAN.parent
sys.path.insert(0, str(HERE))
import statement_db  # noqa: E402

STATE_DIR = REPO / "tmp" / "check-port"
STATE = STATE_DIR / "state.json"
LIBS = ("FLTForHuman", "Reserve")

CK = statement_db.load_checker()

HEADER = re.compile(r"\A\s*/-(?:!)?.*?-/", re.S)
SPEC_PIN = re.compile(r"^[ \t]*spec-pin:[ \t]*(\S+)(?:[ \t]+--.*)?$", re.M)
PIN_MARK = re.compile(
    r"--\s*pin:\s*`?([\w.'\u2080-\u209c]+)`?(?:\s*\(([^):\s]+)(?::(\d+))?\))?")
OWN_MARK = re.compile(r"--\s*own:\s*(.+?)\s*$")
ATTR_ONLY = re.compile(r"^@\[[^\]]*\]$")


def norm_name(raw: str) -> str:
    return raw.rsplit(".", 1)[-1]


def module_sources(text: str) -> list[str] | None:
    """The `spec-pin:` files of a module, in order; None when it is not wired."""
    head = HEADER.match(text)
    if not head:
        return None
    found = SPEC_PIN.findall(head.group(0))
    return list(dict.fromkeys(found)) if found else None


def decl_markers(text: str, rows: list[dict]) -> dict[int, tuple[str, dict | None]]:
    """line -> ("pin"|"own", parsed marker) for the declarations that carry one.

    A marker sits on the comment line above its declaration; attributes and the
    inline scope commands (`@[simp]`, `omit … in`, …) may sit between the two, so
    the walk goes up over exactly those and stops at anything else.
    """
    lines = text.split("\n")
    out: dict[int, tuple[str, dict | None]] = {}
    for r in rows:
        j = r["line"] - 2                     # 0-based, the line above the keyword
        while j >= 0 and not lines[j].strip():
            j -= 1
        while j >= 0:
            s = lines[j].strip()
            if not s or ATTR_ONLY.match(s) or re.match(
                    r"^(?:omit|include|set_option|variable|open)\b.*\bin$", s):
                j -= 1
                continue
            m = PIN_MARK.search(lines[j])
            if m:
                out[r["line"]] = ("pin", {
                    "name": m.group(1),
                    "file": m.group(2),
                    "line": int(m.group(3)) if m.group(3) else None,
                })
                break
            m = OWN_MARK.search(lines[j])
            if m:
                out[r["line"]] = ("own", {"reason": m.group(1)})
                break
            break
    return out


class Wire:
    """The pin side of one module: its wire's rows, indexed for the match tiers."""

    def __init__(self, db, sources: list[str]):
        self.sources = sources
        self.rows: list[dict] = []
        self.unknown: list[str] = []
        for rel in sources:
            got = db.file(rel)
            if not got and not db.has_file(rel):
                self.unknown.append(rel)
            self.rows.extend(dict(r, rel=rel) for r in got)
        self.by_last: dict[str, list[dict]] = defaultdict(list)
        self.by_key: dict[str, list[dict]] = defaultdict(list)
        self.by_strip: dict[str, list[dict]] = defaultdict(list)
        self.by_hash: dict[str, list[dict]] = defaultdict(list)
        self.by_file_last: dict[tuple[str, str], list[dict]] = defaultdict(list)
        for r in self.rows:
            last, name = r["last"], r["name"]
            if not last:                      # anonymous instance: no name to match
                continue
            self.by_last[last].append(r)
            self.by_key[CK.promoted_key(name)].append(r)
            self.by_key[CK.promoted_key(last)].append(r)
            s = CK.strip_pin_prefix(last)
            if s:
                self.by_strip[s].append(r)
            self.by_hash[r["nhash"]].append(r)
            self.by_file_last[(r["rel"], last)].append(r)

def same_kind(a: str, b: str) -> bool:
    return CK.same_kind(a, b)


def pick(cands: list[dict], kind: str, h: str) -> dict | None:
    for c in cands or ():
        if same_kind(kind, c["kind"]) and c["nhash"] == h:
            return c
    return None


def check_decl(row: dict, wire: Wire, db, marker, effective: list[str]) -> dict:
    """One port declaration -> {verdict, how, pin, note}."""
    kind, h, last = row["kind"], row["nhash"], row["last"]
    name = row["name"]
    if marker and marker[0] == "own":
        c = pick(wire.by_hash.get(h), kind, h)
        note = marker[1]["reason"]
        if c:
            note += (f" — but the wire has an identical statement at "
                     f"{c['rel']}:{c['line']}")
        return {"verdict": "own", "how": "own", "pin": c, "note": note}
    mk = marker[1] if marker else None

    def hit(c: dict | None, how: str) -> dict:
        return {"verdict": "ok", "how": how, "pin": c,
                "note": "" if c["name"] == name or c["last"] == last
                else f"pin name {c['name']}"}

    # 1. an explicit marker: it names the copy to diff, and is an assertion
    if mk and mk.get("name"):
        pool = wire.rows
        if mk.get("file"):
            pool = [r for r in wire.rows if r["rel"] == mk["file"]]
        cands = [r for r in pool
                 if r["name"] == mk["name"] or r["last"] == norm_name(mk["name"])]
        c = pick(cands, kind, h)
        if c:
            return hit(c, "marker")
        if cands:
            return {"verdict": "mismatch", "how": "marker", "pin": cands[0], "note": ""}
        return {"verdict": "missing", "how": "marker", "pin": None,
                "note": f"no {mk['name']} in {mk.get('file') or 'the wire'}"}

    # 2. the checker's name tiers, then content
    c = pick(wire.by_last.get(last), kind, h)
    if c:
        return hit(c, "direct name")
    c = pick(wire.by_key.get(CK.promoted_key(name)), kind, h)
    if c:
        return hit(c, "promoted key")
    stripped = CK.strip_pin_prefix(last)
    if stripped:
        c = pick(wire.by_strip.get(stripped), kind, h)
        if c:
            return hit(c, "prefix-stripped")
    c = pick(wire.by_hash.get(h), kind, h)
    if c:
        return hit(c, "content")

    # 3. no identical statement in the wire: is it a name collision or absent?
    same_name = wire.by_last.get(last) or []
    if same_name:
        note = ""
        elsewhere = db.by_hash(row["stmt"], kind) if row.get("stmt") else []
        others = [e for e in elsewhere if e["path"] not in wire.sources]
        if others:
            note = (f"identical statement at {others[0]['path']}:"
                    f"{others[0]['line']} (not in this wire)")
        return {"verdict": "mismatch", "how": "direct name", "pin": same_name[0],
                "note": note}
    # an identical statement elsewhere in the pin is a hint, not a wire member
    elsewhere = db.by_hash(row["stmt"], kind) if row.get("stmt") else []
    note = ""
    if elsewhere:
        e = elsewhere[0]
        note = f"identical statement at {e['path']}:{e['line']} (not in this wire)"
    return {"verdict": "missing", "how": "", "pin": None, "note": note}


def check_module(path: Path, db, rel: str | None = None) -> dict | None:
    """Parse + check one module; None when it carries no `spec-pin:` line."""
    text = path.read_text(encoding="utf-8", errors="replace")
    sources = module_sources(text)
    if sources is None:
        return None
    rel = rel or path.as_posix()
    rows, _lines = statement_db.parse_file(rel, text, CK)
    rows = [r for r in rows if not r[7]]                  # anonymous instances: skip
    markers = decl_markers(text, [{"line": r[0]} for r in rows])
    # a `-- pin:` marker may name a file the header does not list: it is part of
    # this module's wire for that declaration, so the wire reads it too
    files = list(dict.fromkeys(sources + [m[1]["file"] for m in markers.values()
                                          if m[1].get("file")]))
    wire = Wire(db, files)
    wire.sources = sources
    decls = []
    counts = {"ok": 0, "mismatch": 0, "missing": 0, "own": 0}
    for line, end_line, name, _key, last, kind, priv, _anon, stmt, raw, h in rows:
        if priv:                                          # a private helper is invisible
            continue
        row = {"name": name, "last": last, "kind": kind, "stmt": stmt,
               "raw": raw, "nhash": h, "line": line, "end_line": end_line}
        res = check_decl(row, wire, db, markers.get(line), sources)
        if res["pin"] is not None and not res["pin"].get("rel"):
            res["pin"]["rel"] = ""
        counts[res["verdict"]] += 1
        decls.append({"name": name, "kind": kind, "line": line,
                      "verdict": res["verdict"], "how": res["how"],
                      "note": res["note"],
                      "pin": (f"{res['pin']['rel']}:{res['pin']['line']}"
                              if res["pin"] else ""),
                      "port": row["stmt"] if res["verdict"] != "ok" else "",
                      "pin_sig": (res["pin"]["sig"]
                                  if res["verdict"] == "mismatch" else "")})
    return {"module": rel, "sources": sources, "unknown_sources": wire.unknown,
            "counts": counts, "decls": decls}


# ----------------------------------------------------------------------- state
def corpus_stamp(db) -> dict:
    m = db.meta
    return {"format": m.get("format"), "pin_commit": m.get("pin_commit"),
            "builder_sha1": m.get("builder_sha1")}


def load_state() -> dict:
    if not STATE.exists():
        return {"corpus": {}, "modules": {}}
    try:
        return json.loads(STATE.read_text())
    except ValueError:
        return {"corpus": {}, "modules": {}}


def save_state(state: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    tmp = STATE.with_name(STATE.name + ".tmp")
    tmp.write_text(json.dumps(state, indent=1, ensure_ascii=False))
    tmp.replace(STATE)


def content_sha1(path: Path) -> str:
    return hashlib.sha1(path.read_bytes()).hexdigest()


# ---------------------------------------------------------------------- output
def print_module(res: dict, cached: bool, checked_at: str | None) -> None:
    c = res["counts"]
    status = "ok" if not (c["mismatch"] or c["missing"]) else "FAIL"
    tail = (f"cached, checked {checked_at}" if cached
            else f"checked now ({time.strftime('%H:%M:%S')})")
    print(f"{res['module']}  [{status}]  "
          f"{c['ok']} ok, {c['mismatch']} mismatch, {c['missing']} missing, "
          f"{c['own']} own — {tail}")
    for rel in res.get("unknown_sources", []):
        print(f"  UNKNOWN PIN FILE  {rel}")
    for d in res["decls"]:
        mark = {"ok": "ok     ", "own": "own    ", "mismatch": "MISMATCH",
                "missing": "MISSING"}[d["verdict"]]
        if d["verdict"] in ("mismatch", "missing"):
            print(f"  {mark} {d['name']}  ({d['how'] or 'no match'})")
            if d.get("port"):
                print(f"           port: {d['port'][:300]}")
            if d.get("pin_sig"):
                print(f"           pin : {d['pin_sig'][:300]}")
            if d["note"]:
                print(f"           {d['note']}")
        else:
            extra = f"  -> {d['pin']}" if d["pin"] else ""
            note = f"  [{d['note']}]" if d["note"] else ""
            print(f"  {mark} {d['name']}{extra}{note}")
    print()


def wired_modules(legacy: set[str], include_legacy: bool = False
                  ) -> tuple[list[str], int]:
    """Lean files with a `spec-pin:` directive, and how many were exempted.

    The frozen registry's modules are skipped **by path, without opening the
    file**: they are the ported files that predate the protocol, and reading them
    every run is exactly the work the exemption exists to avoid.  Everything else
    is opened (header read) and kept only if it declares a wire.
    """
    out: list[str] = []
    skipped = 0
    for lib in LIBS:
        for p in (LEAN / lib).rglob("*.lean"):
            if ".lake" in p.parts:
                continue
            rel = p.relative_to(LEAN).as_posix()
            if rel in legacy and not include_legacy:
                skipped += 1
                continue
            text = p.read_text(encoding="utf-8", errors="replace")
            if module_sources(text) is not None:      # the header's own rule
                out.append(rel)
    return sorted(out), skipped


# ------------------------------------------------------------------------- main
def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", help="module files (relative to lean/ or absolute)")
    ap.add_argument("--changed", action="store_true",
                    help="only modules whose content or corpus stamp changed "
                         "(the default with no paths)")
    ap.add_argument("--all", action="store_true", help="every wired module")
    ap.add_argument("--force", action="store_true",
                    help="re-check even if the module is unchanged")
    ap.add_argument("--include-legacy", action="store_true",
                    help="also check modules still owned by old_check_stmts.py")
    ap.add_argument("--timestamps", action="store_true",
                    help="show the per-module stamp table and exit")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--verbose", action="store_true", help="show cached declarations too")
    ap.add_argument("--tsv", default=str(statement_db.TSV_DEFAULT))
    a = ap.parse_args()

    db = statement_db.Statements(Path(a.tsv))
    stale = db.stale(statement_db.PIN_DEFAULT)
    if stale:
        print("check_port: warning — the corpus is stale (" + "; ".join(stale)
              + "); run `python3 spec/statement_db.py build`", file=sys.stderr)
    stamp = corpus_stamp(db)
    state = load_state()
    state_corpus_ok = state.get("corpus") == stamp

    if a.timestamps:
        rows = sorted(state.get("modules", {}).items())
        if a.json:
            print(json.dumps(dict(rows), indent=1))
            return 0
        print(f"{'module':70s}  {'checked at':19s}  verdict")
        for mod, e in rows:
            c = e.get("counts", {})
            v = "ok" if not (c.get("mismatch") or c.get("missing")) else "FAIL"
            here = (LEAN / mod)
            now = content_sha1(here) if here.exists() else ""
            fresh = "" if now == e.get("sha1") and state_corpus_ok else "  (edited)"
            print(f"{mod:70s}  {e.get('checked_at', ''):19s}  {v}{fresh}")
        return 0

    legacy = statement_db.legacy_port_files()
    exempt_count = 0
    if a.paths:
        targets = []
        for p in a.paths:
            path = Path(p)
            if not path.is_absolute():
                path = (LEAN / p) if (LEAN / p).exists() else Path(p)
            rel = path.resolve().relative_to(LEAN).as_posix() if path.resolve().is_relative_to(LEAN) else path.as_posix()
            if rel in legacy:
                print(f"check_port: note — {rel} is still in old_check_stmts.py's "
                      f"PORT_FILES (the frozen checker owns it); checking anyway",
                      file=sys.stderr)
            targets.append((rel, path))
    else:
        allw, exempt_count = wired_modules(legacy, a.include_legacy)
        targets = [(rel, LEAN / rel) for rel in allw]
        if not (a.all or a.changed):
            a.changed = True

    results, checked = [], 0
    for rel, path in targets:
        if not path.exists():
            print(f"check_port: no such module: {path}", file=sys.stderr)
            continue
        old = state.get("modules", {}).get(rel)
        sha = content_sha1(path)
        if (not a.force and not a.all and old and state_corpus_ok
                and old.get("sha1") == sha):
            res = {"module": rel, "sources": old.get("sources", []),
                   "unknown_sources": old.get("unknown_sources", []),
                   "counts": old.get("counts", {}),
                   "decls": old.get("decls", []) if (a.verbose or a.json) else []}
            results.append((res, True, old.get("checked_at")))
            continue
        res = check_module(path, db, rel)
        if res is None:
            print(f"{rel}: no `spec-pin:` directive — not wired (tier 3)",
                  file=sys.stderr)
            continue
        res["checked_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
        res["sha1"] = sha
        state.setdefault("modules", {})[rel] = res
        state["corpus"] = stamp
        checked += 1
        results.append((res, False, res["checked_at"]))

    if checked:
        save_state(state)

    if a.json:
        print(json.dumps({"corpus": stamp,
                          "results": [r for r, _c, _t in results]},
                         indent=1, ensure_ascii=False))
    else:
        for res, cached, at in results:
            if cached and not a.verbose:
                c = res["counts"]
                print(f"{res['module']}  [cached]  {c.get('ok', 0)} ok, "
                      f"{c.get('mismatch', 0)} mismatch, {c.get('missing', 0)} missing, "
                      f"{c.get('own', 0)} own")
            else:
                print_module(res, cached, at)
        total = {"ok": 0, "mismatch": 0, "missing": 0, "own": 0}
        for res, _c, _t in results:
            for k, v in res["counts"].items():
                total[k] = total.get(k, 0) + v
        print(f"{total['ok']} ok, {total['mismatch']} mismatch, {total['missing']} "
              f"missing, {total['own']} own — {len(results)} module(s), "
              f"{checked} checked, {len(results) - checked} cached"
              + (f", {exempt_count} exempt (PORT_FILES)" if exempt_count else "")
              + f"; corpus {str(stamp.get('pin_commit'))[:7]}")

    bad = any(r["counts"].get("mismatch") or r["counts"].get("missing")
              or r.get("unknown_sources") for r, _c, _t in results)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
