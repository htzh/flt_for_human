#!/usr/bin/env python3
"""statement_db.py — a plain-text index of every declaration *statement* in the pin.

Why this file exists
--------------------
The pinned FLT tree is 1.1 GB of Lean in 60,478 files.  Its prebuilt docs-site data
(`html/data/{meta,edges,ddecl,titles,shard}.js`, read by the unpublished
`tools/deps/fltdata.py`) indexes only the *graph*: 29,511 theorem nodes and the
33,391 declarations of the 1,450 `Definitions/` modules.  `ddecl.js` carries
`(name, module, line, kind)` and no text, so for a `Theorems/Thm_*.lean` wrapper or a
`P2M/Sol/S_*.lean` silo -- 59,000 of the 60,478 files -- fltdata knows nothing at
all, and for everything it does know it cannot show the statement.  That is why
agents still grep the 1.1 GB tree to read a signature.

This tool flattens the pin once into a **single text file**, one line per
declaration, sorted by `file:line`:

    tmp/flt-statements/statements.tsv

    path  line  end_line  kind  flags  name  nhash  signature

It is tab-separated with the (long) signature last, so `less` pages it, `cut -f1-6`
gives the metadata, `rg` searches it and `awk` can still take it apart.  There is no
database: the file *is* the index, and it is the only generated artifact (plus a
3 MB byte-offset index and a small stamp, below).  It is git-ignored, disposable,
and rebuilt by one command.

    python3 spec/statement_db.py build            # ~40 s, 16 cores
    python3 spec/statement_db.py show ModularCurve.coeffEmb_qExpand
    python3 spec/statement_db.py file Theorems/Thm_ModularCurve_coeffEmb_qExpand.lean
    python3 spec/statement_db.py grep 'dedekindPsi_mul_of_coprime'
    python3 spec/statement_db.py check            # exit 1 if the pin moved under it
    python3 spec/statement_db.py verify           # the file == the checker's own parse

What the columns mean
---------------------
* `path`, `line`, `end_line` -- `line` is the declaration's keyword line (what a
  citation should point at, and what the pin's docs-site index records); an
  `@[...]` attribute line above it belongs to the signature column.
* `kind` -- `theorem`/`lemma`/`def`/`abbrev`/`structure`/`class`/`instance`, as the
  parser's own `DECL_RE` reads it.
* `flags` -- two characters: `p`/`-` private, `a`/`-` anonymous instance.
* `name` -- the name as the pin writes it (enclosing namespaces included, `_root_.`
  left alone).  It may be empty, for an anonymous instance.
* `nhash` -- `sha1` of the **checker-normalised** statement, 20 hex characters.  This
  is the matching key: normalise a port declaration's statement, hash it, and
  `rg -F '\\t<hash>\\t'` finds every pin copy in ~0.1 s.  Normalisation follows
  `spec/lean_parser.py` (`ModularCurve.`/`AlgebraicCurve.`/`kw_` prefixes
  erased), which is what a statement diff compares.
* `signature` -- the *raw* signature with `--` comments dropped and whitespace
  collapsed: the declaration as printed, up to the first top-level `:=`/`where`
  (for a `structure`/`class`, the header and fields).  Raw, because normalisation
  erases namespace qualifiers and a corpus you cannot search for a qualified name
  is worse than useless.  This is what you read; `nhash` is what a tool compares.

Companion files, written by the same build, next to the TSV:

    statements.idx        60,478 lines: `path start_byte end_byte decls`
    statements.json       the stamp: pin commit, checker/build digests, counts

The `.idx` is what makes the file *usable by a checker* rather than only by a
human: one pin file's declarations are a byte range, so a module-scoped check reads
the 1-2 files it names instead of the 1.1 GB tree.  The stamp makes `check` cheap
and lets a consumer tell a stale corpus from a current one.

What it is not
--------------
* Not a second parser.  `DECL_RE`/`ENCLOSE_RE`/`norm`/`top_level_cut` come from
  `spec/lean_parser.py`, the one parser the new checker, the corpus and the
  planning tools share; the frozen `old_check_stmts.py` imports it too.  `verify`
  holds every `SOURCES` file to that parse.
* Not a source of truth.  It is regenerated atomically; tools read the TSV (or the
  `.idx`), never a hand-edited copy.
* Not complete beyond the parser: anonymous instances are indexed (`flags` ends in
  `a`, empty name) but a name-based lookup cannot find them; declarations whose
  *modifier* the regex does not admit (`local instance foo`, `scoped instance`) and
  `inductive`/`axiom`/`opaque` are absent -- the known gap in `CARRY-FORWARD.md`
  ("Tool hazards"), to be closed once in both tools at the same time.

Policy note: this is infrastructure for the successor to the legacy checker.  The
legacy checker and the modules already wired to it are grandfathered; nothing here
changes what it diffs.  New modules are expected to be stated against this corpus
(and the in-file provenance directives that replace the checker's central
`SOURCES`/`PORT_FILES` lists); existing modules migrate only when edited.
"""
from __future__ import annotations

import argparse
import bisect
import hashlib
import importlib.util
import inspect
import json
import multiprocessing as mp
import os
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent          # lean/spec/
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import lean_parser as P  # noqa: E402  (the parser, not the legacy registry)
REPO = HERE.parent.parent
# The frozen legacy registry (`PORT_FILES`/`SOURCES`), read here only for
# `legacy_port_files`/`legacy_source_files`; do not add to its lists.  The parser
# is `spec/lean_parser.py`, imported above.  New modules wire themselves with
# `spec-pin:` and are checked by `spec/check_port.py`.
CHECKER_PATH = HERE / "old_check_stmts.py"
PIN_DEFAULT = Path.home() / "proj" / "fermats-last-theorem"
CACHE = REPO / "tmp" / "flt-statements"
TSV_DEFAULT = CACHE / "statements.tsv"
PIN_SHA_FALLBACK = "aa2d8b3"
FORMAT = 1
NHASH_ALGO = "sha1/20"
SKIP_DIRS = {".lake", "html", "build", ".git"}
NCOL = 8                    # path line end_line kind flags name nhash signature
SIG_COL = NCOL - 1

_PIN_ROOT = ""


# --------------------------------------------------------------------- parsing
# Everything down to `_worker` is the checker's parser, run over the
# comment-blanked text so line numbers survive; see the module docstring.
def flat_code(text: str) -> str:
    """`text` with block comments blanked, newlines kept, so line numbers survive.

    The checker replaces a block comment by one space, which loses the line
    count; a cache keyed by `file:line` cannot afford that.  Replacing a comment
    by *its own* newlines keeps every line boundary and, because `norm()` strips
    comments again, the normalised statement is unchanged.  (Nested `/- -/` is
    beyond the checker too.)
    """
    return re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text,
                  flags=re.DOTALL)


def _line_starts(code: str) -> list[int]:
    starts = [0]
    for i, c in enumerate(code):        # one pass, no per-declaration counting
        if c == "\n":
            starts.append(i + 1)
    return starts


# An `instance` with no name.  `DECL_RE` needs an identifier after the keyword, so
# the legacy checker cannot see these -- but they are real, public statements
# (`Definitions/Def_NumberField_HeightOneSpectrum.lean`, `P2M/Derive/D_*_DecidableEq.lean`)
# and a consumer that greps for them today finds prose it cannot resolve to a name.
# They are indexed as `anon = 1` with an empty name: `grep` and `by_hash` reach
# them, `find` cannot (there is no name to find), and a checker skips them.
ANON_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]\n]*\]\s*)*)"
    r"(?P<mods>(?:(?:private|protected|noncomputable|scoped|local|unsafe)\s+)*)"
    r"(?:(?P<deriv>deriving)\s+)?instance\b"
    # a *named* instance is `instance foo ...`; `deriving instance` has no name by
    # construction, and a nameless instance is followed by `:`/`[`/`(`/`{`
    r"(?(deriv)|(?=\s*[\[({⦃:]))",
    re.MULTILINE,
)


def _structure_end(raw_lines: list[str], header_end: int, limit: int) -> int:
    """Last line of a `structure`/`class` block: first later line at indent 0."""
    for ln in range(header_end + 1, limit):
        s = raw_lines[ln - 1] if ln - 1 < len(raw_lines) else ""
        stripped = s.strip()
        if not stripped or stripped.startswith("--") or stripped.startswith("/-"):
            continue
        if not s[:1].isspace():
            return max(header_end, ln - 1)
    return max(header_end, limit - 1)


def parse_file(rel: str, text: str) -> tuple[list[tuple], int]:
    """(rows, line_count) for one Lean file.

    A row is `(line, end_line, name, last, kind, private, stmt, raw, nhash)`, in
    source order.  One pass over the comment-blanked text does both jobs: the
    declaration walk (position, namespace stack, name and kind, exactly as
    `old_check_stmts.raw_declarations` does it) and the signature slice.
    """
    code = flat_code(text)
    raw_lines = text.split("\n")
    starts = _line_starts(code)

    named = list(P.DECL_RE.finditer(code))
    named_starts = [m.start() for m in named]
    named_at = set(named_starts)
    anon = [m for m in ANON_RE.finditer(code) if m.start() not in named_at]
    if not named and not anon:
        return [], len(raw_lines)
    # (start, end, kind, private, written name); an anonymous instance has no name
    decls = [(m.start(), m.end(), m.group("kind"), "private" in m.group("mods"),
              m.group("name")) for m in named]
    decls += [(m.start(), m.end(), "instance", "private" in m.group("mods"), None)
              for m in anon]
    decls.sort()
    events = P.namespace_events(code)
    stack: list[str | None] = []
    ei = 0
    rows: list[tuple] = []
    for idx, (start, name_end, kind, is_priv, written) in enumerate(decls):
        while ei < len(events) and events[ei][0] < start:
            ekind, ename = events[ei][1], events[ei][2]
            if ekind == "ns":
                stack.append(ename)
            elif ekind == "sec":
                # a `section`/`mutual` frame holds no name, but its `end` must pop
                # this placeholder rather than the enclosing namespace
                stack.append(None)
            else:
                P.pop_frames(stack, ename)
            ei += 1
        # The chunk boundary is the next *named* declaration, exactly as in the
        # checker: an anonymous instance indexed here must not shorten the
        # statement of the declaration before it (a `|`-clause `def` has no
        # top-level `:=`, so its chunk runs to the next declaration it recognises).
        k = bisect.bisect_right(named_starts, start)
        end = named_starts[k] if k < len(named_starts) else len(code)
        chunk = code[name_end:end]
        cut = P.top_level_cut(chunk)
        if kind in ("structure", "class"):
            stmt = P.norm(chunk[:cut]) + " FIELDS " + " ".join(
                P.FIELD_RE.findall(chunk))
        else:
            stmt = P.norm(chunk[:cut])
        # `line` is the declaration's *keyword* line (what a citation should point
        # at, and what the pin's own docs-site index records); the attribute line an
        # `@[...]` may sit on belongs to `raw`, which therefore starts one line up.
        line = bisect.bisect_right(starts, name_end)
        raw_start = bisect.bisect_right(starts, start)
        end_line = line + chunk[:cut].count("\n")
        if kind in ("structure", "class"):
            nxt = (bisect.bisect_right(starts, decls[idx + 1][0])
                   if idx + 1 < len(decls) else len(raw_lines) + 1)
            end_line = _structure_end(raw_lines, end_line, nxt)
        raw = "\n".join(raw_lines[raw_start - 1:end_line])
        if 0 < cut < len(chunk):
            # drop the proof/body that shares the cut's line (`:= rfl`), but only
            # when the raw line is the code line (a blanked block comment shifts
            # the offsets, and a wrong trim is worse than a noisy one)
            ls = starts[end_line - 1]
            le = code.find("\n", ls)
            code_last = code[ls:le if le >= 0 else len(code)]
            if code_last == raw_lines[end_line - 1]:
                col = (name_end + cut) - ls      # column of the cut in its line
                raw = raw[:len(raw) - len(code_last)] + code_last[:col]
        raw = raw.rstrip()
        prefix = P.enclosing_namespace(stack)
        name = (f"{prefix}.{written}" if prefix else written) if written else ""
        rows.append((
            line, end_line, name,
            P.promoted_key(name) if name else "",
            name.rsplit(".", 1)[-1] if name else "", kind,
            1 if is_priv else 0, 0 if written else 1,
            stmt, raw,
            hashlib.sha1(stmt.encode("utf-8")).hexdigest()[:20],
        ))
    return rows, len(raw_lines)


def _worker(rel: str) -> tuple[str, list[tuple], int]:
    try:
        text = (Path(_PIN_ROOT) / rel).read_text(encoding="utf-8", errors="replace")
    except OSError:                            # unreadable is not fatal
        return rel, [], 0
    rows, lines = parse_file(rel, text)
    return rel, rows, lines





def _init_worker(pin_root: str) -> None:
    global _PIN_ROOT
    _PIN_ROOT = pin_root


def row_line(rel: str, r) -> str:
    """One declaration -> one TSV line (the only place the format is written)."""
    line, end_line, name, _key, _last, kind, priv, anon, _stmt, raw, nhash = r
    return (f"{rel}\t{line}\t{end_line}\t{kind}\t{flags_of(priv, anon)}\t"
            f"{name}\t{nhash}\t{sig_from_raw(raw)}\n")


# --------------------------------------------------------------------- pin scan
def pin_root(pin: Path) -> Path:
    return pin.resolve()


def pin_files(pin: Path) -> list[tuple[str, int, int]]:
    """(relpath, size, mtime_ns) for every Lean file worth indexing, sorted."""
    out: list[tuple[str, int, int]] = []
    for p in pin.rglob("*.lean"):
        if SKIP_DIRS & set(p.parts):
            continue
        try:
            st = p.stat()
        except OSError:
            continue
        out.append((p.relative_to(pin).as_posix(), st.st_size, st.st_mtime_ns))
    out.sort()
    return out


def pin_commit(pin: Path) -> str:
    try:
        r = subprocess.run(["git", "-C", str(pin), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=20)
        if r.returncode == 0 and r.stdout.strip():
            return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return PIN_SHA_FALLBACK


def checker_sha1() -> str:
    """Digest of the statement parser (`lean_parser`), not of any registry list.

    The legacy registry is being dismantled one module at a time: every handoff
    deletes a `PORT_FILES` line, and every handoff must not invalidate a 1 GB corpus
    that nothing about the parser changed.  So the digest covers the regexes, the
    name-prefix and kind tables, and the functions that read a statement -- not the
    lists.
    """
    parts = [P.DECL_RE.pattern, P.ENCLOSE_RE.pattern, P.FIELD_RE.pattern,
             repr(P.PIN_PREFIXES), repr(P.KIND_EQUIV)]
    for fn in (P.strip_comments, P.strip_line_comments, P.namespace_events,
               P.enclosing_namespace, P.pop_frames, P.top_level_cut, P.norm,
               P.raw_declarations, P.declarations, P.promoted_key,
               P.strip_pin_prefix, P.same_kind):
        parts.append(inspect.getsource(fn))
    return hashlib.sha1("\n".join(parts).encode()).hexdigest()


def legacy_port_files() -> set[str]:
    """The modules the frozen checker still owns (`PORT_FILES` in the old file)."""
    text = CHECKER_PATH.read_text(encoding="utf-8")
    m = re.search(r"^PORT_FILES = \[(.*?)^\]", text, re.S | re.MULTILINE)
    return set(re.findall(r'^\s*"([^"]+)"', m.group(1), re.MULTILINE)) if m else set()


def legacy_source_files() -> list[str]:
    """The pin files the frozen checker reads (`SOURCES`), in order, deduplicated."""
    text = CHECKER_PATH.read_text(encoding="utf-8")
    m = re.search(r"^SOURCES = \[(.*?)^\]", text, re.S | re.MULTILINE)
    return list(dict.fromkeys(re.findall(r'"([^"]+)"', m.group(1)))) if m else []





def builder_sha1() -> str:
    """Digest of the code that *produces rows*, not of the whole file.

    A docstring or a CLI flag must not invalidate the corpus; a change to the
    parser or to the row format must.  So the digest covers the parse functions,
    the format version and the anonymous-instance pattern.
    """
    parts = [str(FORMAT), ANON_RE.pattern]
    for fn in (flat_code, _line_starts, _structure_end, parse_file):
        parts.append(inspect.getsource(fn))
    return hashlib.sha1("\n".join(parts).encode()).hexdigest()


# -------------------------------------------------------------------- the store
def sig_from_raw(raw: str) -> str:
    """The one-line signature: comments out, whitespace collapsed.

    `raw` is already cut at the declaration's `:=`/`where`; this only makes it a
    single field.  A `--` inside the signature would otherwise comment out the
    rest of the *displayed* line, so line comments go first.
    """
    return " ".join(re.sub(r"--[^\n]*", "", raw).split())


def nhash(stmt: str) -> str:
    """The corpus's statement hash: sha1 of the *normalised* statement, 20 hex.

    `parse_file` inlines the same expression (it is part of the parser digest);
    this is the reader-side spelling, so the register and any checker hash a
    statement exactly the way the corpus did.
    """
    return hashlib.sha1(stmt.encode("utf-8")).hexdigest()[:20]


def flags_of(private: int, anon: int) -> str:
    return ("p" if private else "-") + ("a" if anon else "-")


def parse_row(line: str) -> dict:
    """One TSV line -> a row dict.  The signature is the only field with spaces."""
    p, ln, end, kind, flags, name, nhash, sig = line.rstrip("\n").split("\t", SIG_COL)
    return {
        "path": p, "line": int(ln), "end_line": int(end), "kind": kind,
        "flags": flags, "private": "p" in flags, "anon": "a" in flags,
        "name": name, "last": name.rsplit(".", 1)[-1] if name else "",
        "nhash": nhash, "sig": sig,
    }


def build(pin: Path, out: Path = TSV_DEFAULT, jobs: int = 1,
          quiet: bool = False) -> int:
    files = pin_files(pin)
    if not files:
        sys.exit(f"statement_db: no .lean files under {pin}")
    commit = pin_commit(pin)
    out.parent.mkdir(parents=True, exist_ok=True)
    idx = out.with_suffix(".idx")
    stamp = out.with_suffix(".json")
    tsv_tmp = out.with_name(out.name + ".tmp")
    idx_tmp = idx.with_name(idx.name + ".tmp")

    counts: Counter = Counter()
    private_total = anon_total = 0
    decl_total = 0
    t0 = time.time()
    done = 0
    pos = 0
    with tsv_tmp.open("wb") as fh, idx_tmp.open("w", encoding="utf-8") as ix:
        with mp.Pool(jobs, initializer=_init_worker,
                     initargs=(str(pin),)) as pool:
            # ordered: the file must be sorted by path, line (and the .idx with it)
            for rel, rows, _lines in pool.imap(
                    _worker, [rel for rel, _s, _m in files], chunksize=8):
                start = pos
                buf = []
                for r in rows:
                    buf.append(row_line(rel, r))
                    counts[r[5]] += 1
                    private_total += 1 if r[6] else 0
                    anon_total += 1 if r[7] else 0
                data = "".join(buf).encode("utf-8")
                fh.write(data)
                pos += len(data)
                decl_total += len(rows)
                ix.write(f"{rel}\t{start}\t{pos}\t{len(rows)}\n")
                done += 1
                if not quiet and done % 10000 == 0:
                    print(f"  {done:,}/{len(files):,} files, {decl_total:,} "
                          f"declarations, {time.time() - t0:.0f}s", flush=True)
    tsv_tmp.replace(out)
    idx_tmp.replace(idx)
    stamp.write_text(json.dumps({
        "format": FORMAT, "generator": "spec/statement_db.py",
        "pin": str(pin.resolve()), "pin_commit": commit,
        "checker_sha1": checker_sha1(), "builder_sha1": builder_sha1(),
        "nhash_algo": NHASH_ALGO, "created": time.strftime("%Y-%m-%d %H:%M:%S"),
        "files": len(files), "decls": decl_total,
        "kinds": dict(counts), "private": private_total, "anon": anon_total,
        "bytes": pos,
    }, indent=1))
    if not quiet:
        print(f"wrote {out} — {len(files):,} files, {decl_total:,} declarations, "
              f"{out.stat().st_size / 1e6:.0f} MB, {time.time() - t0:.0f}s, "
              f"pin {commit[:7]}")
    return 0


def update(pin: Path, out: Path = TSV_DEFAULT, jobs: int = 1,
           quiet: bool = False) -> int:
    """Rebuild when the stamp or the pin's worktree says the corpus is out of date.

    A text file cannot be patched row-by-row without a second index, and the pin is
    a pinned clone: it changes only on a re-pin or a deliberate local edit, both of
    which change every consumer's view anyway.  So `update` checks and, when needed,
    rebuilds — the same command the manager runs after a re-pin.
    """
    if not out.exists():
        return build(pin, out, jobs, quiet)
    stale = _stale_reasons(pin, out)
    if stale:
        if not quiet:
            print(f"statement_db: rebuilding ({'; '.join(stale)})", file=sys.stderr)
        return build(pin, out, jobs, quiet)
    if not quiet:
        print("statement_db: up to date")
    return 0


def _stale_reasons(pin: Path, out: Path) -> list[str]:
    """Why the corpus may not describe the pin, or [] when it does."""
    stamp = out.with_suffix(".json")
    idx = out.with_suffix(".idx")
    reasons = []
    if not out.exists():
        return ["no corpus"]
    if not idx.exists() or not stamp.exists():
        return ["missing index or stamp"]
    try:
        meta = json.loads(stamp.read_text())
    except ValueError:
        return ["unreadable stamp"]
    if meta.get("format") != FORMAT:
        reasons.append(f"format {meta.get('format')} -> {FORMAT}")
    if meta.get("pin_commit") != pin_commit(pin):
        reasons.append(f"pin commit {str(meta.get('pin_commit'))[:7]} -> "
                       f"{pin_commit(pin)[:7]}")
    if meta.get("checker_sha1") != checker_sha1():
        reasons.append("spec/old_check_stmts.py changed")
    if meta.get("builder_sha1") != builder_sha1():
        reasons.append("spec/statement_db.py parser changed")
    dirty = _pin_dirty_lean(pin)
    if dirty:
        reasons.append(f"{len(dirty)} edited pin file(s), e.g. {dirty[0]}")
    return reasons


def _pin_dirty_lean(pin: Path) -> list[str]:
    """Lean files with uncommitted changes in the pin clone (a pinned clone is clean)."""
    try:
        r = subprocess.run(
            ["git", "-C", str(pin), "status", "--porcelain", "-uno", "--", "*.lean"],
            capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return []
    if r.returncode != 0:
        return []
    return [ln[3:].strip() for ln in r.stdout.splitlines() if ln.strip()]


# -------------------------------------------------------------------- the reader
class Statements:
    """Read-only view of the corpus.

    `rg` is used when it is on `PATH` (0.1 s for a lookup over 470 MB), with a pure
    Python scan as the fallback, so nothing here requires it.  Rows are dicts with
    the TSV's fields plus `last` (the bare last name component).
    """

    def __init__(self, path: Path | str = TSV_DEFAULT, use_rg: bool | None = None):
        self.path = Path(path)
        if not self.path.exists():
            sys.exit(f"statement_db: no corpus at {self.path} — run "
                     f"`python3 spec/statement_db.py build` first")
        self.idx = self.path.with_suffix(".idx")
        self.stamp_path = self.path.with_suffix(".json")
        self.use_rg = (shutil.which("rg") is not None) if use_rg is None else use_rg
        self._idx: dict[str, tuple[int, int]] | None = None

    @property
    def meta(self) -> dict:
        return json.loads(self.stamp_path.read_text())

    # -- primitives ---------------------------------------------------------
    def iter_rows(self):
        with self.path.open(encoding="utf-8", errors="replace") as fh:
            for line in fh:
                yield parse_row(line)

    def _scan(self, pred) -> list[dict]:
        return [r for r in self.iter_rows() if pred(r)]

    def _rg_rows(self, args: list[str]) -> list[dict] | None:
        """Rows of the lines `rg` selects, or None when rg cannot be used."""
        if not self.use_rg:
            return None
        try:
            r = subprocess.run(
                ["rg", "--no-config", "--no-ignore", "--no-filename", "--color", "never",
                 *args, str(self.path)],
                capture_output=True, text=True, timeout=120)
        except (OSError, subprocess.SubprocessError):
            return None
        if r.returncode not in (0, 1):
            return None
        return [parse_row(ln) for ln in r.stdout.splitlines() if ln]

    # -- queries ------------------------------------------------------------
    def find(self, name: str, limit: int | None = None) -> list[dict]:
        """Resolve a name the way a note writes it.

        Tiers, first hit wins: the exact qualified name as the pin writes it; a
        dotted suffix (a name under the pin's `p2mw` namespace scaffolding or behind
        `_root_.`); and the bare last component.  `matched_by` records the tier.
        """
        last = name.rsplit(".", 1)[-1]
        tiers = [
            ("name", lambda r: r["name"] == name, ["-F", f"\t{name}\t"]),
            ("suffix", lambda r: r["name"].endswith("." + name),
             ["-e", f"\t[^\t]*\\.{re.escape(name)}\t"]),
            ("last", lambda r: r["last"] == last,
             ["-e", f"\t(?:[^\t]*\\.)?{re.escape(last)}\t"]),
        ]
        for how, pred, rg_args in tiers:
            rows = self._rg_rows(rg_args)
            if rows is None:
                rows = self._scan(pred)
            else:
                rows = [r for r in rows if pred(r)]
            if rows:
                for r in rows:
                    r["matched_by"] = how
                return rows[:limit] if limit else rows
        return []

    def by_hash(self, stmt: str, kind: str | None = None,
                limit: int | None = None) -> list[dict]:
        """Pin declarations whose normalised statement equals `stmt`."""
        h = hashlib.sha1(stmt.encode("utf-8")).hexdigest()[:20]
        rows = self._rg_rows(["-F", f"\t{h}\t"])
        if rows is None:
            rows = self._scan(lambda r: r["nhash"] == h)
        if kind:
            # the checker's equivalence, not a string compare: it treats
            # theorem/lemma/def as one kind
            rows = [r for r in rows if P.same_kind(kind, r["kind"])]
        return rows[:limit] if limit else rows

    def by_hashes(self, hashes) -> dict[str, list[dict]]:
        """Batch form of `by_hash`: one scan for many statements.

        This is what a checker wants -- it has thousands of port statements and
        wants each one's pin copies -- and it stays inside `rg`'s automaton: one
        process, all hashes as patterns, results bucketed by the hash field.
        """
        want = set(hashes)
        out: dict[str, list[dict]] = {h: [] for h in want}
        if not want:
            return out
        rows = None
        if self.use_rg:
            try:
                r = subprocess.run(
                    ["rg", "--no-config", "--no-ignore", "--no-filename", "--color",
                     "never", "-F", "-f", "-", str(self.path)],
                    input="\n".join(want) + "\n", capture_output=True, text=True,
                    timeout=120)
                if r.returncode in (0, 1):
                    rows = [parse_row(ln) for ln in r.stdout.splitlines() if ln]
            except (OSError, subprocess.SubprocessError):
                rows = None
        if rows is None:
            rows = self._scan(lambda r: r["nhash"] in want)
        for r in rows:
            if r["nhash"] in out:
                out[r["nhash"]].append(r)
        return out

    def file(self, rel: str) -> list[dict]:
        """One pin file's declarations, in line order (a byte range, not a scan)."""
        span = self._span(rel)
        if span is None:
            return []
        start, end = span
        with self.path.open("rb") as fh:
            fh.seek(start)
            data = fh.read(max(0, end - start))
        return [parse_row(ln) for ln in data.decode("utf-8").splitlines() if ln]

    def _span(self, rel: str) -> tuple[int, int] | None:
        if self._idx is None:
            self._idx = {}
            if self.idx.exists():
                with self.idx.open(encoding="utf-8") as fh:
                    for line in fh:
                        p, start, end, _n = line.rstrip("\n").split("\t")
                        self._idx[p] = (int(start), int(end))
        return self._idx.get(rel)

    def has_file(self, rel: str) -> bool:
        """Whether the corpus indexed this pin file (even if it declares nothing)."""
        return self._span(rel) is not None

    def at(self, rel: str, line: int) -> dict | None:
        for r in self.file(rel):
            if r["line"] == line:
                return r
        return None

    def search(self, pattern: str, kind: str | None = None, public_only: bool = False,
               regex: bool = False, limit: int | None = None) -> list[dict]:
        """Substring or regex search over the whole line (path, name, signature)."""
        rows = self._rg_rows(["-e", pattern] if regex else ["-F", "-e", pattern])
        if rows is None:
            rx = re.compile(pattern) if regex else None
            rows = self._scan(
                (lambda r: rx.search(r["path"] + "\t" + r["name"] + "\t" + r["sig"]))
                if regex else
                (lambda r: pattern in r["path"] or pattern in r["name"]
                 or pattern in r["sig"]))
        if kind:
            rows = [r for r in rows if r["kind"] == kind]
        if public_only:
            rows = [r for r in rows if not r["private"]]
        return rows[:limit] if limit else rows

    def stale(self, pin: Path) -> list[str]:
        """Why this corpus may not describe `pin`, or [] when it does.

        The same check `update`/`check` use, exposed for the other readers (the
        register) so no tool silently reports from a corpus built for a different
        pin or parser.
        """
        return _stale_reasons(Path(pin), self.path)

    def stats(self) -> dict:
        meta = self.meta if self.stamp_path.exists() else {}
        return {
            "corpus": str(self.path),
            "bytes": self.path.stat().st_size,
            "lines": meta.get("decls"),
            "files": meta.get("files"),
            "kinds": meta.get("kinds", {}),
            "private": meta.get("private"), "anonymous": meta.get("anon"),
            "pin_commit": meta.get("pin_commit"),
            "created": meta.get("created"),
        }


# ---------------------------------------------------------------------- output
def github_url(meta: dict, rel: str, line: int, end_line: int) -> str:
    sha = (meta.get("pin_commit") or PIN_SHA_FALLBACK)[:7]
    frag = f"#L{line}" if end_line <= line else f"#L{line}-L{end_line}"
    return f"https://github.com/anthropics/fermats-last-theorem/blob/{sha}/{rel}{frag}"


def format_row(r: dict, meta: dict) -> str:
    priv = ", private" if r["private"] else ""
    name = r["name"] or "<anonymous instance>"
    how = r.get("matched_by")
    tier = f", by {how}" if how and how != "name" else ""
    head = (f"{name}  ({r['kind']}{priv}{tier})  {r['path']}:{r['line']}"
            + (f"-{r['end_line']}" if r["end_line"] > r["line"] else ""))
    return f"{head}\n  {github_url(meta, r['path'], r['line'], r['end_line'])}\n{r['sig']}"


def report_rows(rows: list[dict], meta: dict, as_json: bool) -> None:
    if as_json:
        print(json.dumps({"pin_commit": (meta.get("pin_commit") or "")[:7],
                          "rows": rows}, ensure_ascii=False, indent=1))
        return
    for i, r in enumerate(rows):
        if i:
            print()
        print(format_row(r, meta))


# -------------------------------------------------------------------- commands
def cmd_build(a) -> int:
    return build(Path(a.pin), Path(a.tsv), a.jobs, a.quiet)


def cmd_update(a) -> int:
    return update(Path(a.pin), Path(a.tsv), a.jobs, a.quiet)


def cmd_check(a) -> int:
    out = Path(a.tsv)
    if not out.exists():
        print(f"statement_db: no corpus at {out}", file=sys.stderr)
        return 1
    reasons = _stale_reasons(Path(a.pin), out)
    if reasons:
        print("statement_db: STALE — " + "; ".join(reasons), file=sys.stderr)
        return 1
    meta = json.loads(out.with_suffix(".json").read_text())
    print(f"statement_db: current ({meta.get('files')} files, "
          f"{meta.get('decls')} declarations, pin {str(meta.get('pin_commit'))[:7]})")
    return 0


def cmd_show(a) -> int:
    db = Statements(Path(a.tsv))
    rows = db.find(a.name, limit=a.limit)
    if not rows:
        print(f"statement_db: nothing named {a.name!r}", file=sys.stderr)
        return 1
    if not a.json and not a.limit and len(rows) > 12:
        print(f"{len(rows)} declarations match {a.name!r}; first 20:", file=sys.stderr)
        for r in rows[:20]:
            print(f"  {r['path']}:{r['line']}  {r['name'] or '<anonymous>'}")
        return 0
    report_rows(rows, db.meta, a.json)
    return 0


def cmd_grep(a) -> int:
    db = Statements(Path(a.tsv))
    rows = db.search(a.pattern, kind=a.kind, public_only=a.public,
                     regex=a.regex, limit=a.limit)
    if not rows and not a.regex and "\\" in a.pattern:
        print("statement_db: literal search (use --regex for a pattern); nothing "
              "matched the backslash literally", file=sys.stderr)
    if a.json:
        report_rows(rows, db.meta, True)
        return 0
    for r in rows:
        priv = "*" if r["private"] else " "
        label = r["name"] or "<anonymous instance>"
        print(f"{priv}{r['path']}:{r['line']}  {label} ({r['kind']})")
        print(f"   {r['sig'][:200]}")
    print(f"\n{len(rows)} declaration(s)", file=sys.stderr)
    return 0 if rows else 1


def cmd_file(a) -> int:
    db = Statements(Path(a.tsv))
    rows = db.file(a.path)
    if not rows:
        print(f"statement_db: no declarations indexed for {a.path!r} (path is "
              f"relative to the pin root)", file=sys.stderr)
        return 1
    report_rows(rows, db.meta, a.json)
    return 0


def cmd_stats(a) -> int:
    print(json.dumps(Statements(Path(a.tsv)).stats(), indent=1))
    return 0


# -------------------------------------------------------------------- selfcheck
SAMPLE = [
    "Definitions/Def_ModularCurve_X0.lean",
    "Definitions/Def_ModularForm_HeckeOperator.lean",
    "Theorems/Thm_ModularCurve_coeffEmb_qExpand.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ord_nonneg_of_mem.lean",
    "P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean",
    "Definitions/Def_NumberField_HeightOneSpectrum.lean",   # anonymous instances
]


def _sample_files(pin: Path) -> list[str]:
    want = [rel for rel in SAMPLE if (pin / rel).exists()]
    if len(want) < 3:                     # a re-pinned clone may not have our names
        for rel, _s, _m in pin_files(pin):
            if rel.startswith("Definitions/"):
                want.append(rel)
            if len(want) >= 5:
                break
    return want


def selftest() -> int:
    pin = PIN_DEFAULT
    if not pin.is_dir():
        sys.exit(f"statement_db selftest: pin clone not found at {pin}")
    out = CACHE / "selftest.tsv"
    out.parent.mkdir(parents=True, exist_ok=True)
    files = _sample_files(pin)
    rows_all = []
    n = nanon = 0
    for rel in files:
        text = (pin / rel).read_text(encoding="utf-8")
        rows, _lines = parse_file(rel, text)
        n += len(rows)
        nanon += sum(1 for r in rows if r[7])
        # (1) the corpus's statement view == the legacy checker's own parse
        mine = [(r[2], r[5], r[8]) for r in rows if not r[7]]
        theirs = [(raw, kind, stmt) for raw, kind, stmt
                  in P.raw_declarations(text, include_private=True)]
        assert len(mine) == len(theirs), (rel, len(mine), len(theirs))
        for k, (x, y) in enumerate(zip(mine, theirs)):
            assert x[0] == y[0], f"{rel} #{k} name {x[0]!r} != {y[0]!r}"
            assert x[1] == y[1], f"{rel} #{k} kind {x[1]!r} != {y[1]!r}"
            assert x[2] == y[2], f"{rel} #{k} stmt differs:\n  file: {x[2]!r}\n  ck: {y[2]!r}"
        # (2) the signature re-normalises to the stored statement
        for line, end_line, name, _key, last, kind, priv, anon, stmt, raw, nhash in rows:
            assert nhash == hashlib.sha1(stmt.encode()).hexdigest()[:20], name
            assert raw.strip(), f"{rel}:{line} empty signature"
            if kind not in ("structure", "class"):
                again = P.norm(raw[:P.top_level_cut(raw)])
                assert again.endswith(stmt), (
                    f"{rel}:{line} {name} signature/norm drift:\n"
                    f"  sig->{again!r}\n  stmt->{stmt!r}")
                if not anon:
                    assert last in raw, name
            rows_all.append((rel, (line, end_line, name, "", last, kind, priv, anon,
                                   stmt, raw, nhash)))
    # (3) write a corpus and exercise every query path, with rg and without
    tsv = out.with_name("selftest-c.tsv")
    idx = tsv.with_suffix(".idx")
    with tsv.open("wb") as fh, idx.open("w", encoding="utf-8") as ix:
        pos = 0
        for rel in files:
            mine = [r for r in rows_all if r[0] == rel]
            data = "".join(row_line(rel, r[1]) for r in mine).encode("utf-8")
            fh.write(data)
            ix.write(f"{rel}\t{pos}\t{pos + len(data)}\t{len(mine)}\n")
            pos += len(data)
    tsv.with_suffix(".json").write_text(json.dumps({
        "format": FORMAT, "pin_commit": pin_commit(pin),
        "checker_sha1": checker_sha1(), "builder_sha1": builder_sha1(),
        "files": len(files), "decls": len(rows_all),
        "kinds": dict(Counter(r[1][5] for r in rows_all)),
    }))
    for use_rg in (True, False):
        db = Statements(tsv, use_rg=use_rg)
        rel, r0 = rows_all[0]
        got = db.file(rel)
        assert got, f"file() empty (rg={use_rg})"
        assert db.at(rel, r0[0]), f"at() (rg={use_rg})"
        assert db.find(r0[2]), f"find(name) (rg={use_rg})"
        assert db.find(r0[4]), f"find(last) (rg={use_rg})"
        assert db.by_hash(r0[8], r0[5]), f"by_hash (rg={use_rg})"
        assert db.search(r0[4]), f"search (rg={use_rg})"
    for p in (tsv, idx, tsv.with_suffix(".json")):
        p.unlink(missing_ok=True)
    print(f"statement_db selftest ok ({n} declarations, {nanon} anonymous, "
          f"{len(files)} files, 16 assertions)")
    return 0


def verify(a) -> int:
    """Every pin file the legacy checker reads: the corpus must equal its parse."""
    pin = Path(a.pin)
    sources = legacy_source_files()
    db = Statements(Path(a.tsv))
    checked = mismatched = missing = 0
    for rel in sources:
        p = pin / rel
        if not p.exists():
            continue
        rows = db.file(rel)
        if not rows:
            missing += 1
            print(f"NOT INDEXED  {rel}", file=sys.stderr)
            continue
        theirs = [(raw, kind, hashlib.sha1(stmt.encode()).hexdigest()[:20])
                  for raw, kind, stmt
                  in P.raw_declarations(p.read_text(encoding="utf-8"),
                                         include_private=True)]
        mine = [(r["name"], r["kind"], r["nhash"]) for r in rows if not r["anon"]]
        checked += 1
        if mine != theirs:
            mismatched += 1
            for k, (x, y) in enumerate(zip(mine, theirs)):
                if x != y:
                    print(f"MISMATCH  {rel} #{k}\n  corpus: {x}\n  checker: {y}",
                          file=sys.stderr)
                    break
            if len(mine) != len(theirs):
                print(f"  {rel}: {len(mine)} rows vs {len(theirs)} declarations",
                      file=sys.stderr)
    print(f"verify: {checked} SOURCES files agree, {mismatched} differ, "
          f"{missing} not indexed (pin {db.meta.get('pin_commit', '')[:7]})")
    return 0 if (mismatched == 0 and missing == 0) else 1


# ------------------------------------------------------------------------ main
def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--pin", default=str(PIN_DEFAULT))
    ap.add_argument("--tsv", default=str(TSV_DEFAULT))
    ap.add_argument("--jobs", type=int, default=min(16, os.cpu_count() or 4))
    ap.add_argument("--quiet", action="store_true")
    sub = ap.add_subparsers(dest="cmd")

    def common(p):
        p.add_argument("--pin", default=argparse.SUPPRESS)
        p.add_argument("--tsv", default=argparse.SUPPRESS)
        p.add_argument("--jobs", type=int, default=argparse.SUPPRESS)
        p.add_argument("--quiet", action="store_true", default=argparse.SUPPRESS)
        return p

    for name, fn, help_ in (
            ("build", cmd_build, "parse the pin into the corpus"),
            ("update", cmd_update, "rebuild if the pin or the parser moved"),
            ("check", cmd_check, "exit 1 if the corpus is stale")):
        common(sub.add_parser(name, help=help_)).set_defaults(fn=fn)

    p = common(sub.add_parser("show", help="the statement(s) for a name"))
    p.add_argument("name")
    p.add_argument("--limit", type=int, default=0)
    p.add_argument("--json", action="store_true")
    p.set_defaults(fn=cmd_show)

    p = common(sub.add_parser("grep", help="substring/regex search over the corpus"))
    p.add_argument("pattern")
    p.add_argument("--kind", default=None)
    p.add_argument("--public", action="store_true")
    p.add_argument("--regex", action="store_true")
    p.add_argument("--limit", type=int, default=0)
    p.add_argument("--json", action="store_true")
    p.set_defaults(fn=cmd_grep)

    p = common(sub.add_parser("file", help="every declaration of one pin file"))
    p.add_argument("path")
    p.add_argument("--json", action="store_true")
    p.set_defaults(fn=cmd_file)

    common(sub.add_parser("stats", help="counts and the build stamp")).set_defaults(
        fn=cmd_stats)
    common(sub.add_parser("verify", help="corpus == the legacy checker's parse")).set_defaults(
        fn=verify)
    common(sub.add_parser("selftest", help="check the parser, signatures and queries")).set_defaults(
        fn=lambda a: selftest())

    a = ap.parse_args()
    if not a.cmd:
        ap.print_help()
        return 2
    return a.fn(a)


if __name__ == "__main__":
    raise SystemExit(main())
