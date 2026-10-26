#!/usr/bin/env python3
"""The statement parser shared by the new checker, the corpus and the planning tools.

This module is the *owner* of "the same statement": the declaration regex, the
enclosing-namespace tracker, the statement normaliser (`norm`), the declaration
walk (`raw_declarations` / `declarations` / `declaration_bodies`), the name
helpers (`promoted_key`, `strip_pin_prefix`, `same_kind`) and their tables.

It used to live inside `spec/old_check_stmts.py`.  The legacy checker is now a
consumer, not the owner: it imports these names (see the top of that file) so its
frozen behaviour is unchanged, while `spec/statement_db.py` and
`spec/check_port.py` -- and the tools in `tools/deps/` -- import this module
directly instead of loading the legacy registry.

One behaviour is corrected relative to the old copy: an `end` now closes as many
*n namespace components* as its dotted name carries (`end A.B` closes two), and
`pop_frames` consumes those components from the frames.  The old tracker popped
exactly one frame, so a file writing `end GroupTheory.BassSerre` over two separate
opens carried a doubled `GroupTheory.GroupTheory.` prefix on every later
declaration (and the dedup tools under-reported duplicates for it).  The component
count, not a frame count, is what keeps the other shape right: `namespace I.R …
end I.R` inside an outer namespace pushes **one** dotted frame and must pop
**one**, while `namespace A … namespace B … end A.B` pushes two frames and must
pop two.  `pop_frames` is the one pop.

No registry, no source lists, no pin access: this module only parses text.
"""
from __future__ import annotations

import re

# Declaration keywords. `instance` matters for PhiGen; `structure` for Polynomial.
# The optional `mods` group carries `private` and/or `noncomputable`. `private`
# is what lets the *source* side see the pin's `private` helpers: FLT keeps the
# shared `TPoleOrderLE` prelude private in the six files that repeat it (or
# exposes it only through its `p2m_export` alias, a command the text checker
# cannot follow), yet the port promotes it into `Defs/` so later modules can
# import it. Port declarations are still read without the `private` flag, so a
# `private` port helper is never diffed. `noncomputable` (SET-3 T7) exposes the
# pin's inline `noncomputable def`s, e.g. `Def_LaurentSeries_Hecke{U,V}.lean`'s
# `heckeU`/`heckeV`/`heckeT`; the port writes `noncomputable section` + plain
# `def`, so only the source side needed the extra alternative.
# The optional leading `attrs` group makes an attributed declaration on a single
# line (`@[scoped simp] theorem qTwistEquiv_apply …`, T14) visible. Without it
# the regex anchors on `theorem`, so such a declaration was invisible on *both*
# sides; with it, the port's copy is verified like any other. Adding it changed
# no other match (T14 re-ran the checker: 0 mismatched, 0 missing).
DECL_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]\n]*\]\s*)*)(?P<mods>(?:(?:private|noncomputable)\s+)*)"
    r"(?P<kind>def|theorem|lemma|abbrev|structure|class|instance)\s+"
    r"(?P<name>[\w.'ₐ]+)",
    re.MULTILINE,
)
FIELD_RE = re.compile(r"^\s{2,}([\w'ₐ]+)\s*:", re.MULTILINE)


# Enclosing-namespace tracking.  The same last name can occur twice in one pinned
# file under two different namespaces (e.g. `ModularForm.heckeTLin` and
# `CuspForm.heckeTLin` in `Def_ModularForm_HeckeOperatorForms.lean`, or
# `PowerSeries.heckeU` and `ModularForm.heckeU` across two definition files).  The
# last-name lookup keeps only the first; qualifying each declaration by its
# enclosing `namespace` gives the checker's dotted fallback a key for the second.
# `section`/`mutual` openers are tracked too, because `end` closes whichever is
# innermost.  Only key construction changes; the last-name (`name`) lookups are
# untouched.
ENCLOSE_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?P<ns>namespace)\s+(?P<nsname>[\w.']+)"
    r"|(?P<sec>(?:(?:noncomputable|private|protected)\s+)*section)\b"
    r"|(?P<mut>mutual)\b"
    r"|(?P<end>end)\b(?:\s+(?P<endname>[\w.\x27]+))?)",
    re.MULTILINE,
)


def strip_line_comments(text: str) -> str:
    """Drop `--` comments (used only for the namespace scan)."""
    return re.sub(r"--[^\n]*", "", text)


def namespace_events(text: str) -> list[tuple[int, str, str | None]]:
    """(position, kind, name) for every namespace/section/mutual/end at line start."""
    out: list[tuple[int, str, str | None]] = []
    for m in ENCLOSE_RE.finditer(strip_line_comments(text)):
        if m.group("ns"):
            out.append((m.start(), "ns", m.group("nsname")))
        elif m.group("mut"):
            out.append((m.start(), "sec", None))
        elif m.group("sec"):
            out.append((m.start(), "sec", None))
        else:
            out.append((m.start(), "end", m.group("endname")))
    return out


def enclosing_namespace(stack: list[str | None]) -> str:
    return ".".join(x for x in stack if x)


def pop_frames(stack: list[str | None], ename: str | None) -> None:
    """Close the frames a Lean `end` closes.

    `end` closes one frame; `end A` closes the namespace/section named `A`;
    `end A.B` closes both `B` and `A`.  Lean counts *namespace components*, not
    commands: a single `namespace A.B` pushes one frame that carries two
    components, so `end A.B` pops that one frame; two separate opens `namespace A`
    / `namespace B` push two frames, so the same `end A.B` pops both.  A
    `section`/`mutual` frame counts one component (`None`), because its `end`
    closes it whether or not the command carries a name.
    """
    want = len(ename.split(".")) if ename else 1
    while want > 0 and stack:
        frame = stack.pop()
        # one *open command* pushes one frame; a dotted open (`namespace A.B`)
        # carries several namespace components in that one frame, so it can
        # close several components of an `end A.B` at once.
        want -= len(frame.split(".")) if frame else 1


def strip_comments(text: str) -> str:
    """Remove Lean block comments so prose does not pollute a statement."""
    return re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)


def top_level_cut(text: str) -> int:
    """Index of the first `:=` or `where` outside any bracket pair.

    A `:=` that closes a `let`/`letI`/`let rec` *binding in the type* is not the
    declaration's body separator.  `theorem haar_facts : letI := glBorel … ; …`
    (the adèlic measure prelude of the
    `S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType*` family)
    was cut at that binding, so every such statement read as the literal `': letI'`
    — and any two `let`-headed declarations then compared equal, a check that
    cannot fail.  24 port declarations and 75 pin `SOURCES` declarations were in
    that class; their ports were faithful, but had never actually been diffed, and
    `port_advise` reported a spurious substitution off the same truncation
    (`haar_facts` "already in the port" as
    `AlgebraicCurve.Place.polynomialAlgebra_algebraMap_X`).  Count the pending
    binders at bracket depth 0 and consume their `:=` instead.  2026-10-11.
    """
    depth = 0
    pending_lets = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
            i += 1
            continue
        if c in ")]}":
            depth -= 1
            i += 1
            continue
        if depth != 0:
            i += 1
            continue
        if text.startswith(":=", i):
            if pending_lets:
                pending_lets -= 1
                i += 2
                continue
            return i
        if text.startswith("where", i):
            before = text[i - 1] if i else " "
            after = text[i + 5] if i + 5 < n else " "
            if not (before.isalnum() or before == "_") and not (
                after.isalnum() or after == "_"
            ):
                return i
        before = text[i - 1] if i else " "
        if not (before.isalnum() or before == "_"):
            for tok in ("letrec", "letI", "let_fun", "let"):
                if text.startswith(tok, i):
                    k = i + len(tok)
                    if not (k < n and (text[k].isalnum() or text[k] == "_")):
                        pending_lets += 1
                        i = k
                        break
            else:
                i += 1
        else:
            i += 1
    return n


# Junk tokens that the pin uses as a leading name segment in its generated
# `kw*` blocks (`kw_surgehgf4_hfgkd_ktd_…`, `kw_mlc_hrt…`, `kw_ffgc_…`); they
# carry no mathematical content and the port drops them.  They are erased in
# `norm` too, so a renamed statement that mentions one still matches the pin.
# Step labels (`s12`, `s17`, `v277`, …) are deliberately *not* here: they mark
# pin proof steps and are kept.
KW_JUNK_TOKENS = (
    "surgehgf4", "surge", "hgf4", "dcao", "ffgc", "fdn2", "qephod", "hend21",
    "hk5f", "taseq", "kqe", "hID", "pck", "qtzz", "hH2f", "hH2", "hfgkd",
    "ktd", "cfe", "hBC", "hu5c", "hKD", "ipfd", "HZZ", "mlc", "es", "no6",
    "iucz", "vdcoog", "affod", "vdc", "no3ahbad_riqsucr_a1a",
    "hH2a", "hH2b", "hH2c", "hH2d", "hH2e", "hH2f", "hH2g", "hH2h", "hH2i",
    "hH2j", "hH2k", "hH2l", "hH2m", "hH2n", "hH2o", "hH2p", "hH2q", "hH2r",
    "hH2s", "hH2t", "hH2u", "hH2v", "hH2w", "hH2x", "hH2y", "hH2z",
)
_KW_JUNK_RE = re.compile(
    r"(?<![\w'ₐ-ₜ])(?:" + "|".join(map(re.escape, KW_JUNK_TOKENS)) + r")_"
)
# The `kw*` prefix matcher shared with `spec/check_port.py`'s residual-name
# guard: a port declaration whose last name matches this is a regression.
# `norm` erases the match; the guard rejects the name.  Both use this one
# object, so the two can never drift.
KW_PREFIX_RE = re.compile(
    r"(?:(?<![\w'ₐ-ₜ])|(?<=_))(?:kw[^\W_]*_|kw(?=[A-Z]))"
)
# The capital-`Kw` family: `KwD5…`, `KwF4…`, `KwTateRR3…`, `KwNo6…`,
# `KwVelu…`, `KwDual…`, … and the `Kw…` namespaces.  A declaration whose full
# name has such a segment is a residual; the port-side guard in
# `spec/check_port.py` rejects it.  The exact `Kw` abbreviation (`ArchInfra`'s
# row-isometry subgroup) is not a family name: the pattern requires an
# uppercase/digit immediately after `Kw`.  This is the *name* policy.
KW_FAMILY_RE = re.compile(
    r"(?:(?<![\w'])|(?<=_))Kw[A-Z0-9][A-Za-z0-9_']*")
# The rectification's statement normalisation for the capital family.  The
# generated block token is stripped as a unit: `KwF4gRRTate` → `Tate`,
# `KwF4R1V384aCompletion…` → `Completion…`, `KwTateRR3Cohen…` → `Cohen…`,
# `KwNo6Pin` → `Pin`, `KwD5Between…` → `Between…`.  A namespace that becomes
# empty (`KwF4R1V384a`, `KwTateRR3`, `KwOdaDHDR`, `KwNo3a…`) disappears, taking
# its dot with it.  Remaining `Kw` prefixes (`KwIsogeny…`, `KwVelu…`) are then
# erased by `KW_FAMILY_PREFIX_RE`.
KW_GENERATED_TOKENS = (
    "F4R1V384a", "F4R1V386a", "F4R1V391a", "F4R1V394a", "F4R1V410a",
    "F4R1V392a", "TateRR3", "No3aHbadRiqsucrA1a", "OdaDHDR", "HgfV352",
    "DCAO", "F4gRR", "Hgf", "No6", "D5",
)
KW_GENERATED_RE = re.compile(
    r"(?<![\w'])Kw(?:" + "|".join(
        map(re.escape, sorted(KW_GENERATED_TOKENS, key=len, reverse=True)))
    + r")(?:\.)?"
)
# The generic capital prefix, for the names that keep their suffix
# (`KwIsogenyEndDatum…` → `IsogenyEndDatum…`, `KwVelu…` → `Velu…`).
KW_FAMILY_PREFIX_RE = re.compile(r"(?<![\w'])Kw(?=[A-Z0-9])")
# The pin's informal-question / workspace labels: `Q09`, `Q09AIarch`, `Q09AIarchC`,
# `Q09AIarchG`, `Q09RowIso`.  They name the pin's proof scaffold — the question it answers and
# the workspace it was written in — not mathematics, and the sub-tokens (`AI`, `C`, `G`,
# `RowIso`, `Dock`) carry no meaning of their own.  The port states the subject
# (`ArchApproxIdentity`, `ArchInfra`, `ArchInfraTopology`, `ArchEntryBall`); `check_port`'s
# name guard rejects a residual family name, exactly as it does for `kw*`/`Kw*`.
Q09_FAMILY_RE = re.compile(r"(?:(?<![\w'ₐ-ₜ])|(?<=_))Q09[A-Za-z0-9_']*")
# A few names are renamed past their `norm` image because the mechanical target
# is ambiguous (`charFree` ×7, `proved` ×4, `map_eq` ×2, `axiomAnchor` ×3,
# `zero`/`some_of_mem`/`some_of_ne`, the `HZZ` family and the embedded `kwVelu…`
# names).  This map puts the port spelling back to the pin's normalised spelling
# before the hash is taken; it is the checker's rename exemption, not a
# declaration marker.  Keys are applied longest-first on word boundaries.
CANONICAL_NAMES = {
    # The Q09 sweep (2026-10-25).  `Q09`, `Q09AIarch`, `Q09AIarchC`, `Q09AIarchG` and `Q09RowIso`
    # are the pin's informal-question and workspace labels, not mathematics: the port states the
    # subject (`ArchApproxIdentity`, `ArchInfra`, `ArchEntryBall`).  Only `ArchInfra` occurs inside
    # a statement today (`exists_contDiff_dconvWith`), so only it needs a map entry; a statement
    # that ever mentions the merged `…C`/`…G`/`RowIso` blocks needs its own entry, and the failure
    # is a loud `MISMATCH`, never a silent match.
    'ArchInfra': 'Q09AIarch',
    'adicValuation_algebraMap_ramificationIndex': 'adicValuation_algebraMap',
    'axiomAnchor_hBC': 'axiomAnchor',
    'axiomAnchor_hfgkd_ktd': 'axiomAnchor',
    'axiomAnchor_pck': 'axiomAnchor',
    'completionTraceSum_of_isSeparable_aux': 'completionTraceSum_of_isSeparable',
    'Δ_ne_zero_of_isElliptic_local': 'Δ_ne_zero_of_isElliptic',
    'hDDTerm_velu': 'hDDTerm',
    'instHPD_dcao': 'instHPD',
    'LocalResiduePin': 'Pin',
    'LocalResidueSection': 'Section',
    'ffSeamBaseChange_proved': 'proved',
    'kerQuotEquivBC_map_eq': 'map_eq',
    'kerQuotEquivBC_proved': 'proved',
    'pmopConjKerEquiv_proved': 'proved',
    'point_infinite_charFree': 'point_infinite',
    'pmopConjKerEquiv_proved_core': 'proved_core',
    'sublatticeCoords': 'HZZ',
    'sublatticeCoords_index': 'index',
    'sublatticeCoords_map_eq': 'map_eq',
    'sublatticeIndex_scale': 'scale',
    'sublatticeQuotientZZTransport_proved': 'proved',
    'tisdCharFreeα': 'charFree',
    'tisdCharFreeβ': 'charFree',
    'tisdCharFreeγ': 'charFree',
    'tisdCharFreeδ0': 'charFree',
    'tisdCharFreeδ1': 'charFree',
    'tisdCharFreeδ2': 'charFree',
    'tisdCharFreeδY': 'charFree',
    'VeluPointMap_some_of_mem': 'some_of_mem',
    'VeluPointMap_some_of_ne': 'some_of_ne',
    'VeluPointMap_zero': 'zero',
    'VeluMapEquationAt_oddOrderSummingSet_odd': 'kwVeluMapEquationAt_oddOrderSummingSet_odd',
    'VeluXGenFun_mem_placeOfEquation_of_ne_odd': 'kwVeluXGenFun_mem_placeOfEquation_of_ne_odd',
    'VeluXGenFun_mul_denom_sq_eq_cleared': 'kwVeluXGenFun_mul_denom_sq_eq_cleared',
    'VeluXGenFun_notMem_of_not_isFinitePlace': 'kwVeluXGenFun_notMem_of_not_isFinitePlace',
    'VeluXGenFun_notMem_placeOfEquation_of_mem_odd': 'kwVeluXGenFun_notMem_placeOfEquation_of_mem_odd',
    'VeluYGenFun_mem_placeOfEquation_of_ne_odd': 'kwVeluYGenFun_mem_placeOfEquation_of_ne_odd',
    'VeluYGenFun_ne_algebraMap_odd': 'kwVeluYGenFun_ne_algebraMap_odd',
    'aeval_VeluXGenFun_injective': 'aeval_kwVeluXGenFun_injective',
    'equation_map_veluQuotient_VeluGenFun_odd': 'equation_map_veluQuotient_kwVeluGenFun_odd',
    'eval₂_polynomial_VeluGenFun_odd': 'eval₂_polynomial_kwVeluGenFun_odd',
    'restrictAlong_placeOfPoint_VeluPointMap_odd': 'restrictAlong_placeOfPoint_kwVeluPointMap_odd',
    'transcendental_VeluXGenFun': 'transcendental_kwVeluXGenFun',
}
_CANONICAL_RE = re.compile(
    r"(?<![\w'ₐ-ₜ])(?:" + "|".join(
        map(re.escape, sorted(CANONICAL_NAMES, key=len, reverse=True))) + r")(?![\w'ₐ-ₜ])"
)


def _canonical(text: str) -> str:
    return _CANONICAL_RE.sub(lambda m: CANONICAL_NAMES[m.group(0)], text)


def norm(text: str) -> str:
    # Both the port and the definitions layer spell these declarations inside
    # `namespace ModularCurve`/`namespace AlgebraicCurve`, but the `Theorems/`
    # wrappers additionally qualify every occurrence with the namespace. That
    # qualification is noise for a statement diff, so drop it on both sides
    # before comparing.
    text = re.sub(r"\bModularCurve\.", "", strip_comments(text))
    text = re.sub(r"\bAlgebraicCurve\.", "", text)
    # A `kw*` name is a collision token, not mathematics.  The `kw_` form is the
    # promotion convention (`kw_g₂_ofTau` -> `g₂_ofTau`); the `kwF4R1V384a_*`,
    # `kwTateRR*_*`, `kwTISDα_*` forms are generated prefixes kept from the pin.
    # Both are noise for a statement diff, exactly as a namespace prefix is, and
    # both must be erased *inside* statements too, not only on the declaration
    # name: a declaration whose statement mentions a renamed helper (say
    # `kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X`, which states
    # `kw_functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X)
    # = polyToFunctionField (W⁄F') X`) could otherwise not be promoted at all —
    # the renamed helper would change the statement text and the diff would
    # fail.  Two rules make the general `kw*` family noise:
    #
    #   1. `kw` + word characters + `_` is the generated form; drop the whole
    #      prefix through the first `_`, so `kw_foo` -> `foo` and
    #      `kwF4R1V384a_foo` / `kwTISDα_charFree` -> `foo` / `charFree`.
    #   2. a standalone `kwWord` (no `_`) keeps the word and loses only `kw`,
    #      so `kwVeluPointMap` -> `VeluPointMap` and `kwHgf` -> `Hgf`.
    #
    # The lookbehind keeps a `kw` inside a word (`backward`) untouched and allows
    # a preceding `.`, so method-style references (`L.kw_foo` -> `L.foo`) are
    # erased too (2026-10-06, D-5 §1.5: excluding `.` made
    # `PeriodPair.kw_toPointHom_apply` unmatchable after promotion).  Monotone:
    # both sides are normalised identically, so this can only turn a
    # mismatch/missing into a match, never the other way.
    text = KW_PREFIX_RE.sub("", text)
    # A `kw_` name can carry several junk segments (`kw_surgehgf4_hfgkd_ktd_…`);
    # erase the known leading ones repeatedly.  The loop is bounded: a segment
    # either disappears or the pattern is absent, and eight rounds cover the
    # deepest block in the port.
    for _ in range(8):
        text, n = _KW_JUNK_RE.subn("", text)
        if not n:
            break
    # The capital-`Kw` family is the same kind of collision token.  The generated
    # block token goes as a unit first (`KwF4gRRTate` → `Tate`,
    # `KwF4R1V384aCompletion…` → `Completion…`, `KwD5Between…` → `Between…`),
    # then the remaining generic `Kw` prefix (`KwIsogeny…` → `Isogeny…`).  The
    # exact `Kw` abbreviation is untouched.
    text = KW_GENERATED_RE.sub("", text)
    text = KW_FAMILY_PREFIX_RE.sub("", text)
    # The approved ambiguity fixes are not `norm` images of the old name, so the
    # explicit map puts the new spelling back to the pin's normalised spelling.
    text = _canonical(text)
    # The port homed the pin's re-carried `ValuationOrd` prelude once, in
    # `FLTForHuman/RingTheory/DiscreteValuationRing/Order.lean`, under mathlib's own
    # `IsDiscreteValuationRing` namespace (2026-10-13; see
    # `topics/automorphicForm/TOPIC-local-intertwining-weyl-integrand.md` §1 and
    # `CARRY-FORWARD.md`). A statement that *mentions* a member of that block therefore
    # differs from the pin only by that qualifier: the pin writes `ValuationOrd.ord`, the
    # port `IsDiscreteValuationRing.ord`. Erase both qualifiers when they qualify one of
    # the block's sixteen names, on both sides, exactly as the `kw_` prefix is erased. The
    # alternation is restricted to those names so that an unrelated
    # `IsDiscreteValuationRing.*` (mathlib's `addVal`, `idealOrderIsoENat`) is left alone.
    text = re.sub(
        r"\b(?:ValuationOrd|IsDiscreteValuationRing)\.(?=(?:ord_eq_zero_iff|"
        r"ord_ofMul_mk0_of_irreducible|ord_ofMul_of_mem|pow_maximalIdeal_injective|"
        r"pow_maximalIdeal_ne_of_lt|exists_span_eq_pow|ord_spec|ordA_unique|ordA_span|"
        r"ordA_mul|ordZ_spec|ordA|ordZ|exists_rep|coe_mk_ne_zero|ord)\b)",
        "",
        text,
    )
    return re.sub(r"\s+", " ", text).strip()


def raw_declarations(text: str, include_private: bool = False) -> list[tuple[str, str, str]]:
    """(raw name, kind, normalized statement) for each declaration in `text`.

    With `include_private`, the pin's `private` declarations are read too; the
    port side never passes it (a private port helper is not part of the surface
    being verified).
    """
    text = strip_comments(text)
    matches = list(DECL_RE.finditer(text))
    events = namespace_events(text)
    out: list[tuple[str, str, str]] = []
    stack: list[str | None] = []
    ei = 0
    for idx, m in enumerate(matches):
        while ei < len(events) and events[ei][0] < m.start():
            _, ekind, ename = events[ei]
            if ekind == "ns":
                stack.append(ename)
            elif ekind == "sec":
                stack.append(None)
            else:
                pop_frames(stack, ename)
            ei += 1
        if "private" in m.group("mods") and not include_private:
            continue
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        chunk = text[m.end() : end]
        kind = m.group("kind")
        if kind in ("structure", "class"):
            stmt = norm(chunk[: top_level_cut(chunk)]) + " FIELDS " + " ".join(
                FIELD_RE.findall(chunk)
            )
        else:
            stmt = norm(chunk[: top_level_cut(chunk)])
        prefix = enclosing_namespace(stack)
        name = m.group("name")
        raw = f"{prefix}.{name}" if prefix else name
        out.append((raw, kind, stmt))
    return out


def declarations(text: str) -> dict[str, tuple[str, str]]:
    """last name component -> (kind, normalized statement)."""
    out: dict[str, tuple[str, str]] = {}
    for raw, kind, stmt in raw_declarations(text):
        # First occurrence wins; later duplicates would be redefinitions.
        out.setdefault(raw.rsplit(".", 1)[-1], (kind, stmt))
    return out


# A `def`'s body starts at the declaration's top-level `:=`/`where` and runs to
# the next line at column 0 that opens a new command (Lean indents tactic blocks
# and term continuations, so a column-0 command keyword ends the body).
DEF_BODY_CMD_RE = re.compile(
    r"^(?:end|namespace|section|variable|variable'|theorem|lemma|def|abbrev|private|"
    r"protected|noncomputable|set_option|attribute|open|instance|scoped|local|@\[|"
    r"p2m_|example|#|include|omit|universe|class|structure|inductive|opaque|axiom|"
    r"notation|macro|syntax|elab|deriving|export|initialize|run_cmd)\b"
)


def declaration_body(chunk: str) -> str:
    """The normalized body of a declaration chunk, after its top-level `:=`/`where`.

    Returns "" for a declaration with only a type (`axiom`-like) or for a
    `structure` (whose fields `raw_declarations` already carries).
    """
    cut = top_level_cut(chunk)
    if cut >= len(chunk):
        return ""
    keep = []
    for i, line in enumerate(chunk[cut:].split("\n")):
        if i and line[:1] not in ("", " ", "\t") and DEF_BODY_CMD_RE.match(line):
            break
        keep.append(line)
    return norm("\n".join(keep))


def declaration_bodies(
    text: str, include_private: bool = False
) -> list[tuple[str, str, str, str]]:
    """(raw name, kind, normalized statement, normalized body) per declaration.

    The statement is computed exactly as `raw_declarations` computes it, so a row
    here still agrees with the main pass; only the additional body is new.  Used
    by the opt-in `--prop-bodies` pass.
    """
    text = strip_comments(text)
    matches = list(DECL_RE.finditer(text))
    events = namespace_events(text)
    out: list[tuple[str, str, str, str]] = []
    stack: list[str | None] = []
    ei = 0
    for idx, m in enumerate(matches):
        while ei < len(events) and events[ei][0] < m.start():
            _, ekind, ename = events[ei]
            if ekind == "ns":
                stack.append(ename)
            elif ekind == "sec":
                stack.append(None)
            else:
                pop_frames(stack, ename)
            ei += 1
        if "private" in m.group("mods") and not include_private:
            continue
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        chunk = text[m.end() : end]
        kind = m.group("kind")
        if kind in ("structure", "class"):
            stmt = norm(chunk[: top_level_cut(chunk)]) + " FIELDS " + " ".join(
                FIELD_RE.findall(chunk)
            )
            body = ""
        else:
            stmt = norm(chunk[: top_level_cut(chunk)])
            body = declaration_body(chunk)
        prefix = enclosing_namespace(stack)
        name = m.group("name")
        raw = f"{prefix}.{name}" if prefix else name
        out.append((raw, kind, stmt, body))
    return out


def prop_body_key(body: str) -> str:
    """Body normalisation for the `--prop-bodies` comparison.

    Drops named-argument labels (`f (K := K) x` vs `f K x`) and the parentheses
    around a lone identifier (`f (K)` vs `f K`), which are elaboration spelling,
    not a different proposition.  Dot notation and implicit-argument placement
    still differ textually; those are reported for review.
    """
    key = re.sub(r"\((?:\w+'?)\s*:=\s*", "(", norm(body))
    return re.sub(r"\((\w+'?)\)", r"\1", key)


def promoted_key(raw: str) -> str:
    """The dotted name of a promoted declaration, for matching a public port
    declaration against the pin's `private` original.

    The port writes the shared prelude's methods as `theorem TPoleOrderLE.mono`
    (two components); the pin writes them as
    `private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.mono` (many). Both
    reduce to the last two components. Single-component names are unchanged, so
    `conjPoleBound` et al. still match, while the generic `neg`/`mul`/`qTwist`/
    `qExpand` no longer collide with the unrelated top-level declarations the
    last-name public lookup finds first.
    """
    # `_root_.` may now be preceded by an enclosing-namespace prefix, so strip it
    # wherever it occurs rather than only at the start.
    raw = re.sub(r"(?:^|\.)_root_\.", ".", raw).lstrip(".")
    parts = raw.split(".")
    return ".".join(parts[-2:]) if len(parts) >= 2 else parts[-1]


# The pin's `kw_*` helpers are collision tokens, not mathematics: the port promotes
# the general ones at the prefix-stripped name (`kw_g₂_ofTau` → `g₂_ofTau`).  The
# strip is applied to the **pin** side only, so a pin public name is never shadowed;
# it is a pure fallback consulted after the public and dotted lookups, and it still
# requires the `kind` and the normalised statement to match.  The token list starts
# minimal; see work-order §2.1 and
# `studies/pin-name-prefixes-and-the-checker.md` §5–§6.
PIN_PREFIXES = ("kw",)


def strip_pin_prefix(name: str) -> str | None:
    """The prefix-stripped last name of a pin declaration, or `None`.

    Only prefixes in `PIN_PREFIXES` followed by `_` are stripped, and the result must
    be non-empty: `kw_G_ofTau_eq` → `G_ofTau_eq`, `kw_` → `None`, `scale_lattice` →
    `None`.
    """
    for prefix in PIN_PREFIXES:
        head = prefix + "_"
        if name.startswith(head) and len(name) > len(head):
            return name[len(head):]
    return None


# `def`/`theorem`/`lemma`/`abbrev` all introduce the same thing — a named term
# with a type — and differ only in the reducibility/proof-irrelevance of the body,
# which this statement diff deliberately ignores ("the port adapts proofs, never
# statements"). The motivating case is the pin's `@[reducible] private def
# AlgebraicCurve.Place.polynomialIsScalarTower`, which the port's 2026-10-16
# build-time work rewrote as a `theorem` (same signature, now opaque); the checker
# reported a mismatch on byte-identical statement text. `structure`/`class`/
# `instance` stay distinct: those change the signature, not just the body.
KIND_EQUIV = {"def": "def", "theorem": "def", "lemma": "def", "abbrev": "def"}


def same_kind(a: str, b: str) -> bool:
    """Whether two declaration keywords are interchangeable for a statement diff."""
    return KIND_EQUIV.get(a, a) == KIND_EQUIV.get(b, b)
