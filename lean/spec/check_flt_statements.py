#!/usr/bin/env python3
"""Diff every Layer 0 port declaration's *statement* against the pinned FLT source.

The name/statement check was first run by hand on Layer 0a, and automating it was
a stated follow-up. This does that: for each declaration in the port, it
finds the declaration of the same name in the pinned FLT clone and compares the
statement (signature up to the first top-level `:=` / `where`; for a `structure`,
the header plus the ordered field names). Proof bodies are deliberately ignored —
the port adapts proofs, never statements.

Usage:

    python3 spec/check_flt_statements.py [--flt ~/proj/fermats-last-theorem]

Exit status is 0 when every statement matches, 1 otherwise.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent  # lean/

# Port module -> the pinned FLT files its declarations are transcribed from.
# A declaration is looked up by name across all of these.
SOURCES = [
    "Definitions/Def_ModularCurve_X0.lean",
    "Definitions/Def_ModularCurve_LaurentCoeff.lean",
    "Definitions/Def_ModularCurve_PhiGen.lean",
    # The cone's outbound interface. These nine live in `Defs/Laurent.lean` and
    # `Defs/Jq.lean` with the objects they concern; their pin statements are the
    # `Theorems/` wrappers, so they are *verified* rather than exempted. The
    # wrappers come before the solution file because `coeffEmb_qExpand` also
    # occurs there in the `W1` implicit-`K` form; the public wrapper (explicit
    # `L`, matching our `coeffEmb`) is the interface we match.
    "Theorems/Thm_ModularCurve_coeffMap_qExpand.lean",
    "Theorems/Thm_ModularCurve_coeffEmb_qExpand.lean",
    "Theorems/Thm_ModularCurve_coeffMap_injective.lean",
    "Theorems/Thm_ModularCurve_coeffEmb_injective.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_prime.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_prime_pow.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean",
    "Theorems/Thm_ModularCurve_aeval_jq_eq_zero.lean",
    "Theorems/Thm_ModularCurve_transcendental_jq.lean",
    "P2M/Sol/S_ModularCurve_functionFieldGeneration.lean",
    "Theorems/Thm_ModularCurve_functionFieldGeneration_iff_full_eq.lean",
    # The generic kernel of `FLTForHuman/FieldTheory/CommonRoot.lean`. The three
    # `Polynomial.*` lemmas are stated verbatim from their `Theorems/` wrappers;
    # the pin's `S_Polynomial_mem_range_of_unique_common_root.lean` carries them
    # as `private` declarations, which the checker skips, so the wrappers are the
    # only comparable copy.
    "Theorems/Thm_Polynomial_mem_range_of_unique_common_root.lean",
    "Theorems/Thm_Polynomial_mem_range_of_eval_eq_const.lean",
    "Theorems/Thm_Polynomial_irreducible_of_transitive_ringAut.lean",
    # The peel: `ModularCurve.relfinrank_modularFunctionField`, now a public
    # lemma in `Defs/Fields.lean` beside the fields it concerns.
    "Theorems/Thm_ModularCurve_relfinrank_modularFunctionField.lean",
]

PORT_FILES = [
    "FLTForHuman/FieldTheory/CommonRoot.lean",
    "FLTForHuman/ModularCurve/Defs/Laurent.lean",
    "FLTForHuman/ModularCurve/Defs/Twist.lean",
    "FLTForHuman/ModularCurve/Defs/Jq.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean",
    "FLTForHuman/ModularCurve/Defs/Polynomial.lean",
    "FLTForHuman/ModularCurve/Defs/Fields.lean",
    "FLTForHuman/ModularCurve/Defs/PhiGen.lean",
    "FLTForHuman/ModularCurve/Defs/TS.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean",
    "FLTForHuman/ModularCurve/JqCoefficients.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean",
]

# Declarations whose *statement* has no FLT source, so there is nothing to diff:
# they are our own, not transcribed. `coeff_jq_zero` / `coeff_jq_one` state the
# regular low coefficients of `jq` (base/004: `q⁻¹ + 744 + 196884 q + ⋯`). FLT
# reaches those numbers only inside the deferred modular-form q-expansion cluster
# (`hasSum_jq_qParam` is a different statement), and its declarations there carry
# different names, so the pin has no name/statement to compare against. The proof
# here uses mathlib's pentagonal route over `etaProd`; see
# `FLTForHuman/ModularCurve/JqCoefficients.lean` and `topics/functionFieldGeneration/TOPIC-jq-coefficients.md`.
# Listing them explicitly keeps "0 missing" meaningful: an unlisted new
# declaration still fails the check.
OWN_PROOFS = {
    "coeff_jq_zero",
    "coeff_jq_one",
    # `Spine.lean`'s public surface. `Tight`/`Gen`/`Hall` are FLT's private
    # abbreviations in `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean`
    # (lines 413–419), promoted to public here so a later discharge can name them;
    # the script only reads non-private declarations, so it cannot see the pin's.
    # `Inputs` and `functionFieldGeneration_of` are ours: `Inputs` bundles FLT's
    # significant statements and has no counterpart to diff, and the capstone is
    # the conditional artifact of TOPIC-conditional-capstone.md, not a node in the
    # pin. Their auxiliaries are `private` and so are invisible to the checker.
    "Tight",
    "Gen",
    "Hall",
    "Inputs",
    "functionFieldGeneration_of",
}

# Declaration keywords. `instance` matters for PhiGen; `structure` for Polynomial.
DECL_RE = re.compile(
    r"^(?P<kind>def|theorem|lemma|abbrev|structure|instance)\s+"
    r"(?P<name>[\w.'ₐ]+)",
    re.MULTILINE,
)
FIELD_RE = re.compile(r"^\s{2,}([\w'ₐ]+)\s*:", re.MULTILINE)


def strip_comments(text: str) -> str:
    """Remove Lean block comments so prose does not pollute a statement."""
    return re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)


def top_level_cut(text: str) -> int:
    """Index of the first `:=` or `where` outside any bracket pair."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            if text.startswith(":=", i):
                return i
            if text.startswith("where", i):
                before = text[i - 1] if i else " "
                after = text[i + 5] if i + 5 < n else " "
                if not (before.isalnum() or before == "_") and not (
                    after.isalnum() or after == "_"
                ):
                    return i
        i += 1
    return n


def norm(text: str) -> str:
    # Both the port and the definitions layer spell these declarations inside
    # `namespace ModularCurve`, but the `Theorems/` wrappers additionally qualify
    # every occurrence with the namespace. That qualification is noise for a
    # statement diff, so drop it on both sides before comparing.
    text = re.sub(r"\bModularCurve\.", "", strip_comments(text))
    return re.sub(r"\s+", " ", text).strip()


def declarations(text: str) -> dict[str, tuple[str, str]]:
    """name -> (kind, normalized statement)."""
    text = strip_comments(text)
    matches = list(DECL_RE.finditer(text))
    out: dict[str, tuple[str, str]] = {}
    for idx, m in enumerate(matches):
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        chunk = text[m.end() : end]
        name = m.group("name").rsplit(".", 1)[-1]
        kind = m.group("kind")
        if kind == "structure":
            stmt = norm(chunk[: top_level_cut(chunk)]) + " FIELDS " + " ".join(
                FIELD_RE.findall(chunk)
            )
        else:
            stmt = norm(chunk[: top_level_cut(chunk)])
        # First occurrence wins; later duplicates would be redefinitions.
        out.setdefault(name, (kind, stmt))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--flt",
        default=str(Path.home() / "proj" / "fermats-last-theorem"),
        help="path to the pinned fermats-last-theorem clone",
    )
    args = ap.parse_args()
    flt = Path(args.flt)

    source: dict[str, tuple[str, str, str]] = {}
    for rel in SOURCES:
        p = flt / rel
        if not p.exists():
            print(f"warning: missing source {p}", file=sys.stderr)
            continue
        for name, (kind, stmt) in declarations(p.read_text(encoding="utf-8")).items():
            source.setdefault(name, (kind, stmt, rel))

    ok = missing = mismatch = own = 0
    for rel in PORT_FILES:
        p = LEAN / rel
        for name, (kind, stmt) in declarations(p.read_text(encoding="utf-8")).items():
            if name in OWN_PROOFS:
                own += 1
                continue
            if name not in source:
                print(f"MISSING IN FLT  {rel}: {name}")
                missing += 1
                continue
            skind, sstmt, srel = source[name]
            if kind == skind and stmt == sstmt:
                ok += 1
            else:
                mismatch += 1
                print(f"MISMATCH  {rel}: {name}  (source {srel}, {skind})")
                print(f"    port: {stmt}")
                print(f"    flt : {sstmt}")

    print(
        f"\n{ok} statements identical, {mismatch} mismatched, {missing} missing, "
        f"{own} own-proof declarations exempted "
        f"({ok + mismatch + missing + own} port declarations checked)"
    )
    return 0 if mismatch == 0 and missing == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
