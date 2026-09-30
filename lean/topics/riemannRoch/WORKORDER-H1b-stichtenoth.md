# Work order — H1b: the Stichtenoth genus-existence tower

**Status: DISPATCHED (2026-09-29).** H1a reviewed green (checker 2753/0/0,
`Genus/Index.lean` 1,517 lines, axioms clean). It already landed
`exists_genus_riemannIndex_of_stichtenothGenusExists` (and its wrapper-named body)
— **do not re-state it**; import it. Method and boilerplate are
`WORKORDER-H1a-index.md`; this order states only what differs. Plan: `PLAN.md` §2.

## 0. Scope

The genuinely new piece of phase 1: the `TranscendenceTower` / `PoleDivisorPackage`
→ `IntegralBasisInLSpace` / `HasRegularFractionSubring` → `RiemannGenusBounded` →
`StichtenothGenusExists` construction, plus `finiteDimensional_lSpace_zero_of_constantsAreBase`.
Union content **86 names / 949 once-each lines**, essentially all in
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`
(2,545 lines) — the pin's own proof, so this is transcription of a real
construction, not new mathematics. It is the **scout gate** (playbook §2.6):
before the full dispatch, prototype the
`TranscendenceTower → ofTranscendenceTower → poleDivisor → HasIntegralBasisInLSpace →
HasPoleDivisorPackage → stichtenothGenusExists_of_…` spine in `Scratch.lean` and
record the pre/post estimate; if it transcribes, the set is transcription and the
budget is ~950 lines.

**Prerequisite:** H1a (`indexOfSpecialty_sub_of_ge`, the `ell`/quotient prelude) and
Set D (`PoleDivisorPackage`, `TranscendenceTower`, `IntegralBasisInLSpace`,
`HasIntegralBasisInLSpace`, `HasIntegralBasisRegularOutside`,
`HasRegularFractionSubring`, `StichtenothGenusExists`, `RiemannGenusBounded`,
`IndexOfSpecialtyFinite`).

**Not this set:** H1a's index core, H2's assembly, H3's differentials. The RatFunc
tower tail (`transcendenceTower`, `ofTranscendenceTower`, `ord_X_nonneg_of_ne_placeInfty`,
`algebraMap_polynomial_mem_*`, `isFractionRing_adjoin_X`, `hasPoleDivisorPackage_of_ratFunc_tower`,
`indexOfSpecialtyFinite_of_ratFunc_tower`, `stichtenothGenusExists_of_ratFunc_tower`,
`exists_restrict_eq`) is **in** this set — it is the `RatFunc K` instance of the
tower that makes `stichtenothGenusExists` unconditional.

## 1. Deliverable

`FLTForHuman/AlgebraicCurve/Genus/Stichtenoth.lean`

- namespace `AlgebraicCurve`; imports Set D (`Defs.PoleDivisorPackage`,
  `Defs.AdelicIndex`, `Defs.IsCurveOver`, `Defs.RatFuncPlaces`) and
  `Genus.Index`; specific mathlib modules only
  (`Mathlib.FieldTheory.RatFunc.Basic`, `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, `Mathlib.FieldTheory.IsAlgClosed.Basic`).
- targets, spelled from their wrappers:
  `RationalFunctionField.stichtenothGenusExists`
  (`Theorems/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`)
  and `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase`
  (`Theorems/Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase.lean`).
- collapse the pin duplicates: `stichtenothGenusExists_port` ≡
  `stichtenothGenusExists`; `finiteDimensional_lSpace_zero_of_constantsAreBase_port`
  ≡ its target; write each once.

## 2. Route and risk

- **Route:** the pin's proof of `StichtenothGenusExists` is the chain in §0. The
  scout must confirm the two hard junctions: (a) `ofTranscendenceTower` building the
  `PoleDivisorPackage` from a `TranscendenceTower`, and (b) the `RatFunc` tower
  instance (`transcendenceTower`) via `placeInfty`, `IsFractionRing` and
  `adjoin X`. If either needs an unported pin wrapper (`ord_placeInfty`,
  `deg_placeInfty`, `IsCurveOver.exists_separating_transcendental`), **stop and
  report** — those are not in the port (verified) and belong to a focused support
  dispatch, not this set.
- **mathlib:** the audit (`AUDIT-mathlib.md`) records `finiteDimensional_lSpace_zero_of_constantsAreBase`
  as a **one-mathlib-call** proof (keep the pin statement, drop the pin body for
  the named lemma it reports). Otherwise `IntermediateField.adjoin`,
  `Algebra.IsIntegral.of_finite`, `IsFractionRing`, `LinearIndependent`,
  `Module.finrank`, `Finsupp.single`/`Finsupp.support`. Negatives that matter here:
  mathlib has no `genus`, no `RiemannRoch`, no `Algebra.adjoin_eq_self`; the
  `StichtenothGenusExists`/`PoleDivisorPackage` structures are BESPOKE and must be
  written as the pin writes them.
- **Stop-early risks:** the missing `RatFunc` tower wrappers of above; an
  `IntermediateField.adjoin`/defeq carrier mismatch (playbook §6: prove a generic
  coercion once at abstract carriers rather than `change`); a
  `linearIndependent_pow_mul` reindexing drift.
- Record every mathlib negative.

## 3. Verification, build discipline, report

As `WORKORDER-H1a-index.md` §4–§5, with:
- checker `SOURCES` += the pin `S_..._stichtenothGenusExists.lean` **and** the two
  `Theorems/Thm_AlgebraicCurve_RationalFunctionField_*` wrappers (wrappers first);
  `PORT_FILES` += `FLTForHuman/AlgebraicCurve/Genus/Stichtenoth.lean`.
- edit loop bounded 120 s (`lake env lean …`); file-done
  `flock /tmp/flt_for_human.lock timeout 180 lake build FLTForHuman.AlgebraicCurve.Genus.Stichtenoth`;
  iterate individual declarations in `Scratch.lean`.
- `#print axioms` on both headlines and on `RiemannGenusBounded`,
  `HasPoleDivisorPackage`.

## Appendix — the H1b declaration list

`tools/deps/build/rr_homes.txt`, section `### H1b` (86 rows). The two `_port`
duplicates collapse; the rest is the union.
