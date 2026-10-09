/-
  The `isAlgClosed` finrank/index bound for `K(jq)` in the `q`-expansion model
  (`P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean`,
  pin `aa2d8b3`), statement verbatim from
  `Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean`.

  This is the characteristic-`p` end of the index computation: for an arbitrary
  algebraically closed `K` (in particular `𝔽̄_p`) and `Γ ≤ Γ'` with the `±`-negation
  condition, the degree of `qExpFunctionFieldC K Γ` over `K⟮jqModC K⟯` is finite and
  bounded by `Γ'.index`. Its numeric input is SET-R-C order 1's `ℚ`-side bound,
  carried across the Deuring reduction of SET-R-D order 1 (which compares the two
  characteristics through a shared integral series pair); the characteristic-`p`
  case is what `solution`'s prime branch assembles.

  The engine of the pin's 87-line block — `isAlgebraic_residueField` (59 lines),
  `residueTopHom` (11) and `coe_eq_zero_of_mem_maximalIdeal_top` (8) — is the engine
  of SET-R-D order 2 and is already public in
  `FLTForHuman/ModularCurve/X1/FunctionFieldIsAlgClosed.lean` (namespace
  `ModularCurve.QExpBaseChange`); it is imported and reused, not transcribed. What
  remains genuinely new here is the `jqModC = jNum / X` presentation (`jqModC_eq_div`),
  its Laurent-base-change membership, the two-branch assembly `bound_of_place`, and
  the headline.

  The `ValuationSubring` residue block of the pin's
  `Def_WeierstrassCurve_ReductionMap.lean` is public in
  `FLTForHuman/NumberTheory/ValuationAtPlace.lean` and is imported through
  `FunctionFieldIsAlgClosed.lean`; the pin's `attribute [-simp]` scaffolding lines in
  the wrapper name declarations of unported modules and are not transcribed (in
  particular `ModularForm.heckeDiagMatrix_zero` / `heckeMatrix_zero`, which occur
  only there, are neither transcribed nor re-derived).

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean
-/
import FLTForHuman.ModularCurve.X1.FunctionFieldIsAlgClosed
import FLTForHuman.ModularCurve.Defs.QExpValuationReduction
import FLTForHuman.ModularCurve.X1.FunctionFieldDegree
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial

namespace ModularCurve

namespace DegKDeuring

/-! The pin's `Residue` block (`isAlgebraic_residueField`), its `CharZero` block
(`coe_eq_zero_of_mem_maximalIdeal_top`, `residueTopHom`) and the headline of
SET-R-D order 2 are the SET-R-D engine and are imported from
`FLTForHuman/ModularCurve/X1/FunctionFieldIsAlgClosed.lean` (namespace
`ModularCurve.QExpBaseChange`) rather than re-transcribed. -/

/-- The pin's `jqModC` presentation as the ratio of the integral series of
`jNum = E₄³` and of `X`. -/
theorem jqModC_eq_div (K : Type*) [Field K] :
    ModularCurve.jqModC K = ModularCurve.intSeriesC K ModularCurve.jNum / ModularCurve.intSeriesC K PowerSeries.X := by
  have hX : ModularCurve.intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
    simp [ModularCurve.intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  have hne : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ≠ 0 := by simp
  rw [hX, eq_div_iff hne, ModularCurve.jqModC, mul_comm (HahnSeries.single (-1 : ℤ) (1 : K)), mul_assoc,
    HahnSeries.single_mul_single]
  simp [ModularCurve.intSeriesC]

/-- `jqModC` lies in the Laurent base change of the `ℚ`-side `q`-expansion field. -/
theorem jqModC_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
  have h : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ Γ :=
    ModularCurve.intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)
  have e : ModularCurve.coeffEmb L (ModularCurve.jqModC ℚ) = ModularCurve.jqModC L :=
    ModularCurve.map_jqModC (algebraMap ℚ L)
  exact e ▸ ModularCurve.coeffEmb_mem_laurentBaseChange L h

/-- Deuring's bound over an arbitrary field `K` reached from a characteristic-`p`
residue field of a valuation subring of `L`, with a shared integral series pair. -/
theorem bound_of_place (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ) (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L) (π : A →+* K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index := by
  classical
  have hF := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L Γ hT
  set X : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) :=
    ⟨ModularCurve.jqModC L, jqModC_mem_laurentBaseChange L Γ⟩ with hXdef
  have hXab : (X : LaurentSeries L) =
      ModularCurve.intSeriesC L ModularCurve.jNum / ModularCurve.intSeriesC L PowerSeries.X := jqModC_eq_div L
  have hxab : (x : LaurentSeries K) =
      ModularCurve.intSeriesC K ModularCurve.jNum / ModularCurve.intSeriesC K PowerSeries.X :=
    hx.trans (jqModC_eq_div K)
  have htr : Transcendental K x := by
    have hinj : Function.Injective (algebraMap (ModularCurve.qExpFunctionFieldC K Γ) (LaurentSeries K)) :=
      (algebraMap (ModularCurve.qExpFunctionFieldC K Γ) (LaurentSeries K)).injective
    rw [← transcendental_algebraMap_iff hinj]
    change Transcendental K (x : LaurentSeries K)
    rw [hx]
    exact ModularCurve.transcendental_jqModC K
  obtain ⟨hfin, hle⟩ := ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring A π Γ hF
    ModularCurve.jNum PowerSeries.X X hXab x hxab htr
  exact ⟨hfin, hle.trans (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
    L Γ hT Γ' hΓ' hneg X rfl)⟩

end DegKDeuring

end ModularCurve

open ModularCurve.DegKDeuring in
/-- **The `isAlgClosed` finrank/index bound.** Verbatim from
`Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean`. -/
theorem ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
    haveI : CharP (IsLocalRing.ResidueField A) p :=
      ValuationSubring.charP_residueField_of_liesOverPrime_def hp hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    letI := ZMod.algebra K p
    haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) :=
      ModularCurve.QExpBaseChange.isAlgebraic_residueField p A hA
    let φ : IsLocalRing.ResidueField A →+* K :=
      (IsAlgClosed.lift (R := ZMod p) (S := IsLocalRing.ResidueField A) (M := K)).toRingHom
    exact bound_of_place K Γ hT Γ' hΓ' hneg x hx (AlgebraicClosure ℚ) A (φ.comp (IsLocalRing.residue A))
  ·
    haveI : CharZero K := CharP.charP_to_charZero K
    exact bound_of_place K Γ hT Γ' hΓ' hneg x hx K (⊤ : ValuationSubring K)
      (⊤ : ValuationSubring K).subtype
