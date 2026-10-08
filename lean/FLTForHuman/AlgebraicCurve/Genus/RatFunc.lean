/-
The projective line has genus zero, after FLT's
`P2M/Sol/S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean` (1,461 ln),
pinned at `aa2d8b3`:

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean>.

The pin's proof has two halves: the `HasCanonicalDivisor` instance for `RatFunc K`
(the port already has it as the scoped instance
`instHasCanonicalDivisorRatFuncPerfectField`, `P1/PerfectField.lean`) and the
degree computation `degree (canonicalDivisorOf hω) = -2`. The port writes the
instance once and only the degree half here; the 3 same-file drags
(`ord_add_eq_left`, `differentialCoeff_ne_zero`,
`uniformizer_ne_zero'_PFFRTP1DC`) are already public elsewhere in the port.

The only new public statement besides the headline is the uniqueness form
`canonicalDivisorOf_eq_of_forall`; the headline's statement is its `Theorems/`
wrapper.
-/
import FLTForHuman.AlgebraicCurve.Defs.RatFuncPlaces
import FLTForHuman.AlgebraicCurve.P1.Dictionary
import FLTForHuman.AlgebraicCurve.P1.UnitNormalForm
import FLTForHuman.AlgebraicCurve.P1.PerfectField
import FLTForHuman.AlgebraicCurve.P1.UnitFinite
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem canonicalDivisorOf_eq_of_forall [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : ∀ v : Place K F, D v = v.ordDifferential ω) :
    canonicalDivisorOf hω = D :=
  Finsupp.ext fun v => by rw [canonicalDivisorOf_apply hω v, ← hD v]

end Uniqueness

section PerfectInstance

variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [PerfectField K]

open scoped AlgebraicCurve

theorem degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 {ω : Ω[(RatFunc K)⁄K]}
    (hω : ω ≠ 0) : Divisor.degree (canonicalDivisorOf hω) = -2 := by
  classical
  obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hω hc.symm
  obtain ⟨D, hD, hDdeg⟩ := exists_divisor_smul_dX_of_perfectField K hc0
  have heq : canonicalDivisorOf hω = D := by
    refine canonicalDivisorOf_eq_of_forall hω fun v => ?_
    rw [← hc]
    exact hD v
  rw [heq, hDdeg]

/-- The pin's `genus_eq_degree_div`, private here: the port's public copy lives in
`ResidueTheorem/RRAssembly.lean`, which a `Genus/` leaf must not import. -/
private theorem genus_eq_degree_div_of_ratFunc :
    ∃ (ω₀ : Ω[(RatFunc K)⁄K]) (hω₀ : ω₀ ≠ 0),
      genus K (RatFunc K) = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 := by
  have hne : ∃ ω : Ω[(RatFunc K)⁄K], ω ≠ 0 := exists_ne 0
  refine ⟨hne.choose, hne.choose_spec, ?_⟩
  rw [genus, dif_pos hne]

theorem genus_ratFunc_eq_zero_of_perfectField_s17 : genus K (RatFunc K) = 0 := by
  obtain ⟨ω₀, hω₀, hgen⟩ := genus_eq_degree_div_of_ratFunc (K := K)
  rw [hgen, degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 K hω₀]
  norm_num

end PerfectInstance

/-- The projective line has genus zero over a perfect field (the pin
`genus_ratFunc_eq_zero_of_perfectField`; statement from its `Theorems/` wrapper). -/
theorem genus_ratFunc_eq_zero_of_perfectField (K : Type*) [Field K] [PerfectField K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)] :
    AlgebraicCurve.genus K (RatFunc K) = 0 :=
  genus_ratFunc_eq_zero_of_perfectField_s17 K

/-- The `CharZero` form: a characteristic-zero field is perfect, so the previous
headline applies (the pin `genus_ratFunc_eq_zero`; statement from its `Theorems/`
wrapper). -/
theorem genus_ratFunc_eq_zero (K : Type*) [Field K] [CharZero K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)] :
    AlgebraicCurve.genus K (RatFunc K) = 0 :=
  haveI : PerfectField K := inferInstance
  genus_ratFunc_eq_zero_of_perfectField K

section GenusFF

/-- `RatFunc K` is a curve over `K`; the pin's `isCurveOver_ratFunc`, here the
scoped instance `instIsCurveOverRatFunc` of `P1/UnitFinite.lean` re-exposed. -/
theorem isCurveOver_ratFunc (K : Type*) [Field K] : IsCurveOver K (RatFunc K) :=
  instIsCurveOverRatFunc K

/-- The geometric genus of the projective line is zero over an algebraically
closed field (the pin `genusFF_ratFunc_eq_zero_of_isAlgClosed`; statement from its
`Theorems/` wrapper). The proof is the pin's, over the closure landed in
`ResidueTheorem/RRAssembly.lean`. -/
theorem genusFF_ratFunc_eq_zero_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] :
    genusFF K (RatFunc K) = 0 := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  haveI : HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates :=
    dCoordGenerates_of_isCurveOver
  haveI : Algebra.IsIntegral (RatFunc K) (RatFunc K) := Algebra.IsIntegral.of_finite _ _
  have hRR : FunctionFieldRiemannRoch K (RatFunc K) :=
    functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
  have hC : ConstantsAreBase K (RatFunc K) :=
    constantsAreBase_of_isAlgClosed K (RatFunc K)
  have hSG : StichtenothGenusExists K (RatFunc K) :=
    stichtenothGenusExists_of_isCurveOver hC
  have hW : WeilDualityAdelic K (RatFunc K) :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  rw [← genus_eq_genusFF hRR hW hC]
  exact genus_ratFunc_eq_zero_of_perfectField K

end GenusFF

end AlgebraicCurve
