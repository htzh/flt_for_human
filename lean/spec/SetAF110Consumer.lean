import FLTForHuman.TateCurve.SeriesIdentities
import FLTForHuman.TateCurve.Defect
import FLTForHuman.NumberTheory.AdelicFourier.TraceDual
import FLTForHuman.NumberTheory.AdelicFourier.NonzeroTrace
import FLTForHuman.AutomorphicForm.Adelic.WhittakerNormBound

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain MeasureTheory TateCurve
open scoped NNReal nonZeroDivisors Classical

namespace SetAF110Consumer

/-! ## Zone 1 — the defect series has no constant term (order C, both rows)

Order C's two rows are `defect_qExpansion` (the defect of a point is `∑' N, defectCoeff u N * q ^ N`) and
`defectCoeff_zero` (`defectCoeff u 0 = 0` for `u ≠ 1`). Composed, they give the series a *`q`-valuation*:
the defect of any point with `u ≠ 1` starts at `q ^ 1`, i.e. it vanishes to first order at the cusp. That
is the form the point-arithmetic layer works with, and the reason the defect is a *deformation* parameter
rather than a constant.

The summability of the series is the pin's `summable_norm_*` block (order C transcribed it); here it is a
hypothesis, because a consumer that already has the defect expansion has it too. -/

theorem defect_qExpansion_eq_tsum_succ
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) (hu1 : u ≠ 1)
    (hsum : Summable fun N : ℕ => defectCoeff u N * q ^ N) :
    pointY q u ^ 2 + pointX q u * pointY q u - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q)
      = ∑' N : ℕ, defectCoeff u (N + 1) * q ^ (N + 1) := by
  rw [defect_qExpansion hq0 hq hu0 hu hqu hqu', hsum.tsum_eq_zero_add,
    defectCoeff_zero (K := K) hu1, zero_mul, zero_add]

/-! ## Zone 2 — the trace dual's coset form at a principal representative (order E, with AF109G)

`forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual` (order E) says the finite-part vanishing at
`w` is equivalent to `w` being an integral translate of a trace-dual element, and SET-AF109G's row says the
same vanishing at `algebraMap ξ` is equivalent to `ξ` being trace-dual. Composed at `w = algebraMap ξ`, the
membership form and the coset form are *the same criterion*: `ξ` is trace-dual iff `algebraMap ξ` is an
integral translate of one. That is the bridge a consumer needs to pass between the two forms, and it is the
set's cross-order composition (order E's coset row with the previous set's membership row). -/

theorem mem_traceDual_iff_exists_sub_mem_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (ξ : F) :
    ξ ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) :
          FractionalIdeal (𝓞 F)⁰ F) ∧
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ - algebraMap F (FiniteAdeleRing (𝓞 F) F) r
          ∈ integralFiniteAdeles (𝓞 F) F := by
  rw [← forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψ hψ_inf]
  exact forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual F hψ hψ_inf _

end SetAF110Consumer
