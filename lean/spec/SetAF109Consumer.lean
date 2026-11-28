import FLTForHuman.TateCurve.SeriesIdentities
import FLTForHuman.TateCurve.Tails
import FLTForHuman.NumberTheory.AdelicFourier.TraceDual
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding

set_option autoImplicit false

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.AdelicFourier NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain MeasureTheory TateCurve
open scoped NNReal nonZeroDivisors Classical FourierTransform

namespace SetAF109Consumer

/-! ## Zone 1 — the `q`-expansion is valid at every representative of the `u`-coset (orders F and the
existing `pointX_zpow_mul`)

Order F's row writes `pointX q u` as `xfun u + ∑' N, xCoeff u (N+1) * q ^ (N+1)`. The point-arithmetic
layer does not work with `u` but with a *representative* of `u` modulo `q ^ ℤ` — that is why the module
already carries `pointX_zpow_mul` (the `q`-periodicity of the point coordinates). Composed, they give the
`q`-expansion at every `q ^ n * u`, which is the form a call site has: the expansion is a function of the
coset, so it can be *stated* at the representative the caller holds.

This is the set's cross-order composition: order F's row plus `SeriesIdentities`' periodicity row plus
`TateCurve/Tails`' coefficient layer, whose `xDivTerm`/`growthBound` bounds are what make the `tsum`
usable. -/

theorem pointX_qExpansion_zpow_mul
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) (n : ℤ) :
    pointX q (q ^ n * u) = xfun u + ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1) := by
  rw [pointX_zpow_mul hq0 n]
  exact pointX_qExpansion hq0 hq hu0 hu hqu hqu'

theorem pointY_qExpansion_zpow_mul
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) (n : ℤ) :
    pointY q (q ^ n * u) = yfun u + ∑' N : ℕ, yCoeff u (N + 1) * q ^ (N + 1) := by
  rw [pointY_zpow_mul hq0 n]
  exact pointY_qExpansion hq0 hq hu0 hu hqu hqu'

/-! ## Zone 2 — the trace-dual vanishing set, in the geometric form (order G's two rows)

Order G's Fourier row says the finite-part character vanishes on `integralFiniteAdeles` **iff** `ξ` lies in
the trace dual of the unit ideal. Order G's lattice row identifies the `dualSubmodule` of an ideal lattice
with the `mixedEmbedding` of the dual ideal. Composed at the unit ideal they give the vanishing set as a
*lattice* condition — the form Poisson summation consumes, where the dual lattice is `Λ^* = Λ'` of the
`ℤ`-lattice `mixedEmbedding '' 𝓞 F`. -/

theorem forall_addChar_finitePart_mul_eq_one_iff_mem_dualSubmodule
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (ξ : F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F,
        ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ * z) = 1)
      ↔ mixedEmbedding F ξ ∈
          (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace F)).flip
            (mixedEmbedding.idealLattice F (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) :
            Set (mixedSpace F)) := by
  rw [forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψ hψ_inf]
  rw [coe_dualSubmodule_flip_traceForm_idealLattice]
  constructor
  · intro h
    exact ⟨ξ, h, rfl⟩
  · rintro ⟨y, hy, hEq⟩
    rwa [mixedEmbedding_injective F hEq] at hy

end SetAF109Consumer
