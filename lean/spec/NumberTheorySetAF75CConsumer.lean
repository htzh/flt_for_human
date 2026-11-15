/-
  Cross-module wire test for the character orthogonality over a compact subgroup of the finite
  adèles and for the Fourier transform of a principal coset (`AF75C`).

  A `spec/` probe, not a library module. Two executed zones, both at `F = ℚ` and both against the
  port's concrete Haar measure `M4aS4.finMeasure ℚ` on `𝔸_ℚ^fin` (with the port's `finBorel`
  measurable structure, so the statements are stated at a genuine `IsAddHaarMeasure`):

  * **Zone 1** reads `setIntegral_addChar_mul_eq_ite_of_isCompact` at the concrete compact additive
    subgroup `K = ⊥` and the trivial character `ψf = 1`: the orthogonality relation must evaluate
    to the measure `ν K`, i.e. `∫_{⊥} 1 ∂ν = (ν ⊥).toReal`.
  * **Zone 2** reads `fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` at the
    concrete `d = 1 : 𝓞 ℚ` (nonzero), `k = 3 : ℚ` and the point `w = 0`, where the phase
    `ψf (-(k * w))` is `1` and the triviality indicator is `1`, so the transform of the indicator
    of the coset `3 + 1 • 𝓞̂` collapses to the measure of that coset.

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in
  it) breaks this file.
-/
import FLTForHuman.NumberTheory.AdelicFourier.FiniteCoset

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped Classical NNReal ENNReal
open scoped M4aS4

namespace NumberTheorySetAF75CConsumer

attribute [local instance] M4aS4.finBorel

/-! ### Zone 1 — orthogonality at the trivial subgroup and the trivial character -/

/-- Zone 1: the orthogonality relation at `K = ⊥` (`IsCompact` because `↑⊥ = {0}`) and the
trivial character `ψf = 1` evaluates to the measure `ν ⊥` of the subgroup. -/
theorem setIntegral_trivialChar_bot (ξ : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∫ z in (⊥ : AddSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)),
        (1 : AddChar (FiniteAdeleRing (𝓞 ℚ) ℚ) ℂ) (ξ * z) ∂(M4aS4.finMeasure ℚ)
      = ((M4aS4.finMeasure ℚ) (⊥ : AddSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ))).toReal := by
  have hK : IsCompact ((⊥ : AddSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    rw [AddSubgroup.coe_bot]
    exact isCompact_singleton
  rw [setIntegral_addChar_mul_eq_ite_of_isCompact ℚ (M4aS4.finMeasure ℚ)
    (1 : AddChar (FiniteAdeleRing (𝓞 ℚ) ℚ) ℂ) ⊥ hK ξ]
  simp

/-! ### Zone 2 — the principal coset at `w = 0`, where the phase is `1` -/

/-- Zone 2: at `d = 1 : 𝓞 ℚ`, `k = 3 : ℚ` and `w = 0`, the Fourier transform of the indicator of
the coset `3 + 1 • 𝓞̂` is the measure of that coset: the phase `ψf (-(k * w))` and the triviality
indicator are both `1`, so the coset computation of the headline collapses to `ν (coset)`. -/
theorem fourierIntegral_indicator_principalCoset_zero :
    fourierIntegral (1 : AddChar (FiniteAdeleRing (𝓞 ℚ) ℚ) ℂ) (M4aS4.finMeasure ℚ)
        (((fun z => algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (3 : ℚ)
            + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : 𝓞 ℚ) : ℚ) * z) ''
          integralFiniteAdeles (𝓞 ℚ) ℚ).indicator 1) 0
      = ((M4aS4.finMeasure ℚ) ((fun z => algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (3 : ℚ)
            + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : 𝓞 ℚ) : ℚ) * z) ''
          integralFiniteAdeles (𝓞 ℚ) ℚ)).toReal := by
  rw [fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply ℚ (M4aS4.finMeasure ℚ)
    continuous_const (1 : 𝓞 ℚ) one_ne_zero (3 : ℚ) 0]
  simp

end NumberTheorySetAF75CConsumer

end
