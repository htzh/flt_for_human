/-
  Cross-module wire test for the box normalization in Fourier form (`AF77A`).

  A `spec/` probe, not a library module. The whole zone is at the base field `F = ℚ`, where the
  pin's abstract objects have concrete shapes:

  * `𝓞 ℚ = ℤ`, so `disc ℚ = 1` and `nrComplexPlaces ℚ = 0` (the discriminant factor of the
    identity is `2 ^ 0 / √1 = 1`);
  * the adèles carry the port's `adelicAddHaar` and the finite adèles the `M4aS4` place measure
    `finMeasure` — both additive Haar measures (instances supplied locally below), the pair the
    identity is stated for; the additive character is the standard one `psiQ`;
  * the two integrands are concrete: `fBump` is the Gaussian bump `y ↦ exp (-‖y‖²)` on the mixed
    space of `ℚ` (an element of the Schwartz–Bruhat space's archimedean half), and `gBox` is the
    indicator of the integral finite adèles `integralFiniteAdeles (𝓞 ℚ) ℚ`;
  * the identity is read at `w = 0`. There all three Fourier transforms are the plain integrals
    (`fourierIntegral_def` plus `AddChar.map_zero_eq_one`): the twisted archimedean transform at
    `ringEquiv 0 = 0`, the twisted finite transform at `0`, and the adèlic one at `0`. The consumer
    states and proves that integral form, so the module's own statement is never restated.

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in its
  proof) breaks this file.
-/
import FLTForHuman.EisensteinGeneral.Factorization.BoxFourier
import FLTForHuman.NumberTheory.NumberField.StandardGlobalAddCharRat
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfiniteAdeleRing
open NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open scoped ENNReal NNReal Classical M4aS4

namespace EisensteinGeneralSetAF77AConsumer

-- the adèles' and the finite adèles' Borel structures (the port spells them as named instances)
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] M4aS4.finBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] M4aS4.isAddHaarMeasure_finMeasure

/-- A bump-Schwartz function on the mixed space of `ℚ`: the Gaussian bump
`y ↦ exp (-‖y‖²)`. -/
def fBump : mixedEmbedding.mixedSpace ℚ → ℂ :=
  fun y => Complex.exp (-(((‖y‖ : ℝ) ^ 2 : ℝ) : ℂ))

/-- The indicator of the integral finite adèles of `ℚ`. -/
def gBox : FiniteAdeleRing (𝓞 ℚ) ℚ → ℂ :=
  Set.indicator (integralFiniteAdeles (𝓞 ℚ) ℚ) fun _ => 1

/-- A Fourier transform at the argument `0` is the plain integral: the character factor is
`ψ 0 = 1`. This is what turns all three transforms of the identity into integrals at `w = 0`. -/
theorem fourierIntegral_apply_zero {A : Type*} [CommRing A] [MeasurableSpace A]
    (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) : fourierIntegral ψ μ f 0 = ∫ v, f v ∂μ := by
  rw [fourierIntegral_def]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

/-! ### The headline at `F = ℚ`, `w = 0`, and both sides' integrals -/

/-- The headline of `BoxFourier` at `F = ℚ`, `μ = adelicAddHaar`, `ν = finMeasure`, `ψ = psiQ`,
`f = fBump` (the box bump), `g = gBox` (the `integralFiniteAdeles` indicator) and `w = 0`.

At `w = 0` the three Fourier transforms of the identity collapse to integrals, and the statement
below is the resulting identity of plain integrals: the inverse box measure times the integral of
the (box-indicator) pure tensor on the left, and the discriminant factor — which at `F = ℚ` is
`2 ^ 0 / √|1| = 1` — times the archimedean integral of `fBump` and the normalized finite integral of
`gBox` on the right. -/
theorem inv_measure_adelicBox_mul_fourierIntegral_tensor_eq_rat_zero :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ)).toReal : ℂ)⁻¹ *
        (∫ x, fBump (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * gBox x.2
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))
      = (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ) *
        ((∫ y, fBump y ∂(volume : Measure (mixedEmbedding.mixedSpace ℚ))) *
          (((M4aS4.finMeasure ℚ (integralFiniteAdeles (𝓞 ℚ) ℚ)).toReal : ℂ)⁻¹ *
            ∫ z, gBox z ∂(M4aS4.finMeasure ℚ))) := by
  have h := EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    (F := ℚ) (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (M4aS4.finMeasure ℚ)
    NumberField.StandardAddChar.psiQ fBump gBox 0
  have h1 : ((0 : AdeleRing (𝓞 ℚ) ℚ).1) = (0 : InfiniteAdeleRing ℚ) := rfl
  have h2 : ((0 : AdeleRing (𝓞 ℚ) ℚ).2) = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl
  rw [h1, h2] at h
  simpa only [fourierIntegral_apply_zero, map_zero] using h

end EisensteinGeneralSetAF77AConsumer
