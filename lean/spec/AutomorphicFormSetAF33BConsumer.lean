/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/LocalIntertwiningFinprod.lean`
  (SET-AF33B).

  The row under test is the finite-adèle Euler product
  `integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`.  It is
  exercised in composition, never by `#check`: each theorem below instantiates it (or one of
  the landed helpers it factors through) at data where the row's content has to *compute*.

  * `multipliable_euler_factor_at_half` turns the row's hypothesis `1 / 2 < s.re` into the
    `z.re < -1` shape the Euler product's summability asks for at the row's own exponent
    `-(2 * s + 1)` — the `2s` vs `2s + 1` bookkeeping the row is built on — and concludes that
    the infinite product on the row's right-hand side is convergent.  This is the premise the
    row's final `Tendsto` comparison consumes, exposed at the consumer level;
  * `boxed_stratum_integral` is the row's assembly identity `stratum_identity` at the boundary
    `T = S`, where the correction product `∏ v ∈ T \ S` collapses to `1` and the identity reads
    "the box-normalized integral over the `S`-stratum is the product of the local integrals at
    `S`" — the input the exhaustion over `T` starts from;
  * `euler_product_all_places` is the row at `S = ∅`: every local factor of `∏ v ∈ S` is `1`,
    the box normalization stands alone, and the identity becomes the unramified Euler product
    over all finite places;
  * `norm_integral_boxed_stratum` is the row's `L¹` computation `setIntegral_norm_Phi_eq` at the
    same boundary `T = S`, where the beta-product over `T \ S` disappears and the `L¹` norm of
    the integrand over the stratum is the box measure times the local `L¹` norms at `S`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF33BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.LocalIntertwiningFinprod

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.LocalIntertwining MeasureTheory
open AutomorphicForm.LocalIntertwining.FiniteAdeleAssembly
open IsDedekindDomain Filter
open scoped ENNReal NNReal RestrictedProduct

namespace AutomorphicFormSetAF33BConsumer

section EulerFactor

variable (F : Type) [Field F] [NumberField F]
  (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
  (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
  (s : ℂ)

/-- The row's `1 / 2 < s.re` reaches the summability side: at the row's own exponent the Euler
product of the right-hand side is convergent.  The exponent `-(2 * s + 1)` has real part below
`-1` exactly under the row's hypothesis, which is the `2s` versus `2s + 1` shift read backwards. -/
theorem multipliable_euler_factor_at_half
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) (hs : 1 / 2 < s.re) :
    Multipliable fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      1 - eul F χ ϖ (-(2 * s + 1)) w.1 := by
  have hz : (-(2 * s + 1)).re < -1 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, Complex.one_re]
    linarith
  exact multipliable_one_sub_eul χ ϖ hz S hχ₁

end EulerFactor

section Box

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
  (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
  (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
  (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
  (s : ℂ)

/-- The assembly identity at the boundary `T = S`: the ratio product over `T \ S` is empty, so
the box-normalized integral over the `S`-stratum is exactly the product of the local integrals
at `S`.  This is the shape the exhaustion of the headline starts from. -/
theorem boxed_stratum_integral (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) (hs : 1 / 2 < s.re) :
    (ν.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x in stratumSet F S, Phi F S h χ s x ∂ν
      = ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
            * ∫ y, h v y ∂(μ v)) := by
  have hrow := stratum_identity F ν μ (subset_refl S) h ϖ hϖ χ hχ hχ₁ s hs
  simpa only [Finset.sdiff_self, Finset.prod_empty, mul_one] using hrow

/-- The headline at `S = ∅`: the unramified Euler product over every finite place, with the box
normalization standing alone.  Every factor of `∏ v ∈ S` is `1`, so the row's right-hand side is
the single infinite product `∏' (1 - χ v (ϖ v) * N v ^ (-(2 * s + 1)))`. -/
theorem euler_product_all_places
    (hϖ : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))),
      Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχ : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))),
      ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))),
      ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) (hs : 1 / 2 < s.re) :
    (ν.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * (∫ x, Phi F (∅ : Finset (HeightOneSpectrum (𝓞 F))) h χ s x ∂ν)
        * ∏' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F)))},
            (1 - eul F χ ϖ (-(2 * s)) w.1)
      = (∏ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F))),
            (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
              * ∫ y, h v y ∂(μ v)))
        * ∏' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F)))},
            (1 - eul F χ ϖ (-(2 * s + 1)) w.1) := by
  exact integral_finiteAdeleRing_impl F ν (∅ : Finset (HeightOneSpectrum (𝓞 F))) μ h ϖ hϖ χ
    hχ hχ₁ s hs

/-- The row's `L¹` computation at the boundary `T = S`: the beta-product over `T \ S` is empty,
so the norm of the integrand over the stratum is the box measure times the inverse product of the
local measures times the local `L¹` norms at `S`. -/
theorem norm_integral_boxed_stratum (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) (hs : 1 / 2 < s.re) :
    ∫ x in stratumSet F S, ‖Phi F S h χ s x‖ ∂ν
      = ν.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F)
        * (∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * (∏ v ∈ S, ∫ y, ‖h v y‖ ∂(μ v)) := by
  have hs0 : 0 < s.re := by linarith
  have hrow := setIntegral_norm_Phi_eq F ν μ (subset_refl S) h ϖ hϖ χ hχ hχ₁ s hs0
  simpa only [Finset.sdiff_self, Finset.prod_empty, mul_one] using hrow

end Box

end AutomorphicFormSetAF33BConsumer
