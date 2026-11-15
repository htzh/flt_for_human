/-
  The integral of a pure tensor against the product of a finite part of the unramified Weyl integrand and
  a finite Euler product, at a point of the convergence half-plane.

  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.NormProdSum
import FLTForHuman.AutomorphicForm.Adelic.LocalIntertwiningFinprod
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicBox.Normalization

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.InfiniteAdeleRing
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped ENNReal NNReal Classical Topology BigOperators

namespace AutomorphicForm.LocalIntertwining

theorem integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹
        * (∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
              * ((∏ v ∈ S, h v (x.2 v))
                * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                    (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                        (fun _ => (1 : ℂ)) (x.2 v.1)
                      + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                          (x.2 v.1)))) ∂μ)
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (∫ y, f y)
        * ((∏ v ∈ S, (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
              * ∫ y, h v y ∂(μv v)))
          * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) := by
  let _ : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  have _ : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h3 := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq F μ
    (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 F) F)) f
    (fun z : FiniteAdeleRing (𝓞 F) F => (∏ v ∈ S, h v (z v))
      * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
              (fun _ => (1 : ℂ)) (z v.1)
            + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                (z v.1))))
  have h4 :=
    AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
      F (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 F) F)) S μv h ϖ hϖ χ hχ hχ₁ s hs
  rw [h3, ← h4]
  unfold Measure.real
  ring

end AutomorphicForm.LocalIntertwining

end
