/-
  The façade of the TateGlobal analytic core.

  Three declarations: the consumed headlines
  `NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq`,
  `NumberField.TateGlobal.integrable_zetaIntegrand` and
  `NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator`.
  Each statement is the pin wrapper `Theorems/Thm_NumberField_TateGlobal_*.lean`
  verbatim (playbook §4: the wrapper is the statement authority), and each proof is
  the development's own headline:

  * `zetaIntegral_mul_eulerFactors_eq` — `…/TateGlobal/G2Proof`'s
    `NumberField.TateGlobal.G2Proof.zetaIntegral_mul_eulerFactors_eq`
    (`EulerFactors.lean`, the pin's `solution` at A 5573);
  * `integrable_zetaIntegrand` — `NumberField.TateGlobal.integrable_zetaIntegrand_holds`
    (`IntegrableZetaIntegrand.lean`, the pin's `solution` at B 6193);
  * `exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator` —
    `NumberField.TateGlobal.IndicatorEulerFactors.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator`
    (`IndicatorEulerFactors.lean`, the pin's `solution` at C 5588).

  The rest of the theory stays public in the unlisted development modules
  (`EulerFactors`, `IntegrableZetaIntegrand`, `IndicatorEulerFactors` and the
  twenty modules they import); a consumer that needs one of their declarations
  imports the module directly.  Only these three headlines are checked, so this
  module declares nothing else.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrappers are
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_integrable_zetaIntegrand.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean
  and the proof silos are `P2M/Sol/S_NumberField_TateGlobal_*.lean` of the same pin.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.EulerFactors
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IntegrableZetaIntegrand
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IndicatorEulerFactors

open MeasureTheory NumberField NumberField.AdelicFourier AutomorphicForm IsDedekindDomain

namespace NumberField
namespace TateGlobal

theorem zetaIntegral_mul_eulerFactors_eq (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s :=
  G2Proof.zetaIntegral_mul_eulerFactors_eq F ν S μf μa ϖ hϖ

theorem integrable_zetaIntegrand (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν :=
  integrable_zetaIntegrand_holds F ν hf hχc hχu hs

theorem exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ A : (InfiniteAdeleRing F → ℂ) → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) → ℂ → ℂ,
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (G : InfiniteAdeleRing F → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : ∀ x, f x = (integralOutside S).indicator
          (fun x => G x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = A G χ s * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s :=
  IndicatorEulerFactors.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator F ν S μf ϖ hϖ

end TateGlobal
end NumberField
