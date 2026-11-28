import FLTForHuman.AutomorphicForm.Adelic.PolyDecay
import FLTForHuman.NumberTheory.AdelicFourier.PoissonNormalized
import FLTForHuman.NumberTheory.StandardAddChar.GlobalAndInfinite
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.EisensteinGeneral.ArchKType

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical NNReal

namespace SetAF111Consumer

/-! ## Zone 1 — Poisson summation at the standard character (orders D and the standard-character fact)

Order D's `PoissonNormalized` row is the pure-tensor Poisson summation for **any** global character, and
`NumberField.StandardAddChar.isGlobalAddChar_stdAddChar` is the port's proof that `stdAddChar F` *is* one.
Composed, the theorem holds at the standard character with its character hypothesis discharged — the form
every call site wants, because `stdAddChar` is the character the Fourier layer is built around. -/

theorem tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_stdAddChar
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (hμB : μ (AdelicBox.adelicBox F) = 1)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ∑' ξ : F, fourierIntegral (StandardAddChar.stdAddChar F) μ f
          (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
  tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one F μ hμB
    (StandardAddChar.isGlobalAddChar_stdAddChar F) hf

/-! ## Zone 2 — the polynomial decay at the standard character (orders A and the standard-character fact)

Order A's row bounds the `addChar`-twisted unipotent integral by `(1 + ‖ξ‖)^{-N}` for a global character
`ψ`; the same composition discharges `ψ` at `stdAddChar`, which is the case the Eisenstein assembly
instantiates. The `let α` at the front of the pin's statement is unfolded at the call site, which is why
this consumer restates the binder block: nothing mathematical changes, only that one hypothesis is gone. -/

theorem exists_norm_integral_weyl_unipotent_mul_stdAddChar_le_polyDecay
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F) (N : ℕ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : F,
      ‖∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))
            ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) :=
  fun hα μ ν hμ hν s hs φ hφ hφK hφc g N =>
    norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary F hα μ ν hμ hν
      (StandardAddChar.stdAddChar F) (StandardAddChar.isGlobalAddChar_stdAddChar F)
      s hs φ hφ hφK hφc g N

end SetAF111Consumer
