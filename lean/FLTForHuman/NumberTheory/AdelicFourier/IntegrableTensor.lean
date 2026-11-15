/-
  The pure tensor of two integrable functions is integrable on the adèle ring.

  For an additive Haar measure `μ` on `𝔸_F`, an additive Haar measure `ν` on the finite adèles, and
  integrable `f : mixedSpace F → ℂ`, `g : 𝔸_F^fin → ℂ`, the pure tensor
  `x ↦ f (x.1) * g (x.2)` is `μ`-integrable (`integrable_mul_of_integrable_of_integrable`).  This is
  the integrability of `NumberTheory/AdelicFourier/Space` without the Schwartz/locally-constant
  hypotheses on the two factors, and it is the input of every Eisenstein-series glue argument.

  The proof transports `volume` on the mixed space to a Haar measure on the infinite adèles along
  `InfiniteAdeleRing.ringEquiv_mixedSpace`, uses `Integrable.mul_prod` on the product, and converts
  the resulting Haar measure on `𝔸_F` into `μ` by
  `NumberField.AdelicHaar.exists_smul_eq_of_isAddHaarMeasure_adeleRing`.  The ingredients of that
  transport are the shared normalization module (`NumberTheory/AdelicBox/Normalization`).

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable.lean`, whose
  `ch3_`-prefixed private copies of the seven transport/countability lemmas are **not** ported: they
  are the public declarations of `NumberTheory/AdelicBox/Normalization` (the pin proved them twice).

  spec-pin: P2M/Sol/S_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable.lean
-/
import FLTForHuman.NumberTheory.AdelicBox.Normalization
import FLTForHuman.NumberTheory.AdelicHaar.Uniqueness
import FLTForHuman.NumberTheory.AdelicFourier
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox
open IsDedekindDomain
open scoped ENNReal NNReal Classical

namespace NumberField.AdelicFourier

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem integrable_mul_of_integrable_of_integrable (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (hf : Integrable f MeasureTheory.volume) (hg : Integrable g ν) :
    Integrable (fun x : AdeleRing (𝓞 F) F => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) μ := by
  let mX : MeasurableSpace (InfiniteAdeleRing F) := borel _
  have : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
  have : SecondCountableTopology (InfiniteAdeleRing F) :=
    NumberField.AdelicBox.secondCountableTopology_infiniteAdeleRing (F := F)
  have : SigmaCompactSpace (FiniteAdeleRing (𝓞 F) F) :=
    NumberField.AdelicBox.sigmaCompactSpace_finiteAdeleRing (F := F)
  have : SigmaFinite ν := by infer_instance
  have hmA : ‹MeasurableSpace (AdeleRing (𝓞 F) F)›
      = @Prod.instMeasurableSpace (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) mX ‹_› := by
    rw [BorelSpace.measurable_eq (α := AdeleRing (𝓞 F) F)]
    exact (Prod.borelSpace (α := InfiniteAdeleRing F)
      (β := FiniteAdeleRing (𝓞 F) F)).measurable_eq.symm
  subst hmA
  let mA : MeasurableSpace (AdeleRing (𝓞 F) F) :=
    @Prod.instMeasurableSpace (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) mX ‹_›
  have hsymm_meas : Measurable (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :=
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace_symm (F := F)).measurable
  let eM : mixedEmbedding.mixedSpace F ≃ᵐ InfiniteAdeleRing F :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toEquiv
      measurable_toFun := hsymm_meas
      measurable_invFun := (continuous_ringEquiv_mixedSpace F).measurable }
  set πX : Measure (InfiniteAdeleRing F) :=
    Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm volume with hπX
  have hπXH : πX.IsAddHaarMeasure := by
    have h := AddEquiv.isAddHaarMeasure_map (volume : Measure (mixedEmbedding.mixedSpace F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace_symm (F := F))
      (continuous_ringEquiv_mixedSpace F)
    have hfun : (⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv :
        mixedEmbedding.mixedSpace F → InfiniteAdeleRing F)
        = ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := rfl
    rw [hfun] at h
    exact h
  have hπH : (πX.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure πX ν
  let π : Measure (AdeleRing (𝓞 F) F) := πX.prod ν
  have hπA : Measure.IsAddHaarMeasure π := hπH
  obtain ⟨c, -, hμ⟩ :=
    @NumberField.AdelicHaar.exists_smul_eq_of_isAddHaarMeasure_adeleRing F _ _ mA ‹_› μ π ‹_› hπA
  have hmap : Measure.map (⇑eM) volume = πX := rfl
  have hfX : Integrable (fun x : InfiniteAdeleRing F => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) πX := by
    rw [← hmap]
    refine (integrable_map_equiv eM _).mpr ?_
    have hcomp : ((fun x : InfiniteAdeleRing F => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) ∘ ⇑eM) = f :=
      funext fun y => congrArg f ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [hcomp]
    exact hf
  have hπint : Integrable
      (fun x : AdeleRing (𝓞 F) F => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) π :=
    Integrable.mul_prod (μ := πX) (ν := ν) hfX hg
  rw [hμ]
  exact hπint.smul_measure_nnreal

end NumberField.AdelicFourier

end
