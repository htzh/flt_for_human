/-
  Normalizing the box measure: the compactness, countability and mixed-space transport behind
  `inv_measure_adelicBox_mul_integral_pureTensor_eq`, and the identity itself.

  The adèlic Fourier transform of a pure tensor carries the constant
  `μ (adelicBox F) / (covolume * ν (integralFiniteAdeles))` (`NumberTheory/AdelicFourier/Transform`).
  This module computes it: for an additive Haar measure `μ` on `𝔸_F` and `ν` on the finite adèles,

    `μ (adelicBox F)⁻¹ * ∫ x, f x.1 * g x.2 ∂μ
       = (2 ^ nrComplexPlaces F / √|disc F|) * (∫ f) * (ν (𝓞̂)⁻¹ * ∫ g ∂ν)`,

  the discriminant factor being the covolume of `𝓞_F` in the mixed space.  The proof needs, and this
  module also carries, the ingredients: the ball `{y | s * y ∈ 𝓞̂}` is compact for `s ≠ 0`
  (`isCompact_setOf_mul_mem_integralFiniteAdeles`), the finite adèles are `σ`-compact, the completions
  and the infinite adèles are second countable (the two countability rows the pin repeats in its other
  files; `secondCountableTopology_infiniteAdeleRing` also exists in the archimedean approximation
  module — this is the pin's own duplicate, kept because this module sits below it), and the
  mixed-space transport of `InfiniteAdeleRing.ringEquiv_mixedSpace` is continuous in both directions
  with the coordinate formulas `ringEquiv_mixedSpace_symm_apply_of_isReal/_of_isComplex`.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq.lean`, whose label
  namespace `BoxNormalization` is dropped (the pin's names are already descriptive).  The seven
  transport/countability declarations are the ones the Eisenstein glue row
  (`NumberTheory/AdelicFourier/IntegrableTensor`) re-proved privately in the pin; they are written once
  here, publicly.

  spec-pin: P2M/Sol/S_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq.lean
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicHaar.Uniqueness
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfiniteAdeleRing
open IsDedekindDomain
open scoped ENNReal NNReal Classical

namespace NumberField.AdelicBox

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_setOf_mul_mem_integralFiniteAdeles (s : 𝓞 F) (hs : s ≠ 0) :
    IsCompact {y : FiniteAdeleRing (𝓞 F) F |
      algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * y ∈ integralFiniteAdeles (𝓞 F) F} := by
  set a : FiniteAdeleRing (𝓞 F) F := algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s with ha_def
  have hsF : (algebraMap (𝓞 F) F s) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  have ha : IsUnit a := by
    have hu : IsUnit (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s)) :=
      (IsUnit.mk0 _ hsF).map _
    rwa [← IsScalarTower.algebraMap_apply] at hu
  obtain ⟨u, hu⟩ := ha
  have hset : {y : FiniteAdeleRing (𝓞 F) F | a * y ∈ integralFiniteAdeles (𝓞 F) F}
      = (fun c => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * c) ''
          integralFiniteAdeles (𝓞 F) F := by
    ext y
    constructor
    · intro hy
      refine ⟨a * y, hy, ?_⟩
      simp only [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · rintro ⟨c, hc, rfl⟩
      simp only [Set.mem_ofPred_eq, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
      exact hc
  rw [hset]
  exact (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

theorem sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  have : Countable F := by
    obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℚ) (M := F)
    rw [← Set.countable_univ_iff]
    have : Countable (Submodule.span ℚ (Set.range b)) := inferInstance
    rwa [hb] at this
  have : Countable (𝓞 F) := inferInstanceAs (Countable (integralClosure ℤ F))
  let K : {s : 𝓞 F // s ≠ 0} → Set (FiniteAdeleRing (𝓞 F) F) := fun s =>
    {y | algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s.1 * y ∈ integralFiniteAdeles (𝓞 F) F}
  refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
  · rintro _ ⟨s, rfl⟩
    exact isCompact_setOf_mul_mem_integralFiniteAdeles F s.1 s.2
  · refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨s, hs, hy⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 F) F y
    exact Set.mem_sUnion.mpr ⟨K ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, hy⟩

omit [NumberField F] in

theorem secondCountableTopology_completion (v : InfinitePlace F) :
    SecondCountableTopology v.Completion := by
  rcases isReal_or_isComplex v with hv | hv
  · exact (Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
  · exact
      (Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology

theorem secondCountableTopology_infiniteAdeleRing :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  have : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion :=
    secondCountableTopology_completion F
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

omit [NumberField F] in

theorem ringEquiv_mixedSpace_symm_apply_of_isReal (y : mixedEmbedding.mixedSpace F)
    (v : InfinitePlace F) (hv : v.IsReal) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v
      = (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
  apply (Completion.isometryEquivRealOfIsReal hv).injective
  rw [IsometryEquiv.apply_symm_apply]
  have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
  exact h

omit [NumberField F] in

theorem ringEquiv_mixedSpace_symm_apply_of_isComplex (y : mixedEmbedding.mixedSpace F)
    (v : InfinitePlace F) (hv : v.IsComplex) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v
      = (Completion.isometryEquivComplexOfIsComplex hv).symm (y.2 ⟨v, hv⟩) := by
  apply (Completion.isometryEquivComplexOfIsComplex hv).injective
  rw [IsometryEquiv.apply_symm_apply]
  have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
  exact h

omit [NumberField F] in

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases isReal_or_isComplex v with hv | hv
  · have : (fun y : mixedEmbedding.mixedSpace F => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v)
        = fun y => (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) :=
      funext fun y => ringEquiv_mixedSpace_symm_apply_of_isReal F y v hv
    rw [this]
    exact (Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have : (fun y : mixedEmbedding.mixedSpace F => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v)
        = fun y => (Completion.isometryEquivComplexOfIsComplex hv).symm (y.2 ⟨v, hv⟩) :=
      funext fun y => ringEquiv_mixedSpace_symm_apply_of_isComplex F y v hv
    rw [this]
    exact (Completion.isometryEquivComplexOfIsComplex hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

open scoped Classical in
theorem inv_measure_adelicBox_mul_integral_pureTensor_eq
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2 ∂μ
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) *
        ((∫ y, f y) * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹ * ∫ z, g z ∂ν)) := by

  let mX : MeasurableSpace (InfiniteAdeleRing F) := borel _
  have : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
  have : SecondCountableTopology (InfiniteAdeleRing F) := secondCountableTopology_infiniteAdeleRing F
  have : SigmaCompactSpace (FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_finiteAdeleRing F
  have : SigmaFinite ν := by infer_instance

  have hmA : ‹MeasurableSpace (AdeleRing (𝓞 F) F)›
      = @Prod.instMeasurableSpace (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) mX ‹_› := by
    rw [BorelSpace.measurable_eq (α := AdeleRing (𝓞 F) F)]
    exact (Prod.borelSpace (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).measurable_eq.symm
  subst hmA
  let mA : MeasurableSpace (AdeleRing (𝓞 F) F) :=
    @Prod.instMeasurableSpace (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) mX ‹_›
  -- `AdeleRing` is a `def`, not an `abbrev`: after `subst` above its two halves are only
  -- defeq at the semireducible transparency, which is not enough for a `Measure`'s `FunLike`/`integral`
  -- instance argument.  Read the ambient measure at the product type it now *is*: `μP` is `rfl`-equal
  -- to `μ`, and the `change` below restates the frozen goal there.
  let μP : Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := μ
  change ((μP (adelicBox F)).toReal : ℂ)⁻¹ *
      ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2 ∂μP
    = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) *
      ((∫ y, f y) * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹ * ∫ z, g z ∂ν))

  have hsymm_meas : Measurable (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :=
    (continuous_ringEquiv_mixedSpace_symm F).measurable
  let eM : mixedEmbedding.mixedSpace F ≃ᵐ InfiniteAdeleRing F :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toEquiv
      measurable_toFun := hsymm_meas
      measurable_invFun := (continuous_ringEquiv_mixedSpace F).measurable }
  set πX : Measure (InfiniteAdeleRing F) :=
    Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm volume with hπX
  have hπXH : πX.IsAddHaarMeasure := by
    have h := AddEquiv.isAddHaarMeasure_map (volume : Measure (mixedEmbedding.mixedSpace F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv
      (continuous_ringEquiv_mixedSpace_symm F) (continuous_ringEquiv_mixedSpace F)
    have hfun : (⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv :
        mixedEmbedding.mixedSpace F → InfiniteAdeleRing F)
        = ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := rfl
    rw [hfun] at h
    exact h
  have hπH : (πX.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure πX ν

  let πP : Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := πX.prod ν
  have hπA : πP.IsAddHaarMeasure := hπH
  obtain ⟨c, hc, hμ⟩ :=
    @AdelicHaar.exists_smul_eq_of_isAddHaarMeasure_adeleRing F _ _ mA ‹_› μP πP ‹_› hπA
  have hμP : μP = c • πP := hμ

  have hV : (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal
      = Real.sqrt |(discr F : ℝ)| / (2 : ℝ) ^ nrComplexPlaces F := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm,
      Int.norm_eq_abs, inv_pow, inv_mul_eq_div]
  have hπXbox : πX (infiniteBox F) = volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
    rw [hπX, Measure.map_apply hsymm_meas (measurableSet_infiniteBox F)]
    congr 1
    ext y
    simp only [Set.mem_preimage, infiniteBox, RingEquiv.apply_symm_apply]
  have hbox : μP (adelicBox F) = c * (πX (infiniteBox F) * ν (integralFiniteAdeles (𝓞 F) F)) := by
    have hset : adelicBox F = infiniteBox F ×ˢ integralFiniteAdeles (𝓞 F) F := rfl
    rw [hμP, hset, Measure.coe_nnreal_smul_apply]
    congr 1
    exact Measure.prod_prod (μ := πX) (ν := ν) (infiniteBox F) (integralFiniteAdeles (𝓞 F) F)

  have hint : ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2 ∂μP
      = c • ((∫ y, f y) * ∫ z, g z ∂ν) := by
    rw [hμP, integral_smul_nnreal_measure]
    congr 1
    have h1 : ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2 ∂πP
        = (∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x) ∂πX) * ∫ z, g z ∂ν :=
      integral_prod_mul (μ := πX) (ν := ν) (fun x => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) g
    have h2 : ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x) ∂πX = ∫ y, f y := by
      have h3 := integral_map_equiv (μ := volume) eM
        (fun x => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x))
      refine (Eq.trans rfl h3).trans ?_
      congr 1
      funext y
      exact congrArg f ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
    exact h1.trans (by rw [h2])

  have hP0 : ν (integralFiniteAdeles (𝓞 F) F) ≠ 0 :=
    (isOpen_integralFiniteAdeles F).measure_ne_zero ν ⟨0, fun v => zero_mem _⟩
  have hPt : ν (integralFiniteAdeles (𝓞 F) F) ≠ ∞ := (isCompact_integralFiniteAdeles F).measure_ne_top
  have hP : (ν (integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hP0, hPt⟩
  have hd : Real.sqrt |(discr F : ℝ)| ≠ 0 := by
    rw [Real.sqrt_ne_zero (abs_nonneg _)]
    exact abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F))
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  have hP' : (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP
  have h2 : ((2 : ℝ) : ℂ) ^ nrComplexPlaces F ≠ 0 := pow_ne_zero _ (by norm_num)

  rw [hint, hbox, hπXbox, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, hV, NNReal.smul_def,
    Complex.real_smul]
  push_cast
  field_simp

end NumberField.AdelicBox

end
