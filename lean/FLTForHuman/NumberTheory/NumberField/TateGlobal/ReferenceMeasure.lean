/-
  The reference measure on `Q S = arch × (S × deep)` and the constant that
  compares it with `asmMeasure`: `deepRef` is the probability Haar measure on
  the deep units, `sRef`/`archRef` the products of the local multiplicative Haar
  measures, `refMeasure` their product, `refConst` the Haar scalar factor; the
  section also restates `localZeta` through `mulHaar`/`mulHaarCompletion` and
  computes the factorwise integrals.

  Transcribed from the pin's `Fold_TateReference` section (`NumberField.TateGlobal`
  blocks `RangeVal` … `Factorwise`), declared lines 2894-3231 of file A, pinned
  `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, and so are the
  `set_option synthInstance.maxHeartbeats 800000 in` wrappers on the
  `LocallyCompactSpace`/`isHaarMeasure_refMeasure` instances (the port's global
  instances elaborate at the low edit cap).  The pin's file-scoped
  `attribute [local instance] countable_heightOneSpectrum` (A 2944) is
  re-declared here (work order §8.5), as is the pin's `section Instances` block
  of `scoped instance`s for the `BorelSpace`/`MeasurableMul` instances that the
  local Haar measures need.  No file-wide option beyond `setOption autoImplicit
  false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ValuedOrdBridge
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_TateReference



open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

section RangeVal

variable {K : Type*} [GroupWithZero K]

-- pin: range_units_val (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2894)
theorem range_units_val : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

end RangeVal

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

-- pin: mulMeasure_singleton_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2911)
theorem mulMeasure_singleton_zero (μ : Measure K) : mulMeasure μ {0} = 0 := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_singleton 0),
    Measure.restrict_restrict (measurableSet_singleton 0), Set.inter_compl_self, Measure.restrict_empty,
    lintegral_zero_measure]

-- pin: mulMeasure_restrict_compl_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2916)
theorem mulMeasure_restrict_compl_zero (μ : Measure K) : (mulMeasure μ).restrict {0}ᶜ = mulMeasure μ := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have h : {a : K | ¬a ∈ ({0}ᶜ : Set K)} = {0} := by
    ext a
    simp
  rw [h]
  exact mulMeasure_singleton_zero μ

variable [MeasurableSpace Kˣ]

-- pin: integral_comp_val_comap_mulMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2927)
theorem integral_comp_val_comap_mulMeasure (hval : MeasurableEmbedding (Units.val : Kˣ → K)) (μ : Measure K)
    (φ : K → ℂ) : ∫ t, φ (t : K) ∂(Measure.comap Units.val (mulMeasure μ)) = ∫ x, φ x ∂(mulMeasure μ) := by
  rw [← hval.integral_map, hval.map_comap, range_units_val, mulMeasure_restrict_compl_zero]

-- pin: localZeta_eq_integral_comap (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2931)
theorem localZeta_eq_integral_comap (hval : MeasurableEmbedding (Units.val : Kˣ → K)) (μ : Measure K)
    (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ f χ s
      = ∫ t, f t * (χ t : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ s ∂(Measure.comap Units.val (mulMeasure μ)) := by
  have h := integral_comp_val_comap_mulMeasure hval μ (fun x => f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
  simp only [charExt_coe_units] at h
  rw [localZeta, ← h]

end CompVal

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] countable_heightOneSpectrum

section Instances

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: instLocallyCompactSpaceArchUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2951)
scoped instance instLocallyCompactSpaceArchUnits : LocallyCompactSpace (InfiniteAdeleRing F)ˣ := inferInstance

-- pin: instLocallyCompactSpaceSUnitsProdDeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2954)
scoped instance instLocallyCompactSpaceSUnitsProdDeepUnits :
    LocallyCompactSpace (SUnits (F := F) S × DeepUnits (F := F) S) := inferInstance

-- pin: instLocallyCompactSpaceQ (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2958)
scoped instance instLocallyCompactSpaceQ : LocallyCompactSpace (Q (F := F) S) := inferInstance

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

-- pin: instBorelSpaceDeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2963)
scoped instance instBorelSpaceDeepUnits : BorelSpace (DeepUnits (F := F) S) := Pi.borelSpace

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

-- pin: instBorelSpaceSUnitsProdDeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2968)
scoped instance instBorelSpaceSUnitsProdDeepUnits : BorelSpace (SUnits (F := F) S × DeepUnits (F := F) S) :=
  Prod.borelSpace

-- pin: instMeasurableMulSUnitsProdDeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2971)
scoped instance instMeasurableMulSUnitsProdDeepUnits : MeasurableMul (SUnits (F := F) S × DeepUnits (F := F) S) :=
  inferInstance

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

-- pin: instBorelSpaceQ (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2976)
scoped instance instBorelSpaceQ : BorelSpace (Q (F := F) S) := Prod.borelSpace

-- pin: instMeasurableMulArchUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2978)
scoped instance instMeasurableMulArchUnits : MeasurableMul (InfiniteAdeleRing F)ˣ := inferInstance

end Instances

section Deep

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

-- pin: deepRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2990)
def deepRef : Measure (DeepUnits (F := F) S) := haarMeasure ⊤

-- pin: isHaarMeasure_deepRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2992)
scoped instance isHaarMeasure_deepRef : (deepRef (F := F) S).IsHaarMeasure := by
  unfold deepRef
  infer_instance

-- pin: deepRef_univ (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2996)
theorem deepRef_univ : deepRef (F := F) S Set.univ = 1 := by
  rw [deepRef, ← PositiveCompacts.coe_top]
  exact haarMeasure_self

-- pin: isProbabilityMeasure_deepRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3000)
scoped instance isProbabilityMeasure_deepRef : IsProbabilityMeasure (deepRef (F := F) S) :=
  ⟨deepRef_univ S⟩

end Deep

section SFactor

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

-- pin: instIsHaarMeasureMulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3015)
scoped instance instIsHaarMeasureMulHaar (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] : (MulHaarFromAdditive.mulHaar μ).IsHaarMeasure := by
  obtain ⟨ϖ, hϖ, -⟩ := ValuedOrdBridge.exists_irreducible_valued (v := v)
  exact MulHaarFromAdditive.isHaarMeasure_mulHaar μ hϖ

-- pin: sRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3020)
def sRef (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) : Measure (SUnits (F := F) S) :=
  Measure.pi fun v : S => MulHaarFromAdditive.mulHaar (μf v.1)

-- pin: isHaarMeasure_sRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3023)
scoped instance isHaarMeasure_sRef (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] : (sRef S μf).IsHaarMeasure := by
  unfold sRef
  infer_instance

-- pin: sigmaFinite_sRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3028)
scoped instance sigmaFinite_sRef (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] : SigmaFinite (sRef S μf) := by
  unfold sRef
  infer_instance

-- pin: localZeta_eq_integral_mulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3033)
theorem localZeta_eq_integral_mulHaar {v : HeightOneSpectrum (𝓞 F)} (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) :
    localZeta μ f χ s = ∫ t, f t * (χ t : ℂ) * ((modulus (t : v.adicCompletion F) : ℝ) : ℂ) ^ s
      ∂(MulHaarFromAdditive.mulHaar μ) :=
  localZeta_eq_integral_comap MulHaarFromAdditive.measurableEmbedding_val μ f χ s

end SFactor

section Arch

-- pin: archPiUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3044)
def archPiUnits : (InfiniteAdeleRing F)ˣ ≃ₜ* ((w : InfinitePlace F) → (w.Completion)ˣ) :=
  ContinuousMulEquiv.piUnits

omit [NumberField F] in
-- pin: archPiUnits_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3048)
theorem archPiUnits_apply (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    ((archPiUnits a w : (w.Completion)ˣ) : w.Completion) = (a : InfiniteAdeleRing F) w := rfl

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

-- pin: instIsHaarMeasureMulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3054)
scoped instance instIsHaarMeasureMulHaarCompletion (w : InfinitePlace F) (μ : Measure w.Completion)
    [μ.IsAddHaarMeasure] : (ArchMulHaarCompletion.mulHaarCompletion w μ).IsHaarMeasure :=
  ArchMulHaarCompletion.isHaarMeasure_mulHaarCompletion_total w

omit [NumberField F] in
-- pin: localZeta_eq_integral_mulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3059)
theorem localZeta_eq_integral_mulHaarCompletion (w : InfinitePlace F) (μ : Measure w.Completion)
    (f : w.Completion → ℂ) (χ : (w.Completion)ˣ →* ℂˣ) (s : ℂ) :
    localZeta μ f χ s = ∫ t, f t * (χ t : ℂ) * ((modulus (t : w.Completion) : ℝ) : ℂ) ^ s
      ∂(ArchMulHaarCompletion.mulHaarCompletion w μ) :=
  localZeta_eq_integral_comap (ArchMulHaarCompletion.measurableEmbedding_val_completion w) μ f χ s

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

-- pin: archRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3067)
def archRef (μa : (w : InfinitePlace F) → Measure (w.Completion)) : Measure (InfiniteAdeleRing F)ˣ :=
  (Measure.pi fun w : InfinitePlace F => ArchMulHaarCompletion.mulHaarCompletion w (μa w)).map
    (archPiUnits (F := F)).symm

-- pin: isHaarMeasure_archRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3071)
scoped instance isHaarMeasure_archRef (μa : (w : InfinitePlace F) → Measure (w.Completion))
    [∀ w, (μa w).IsAddHaarMeasure] : (archRef μa).IsHaarMeasure := by
  unfold archRef
  infer_instance

-- pin: sigmaFinite_archRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3076)
scoped instance sigmaFinite_archRef (μa : (w : InfinitePlace F) → Measure (w.Completion))
    [∀ w, (μa w).IsAddHaarMeasure] : SigmaFinite (archRef μa) :=
  inferInstance

omit [∀ w : InfinitePlace F, BorelSpace (w.Completion)] in
-- pin: integral_archRef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3081)
theorem integral_archRef (μa : (w : InfinitePlace F) → Measure (w.Completion)) (G : (InfiniteAdeleRing F)ˣ → ℂ) :
    ∫ a, G a ∂(archRef μa)
      = ∫ t, G ((archPiUnits (F := F)).symm t)
          ∂(Measure.pi fun w : InfinitePlace F => ArchMulHaarCompletion.mulHaarCompletion w (μa w)) := by
  unfold archRef
  exact (archPiUnits (F := F)).symm.toHomeomorph.measurableEmbedding.integral_map G

end Arch

section Reference

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

-- pin: refMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3107)
def refMeasure : Measure (Q (F := F) S) := (archRef μa).prod ((sRef S μf).prod (deepRef S))

-- pin: isHaarMeasure_refMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3110)
scoped instance isHaarMeasure_refMeasure : (refMeasure S μa μf).IsHaarMeasure := by
  unfold refMeasure
  infer_instance

-- pin: integral_refMeasure_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3114)
theorem integral_refMeasure_mul (A : (InfiniteAdeleRing F)ˣ → ℂ) (B : SUnits (F := F) S → ℂ)
    (C : DeepUnits (F := F) S → ℂ) :
    ∫ q, A q.1 * (B q.2.1 * C q.2.2) ∂(refMeasure S μa μf)
      = (∫ a, A a ∂(archRef μa)) * ((∫ t, B t ∂(sRef S μf)) * ∫ o, C o ∂(deepRef S)) := by
  unfold refMeasure
  rw [integral_prod_mul (μ := archRef μa) A (fun p : SUnits (F := F) S × DeepUnits (F := F) S => B p.1 * C p.2),
    integral_prod_mul]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

-- pin: refConst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3125)
def refConst : ℝ≥0 := haarScalarFactor (asmMeasure S ν) (refMeasure S μa μf)

-- pin: refConst_pos (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3127)
theorem refConst_pos : 0 < refConst S μa μf ν :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

-- pin: asmMeasure_eq_refConst_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3130)
theorem asmMeasure_eq_refConst_smul : asmMeasure S ν = refConst S μa μf ν • refMeasure S μa μf :=
  isMulLeftInvariant_eq_smul _ _

-- pin: integral_asmMeasure_eq_refConst_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3133)
theorem integral_asmMeasure_eq_refConst_mul (G : Q (F := F) S → ℂ) :
    ∫ q, G q ∂(asmMeasure S ν) = ((refConst S μa μf ν : ℝ) : ℂ) * ∫ q, G q ∂(refMeasure S μa μf) := by
  rw [asmMeasure_eq_refConst_smul S μa μf ν, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

-- pin: setIntegral_unitsOutside_eq_refConst_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3137)
theorem setIntegral_unitsOutside_eq_refConst_mul (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), G x ∂ν
      = ((refConst S μa μf ν : ℝ) : ℂ) * ∫ q, G (asm S q) ∂(refMeasure S μa μf) := by
  rw [setIntegral_unitsOutside_eq_integral_asmMeasure, integral_asmMeasure_eq_refConst_mul S μa μf ν]

end Reference

section Factorwise

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

section DeepConst

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

-- pin: integral_deepRef_const (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3154)
theorem integral_deepRef_const (c : ℂ) : ∫ _o, c ∂(deepRef (F := F) S) = c := by
  rw [integral_const, probReal_univ, one_smul]

end DeepConst

section SProd

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

-- pin: integral_sRef_prod (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3167)
theorem integral_sRef_prod (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] (φ : (v : S) → (v.1.adicCompletion F)ˣ → ℂ) :
    ∫ t, ∏ v : S, φ v (t v) ∂(sRef S μf) = ∏ v : S, ∫ u, φ v u ∂(MulHaarFromAdditive.mulHaar (μf v.1)) :=
  integral_fintype_prod_eq_prod φ

end SProd

section ArchProd

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

-- pin: integral_archRef_prod (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3181)
theorem integral_archRef_prod (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (φ : (w : InfinitePlace F) → (w.Completion)ˣ → ℂ) :
    ∫ a, ∏ w, φ w (archPiUnits a w) ∂(archRef μa)
      = ∏ w, ∫ t, φ w t ∂(ArchMulHaarCompletion.mulHaarCompletion w (μa w)) := by
  rw [integral_archRef]
  simp only [ContinuousMulEquiv.apply_symm_apply]
  exact integral_fintype_prod_eq_prod φ

end ArchProd

end Factorwise

end NumberField.TateGlobal

end



end Fold_TateReference
