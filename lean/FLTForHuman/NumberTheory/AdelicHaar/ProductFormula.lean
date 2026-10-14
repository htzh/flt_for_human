/-
  The product formula: principal ideles preserve additive Haar measure.

  The modulus of a principal idele is `1`. The proof is the four-node chain

  * `isAddFundamentalDomain_preimage_mul` — the `μ`-fundamental domain
    `(a ·) ⁻¹' adelicBox` for the principal adeles, from the box's unique
    representative property;
  * `addHaarScalarFactor_map_mulLeft` / `measurePreserving_mul` — the
    translation `x ↦ a x` is measure preserving, because it is an additive
    automorphism carrying one fundamental domain to another
    (`IsAddFundamentalDomain.measure_eq`) and `addHaarScalarFactor` is `1` by
    uniqueness of Haar measure;
  * `regular_adelicAddHaar` — the port's `adelicAddHaar` is regular;
  * `addHaarScalarFactor_eq_one_of_integral_eq` /
    `distribHaarChar_algebraMap_impl` — the modulus of the image of a unit is
    `1`, read off the invariance of the integral.

  Transcribed whole from the four pin `S_` files (pinned `aa2d8b3`), each
  except its final `solution`, whose headline belongs to the tier-1 façade
  `FLTForHuman/NumberTheory/AdelicModulus.lean`:

  * `P2M/Sol/S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean`
  * `P2M/Sol/S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean`
  * `P2M/Sol/S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean`
  * `P2M/Sol/S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean`

  The pin's cross-file `Theorems.` wrappers are replaced by this module's own
  declarations, so the four pin files are four sections of one file. The
  `p2m_*` scaffolding is dropped; no file-wide option beyond
  `set_option autoImplicit false` and the house `haveI` linter setting.
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing: they feed instance search in the `exact`s.
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

noncomputable section

namespace FltWs24

namespace AdelicModulusOne

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

-- pin: isAddFundamentalDomain_preimage_mul (S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean:18)
theorem isAddFundamentalDomain_preimage_mul [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) (a : F) (ha : a ≠ 0) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F 𝔸 a * x) ⁻¹' AdelicBox.adelicBox F) μ := by
  have hm : ‹MeasurableSpace 𝔸› = AdelicHaar.adeleBorel (𝓞 F) F := BorelSpace.measurable_eq
  subst hm
  letI : MeasurableSpace 𝔸 := AdelicHaar.adeleBorel (𝓞 F) F
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · exact ((AdelicBox.measurableSet_adelicBox F).preimage
      (measurable_const_mul (algebraMap F 𝔸 a))).nullMeasurableSet
  · obtain ⟨k, hk, huniq⟩ :=
      AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F (algebraMap F 𝔸 a * x)
    refine ⟨⟨algebraMap F 𝔸 (a⁻¹ * k), a⁻¹ * k, rfl⟩, ?_, ?_⟩
    · show algebraMap F 𝔸 a * (algebraMap F 𝔸 (a⁻¹ * k) + x) ∈ AdelicBox.adelicBox F
      rwa [mul_add, ← map_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    · rintro ⟨_, k', rfl⟩ hk'
      have hk'B : algebraMap F 𝔸 (a * k') + algebraMap F 𝔸 a * x ∈ AdelicBox.adelicBox F := by
        have h : algebraMap F 𝔸 a * (algebraMap F 𝔸 k' + x) ∈ AdelicBox.adelicBox F := hk'
        rwa [mul_add, ← map_mul] at h
      have hak : a * k' = k := huniq (a * k') hk'B
      have hk'eq : k' = a⁻¹ * k := by
        rw [← hak, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      subst hk'eq
      rfl

-- pin: principalUnit (S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean:16)
noncomputable def principalUnit (a : F) (ha : a ≠ 0) : 𝔸ˣ :=
  Units.map (algebraMap F 𝔸 : F →+* 𝔸).toMonoidHom (Units.mk0 a ha)

-- pin: mul_eq_coe_mulLeft (S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean:22)
theorem mul_eq_coe_mulLeft (a : F) (ha : a ≠ 0) :
    (fun x => algebraMap F 𝔸 a * x) = ⇑(ContinuousAddEquiv.mulLeft (principalUnit F a ha)) :=
  rfl

-- pin: countable_principalSubgroup (S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean:26)
theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  refine Function.Surjective.countable
    (f := fun k : F => (⟨algebraMap F 𝔸 k, k, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) ?_
  rintro ⟨x, k, rfl⟩
  exact ⟨k, rfl⟩

-- pin: addHaarScalarFactor_map_mulLeft (S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean:33)
theorem addHaarScalarFactor_map_mulLeft [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0)
    (hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F 𝔸 a * x) ⁻¹' AdelicBox.adelicBox F) μ) :
    (μ.map (ContinuousAddEquiv.mulLeft (principalUnit F a ha))).addHaarScalarFactor μ = 1 := by
  have hm : ‹MeasurableSpace 𝔸› = AdelicHaar.adeleBorel (𝓞 F) F := BorelSpace.measurable_eq
  subst hm
  letI : MeasurableSpace 𝔸 := AdelicHaar.adeleBorel (𝓞 F) F
  set e : 𝔸 ≃ₜ+ 𝔸 := ContinuousAddEquiv.mulLeft (principalUnit F a ha) with he
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  have hcl : IsCompact (closure (AdelicBox.adelicBox F)) := hC.closure_of_subset hBC
  have key := measure_isAddInvariant_eq_smul_of_isCompact_closure (μ.map e) μ hcl
  have hme : Measurable (⇑e) := e.continuous.measurable
  rw [Measure.map_apply hme (AdelicBox.measurableSet_adelicBox F)] at key
  haveI := countable_principalSubgroup F
  haveI : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 F) F) 𝔸 :=
    ⟨fun c => measurable_const_add (c : 𝔸)⟩
  haveI : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) 𝔸 μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : 𝔸) s⟩
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      (⇑e ⁻¹' AdelicBox.adelicBox F) μ := by
    rw [← mul_eq_coe_mulLeft F a ha]; exact hFD
  have hμeq : μ (⇑e ⁻¹' AdelicBox.adelicBox F) = μ (AdelicBox.adelicBox F) :=
    hFD'.measure_eq (AdelicBox.isAddFundamentalDomain_adelicBox F μ)
  rw [hμeq, ENNReal.smul_def, smul_eq_mul] at key
  have h0 : μ (AdelicBox.adelicBox F) ≠ 0 := (AdelicBox.measure_adelicBox_pos F μ).ne'
  have htop : μ (AdelicBox.adelicBox F) ≠ ⊤ := (AdelicBox.measure_adelicBox_lt_top F μ).ne
  have h1 : ((μ.map e).addHaarScalarFactor μ : ℝ≥0∞) = 1 := by
    rw [← ENNReal.mul_left_inj h0 htop, one_mul]; exact key.symm
  exact_mod_cast h1

-- pin: measurePreserving_mul (S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean:65)
theorem measurePreserving_mul [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] [μ.Regular] (a : F) (ha : a ≠ 0)
    (hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F 𝔸 a * x) ⁻¹' AdelicBox.adelicBox F) μ) :
    MeasurePreserving (fun x => algebraMap F 𝔸 a * x) μ μ := by
  have h1 := addHaarScalarFactor_map_mulLeft F μ a ha hFD
  rw [mul_eq_coe_mulLeft F a ha]
  set e : 𝔸 ≃ₜ+ 𝔸 := ContinuousAddEquiv.mulLeft (principalUnit F a ha) with he
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (μ.map e).Regular := Regular.map e.toHomeomorph
  have huniq := isAddLeftInvariant_eq_smul_of_regular (μ.map e) μ
  rw [h1, one_smul] at huniq
  exact ⟨e.continuous.measurable, huniq⟩

end AdelicModulusOne

section RegularAdelicAddHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel

-- pin: regular_adelicAddHaar (S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean:13)
-- The pin's `first | … | … | …` fallbacks are unreachable in mathlib `v4.34.0`: the first
-- alternative closes the goal, so only it is kept (statements unchanged).
theorem regular_adelicAddHaar (F : Type) [Field F] [NumberField F] :
    (AdelicHaar.adelicAddHaar (𝓞 F) F).Regular := by
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  exact (inferInstance : (Measure.addHaar : Measure (AdeleRing (𝓞 F) F)).Regular)

end RegularAdelicAddHaar

namespace AdelicModulusOneChar

-- pin: addHaarScalarFactor_eq_one_of_integral_eq (S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean:16)
theorem addHaarScalarFactor_eq_one_of_integral_eq {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ'] [μ'.IsAddLeftInvariant]
    (h : ∀ f : G → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂μ' = ∫ x, f x ∂μ) :
    addHaarScalarFactor μ' μ = 1 := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have hpos : 0 < ∫ x, f x ∂μ :=
    f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero
  have h1 := integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport μ' μ f_cont f_comp
  rw [h f f_cont f_comp, integral_smul_nnreal_measure] at h1
  have h2 : (addHaarScalarFactor μ' μ : ℝ) = 1 := by
    rw [NNReal.smul_def, smul_eq_mul] at h1
    field_simp at h1
    linarith [h1, hpos]
  exact_mod_cast h2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

-- pin: distribHaarChar_algebraMap_impl (S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean:37)
theorem distribHaarChar_algebraMap_impl [MeasurableSpace 𝔸] [BorelSpace 𝔸] (a : Fˣ) :
    distribHaarChar 𝔸 (Units.map (algebraMap F 𝔸).toMonoidHom a) = 1 := by
  set u : 𝔸ˣ := Units.map (algebraMap F 𝔸).toMonoidHom a with hu

  let μ : Measure 𝔸 := Measure.addHaar
  haveI : μ.Regular := by
    show (Measure.addHaar : Measure 𝔸).Regular
    unfold Measure.addHaar; infer_instance

  -- The pin calls the `Theorems/` wrapper; here the engine's own declarations replace it.
  have hmp : MeasurePreserving (fun x => (u : 𝔸) * x) μ μ :=
    AdelicModulusOne.measurePreserving_mul F μ (a : F) a.ne_zero
      (AdelicModulusOne.isAddFundamentalDomain_preimage_mul F μ (a : F) a.ne_zero)

  have hsf : addHaarScalarFactor (DomMulAct.mk u⁻¹ • μ : Measure 𝔸) μ = 1 := by
    refine addHaarScalarFactor_eq_one_of_integral_eq _ μ fun f hf hfc => ?_
    rw [integral_domSMul]
    simp only [Equiv.symm_apply_apply, inv_inv]
    have hme : MeasurableEmbedding (fun x => (u : 𝔸) * x) :=
      (ContinuousAddEquiv.mulLeft u).toHomeomorph.measurableEmbedding
    exact hmp.integral_comp hme f
  have hinv : distribHaarChar 𝔸 u⁻¹ = 1 := by
    rw [← addHaarScalarFactor_smul_eq_distribHaarChar μ u⁻¹]
    exact hsf
  rwa [map_inv (distribHaarChar 𝔸) u, inv_eq_one] at hinv

end AdelicModulusOneChar

end FltWs24
