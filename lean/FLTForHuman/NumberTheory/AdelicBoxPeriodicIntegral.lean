/-
  The adelic box: the periodic `lintegral` and the conditional integral along `K -> A`.

  Two rows on the additive Haar measure of the adele ring and the box `adelicBox K`:

  * `setLIntegral_adelicBox_comp_mul_add_eq_of_periodic`: for a function periodic along the
    rational adeles (period `algebraMap K (AdeleRing ...) beta`), the `lintegral` over the box of the
    composed function equals the `lintegral` over the whole adele ring -- the box is a fundamental
    domain for `K`'s action (`distribHaarChar_algebraMap` is the character identity the change of
    variables spends).
  * `integral_cond_adelicBox_comp_mul_algebraMap`: the corresponding conditional integral against
    `adelicBox K` of a function pulled back along `algebraMap K (AdeleRing ...)`: it is the
    conditional integral over the box itself, by measure preservation
    (`measurePreserving_mul_algebraMap_adelicAddHaar`) and the fundamental-domain property
    (`isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`).

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic.lean` (129 lines,
  six public rows) and
  `P2M/Sol/S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.lean` (122 lines, seven
  public rows), with the statements from the wrappers of the same names.  Both pin label namespaces are
  machine tokens and are rectified to the word namespaces `PeriodicBoxIntegral` and `CondBoxIntegral`;
  the prelude rows are public in the pin and stay public here, so the module is checker-visible beyond
  the two headlines.

  Assumes from earlier modules: `NumberTheory/AdelicBox.lean` (the box itself),
  `NumberTheory/AdelicHaar/{GeneralLinear,PlaceMeasure}.lean` (the Haar measures and the character) and
  `NumberTheory/AdelicLevel/Level.lean`.
  spec-pin: Theorems/Thm_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic.lean
  spec-pin: Theorems/Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.lean
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicModulus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped NNReal ENNReal Pointwise ProbabilityTheory

namespace PeriodicBoxIntegral

open scoped Pointwise

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

scoped instance instCountableF : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

scoped instance instCountablePrincipal : Countable ↥(AdeleRing.principalSubgroup (𝓞 F) F) := by
  refine Function.Surjective.countable
    (f := fun k : F => (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : ↥(AdeleRing.principalSubgroup (𝓞 F) F)))
    ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

theorem regular_adelicAddHaar : (adelicAddHaar (𝓞 F) F).Regular := by
  exact NumberField.AdelicHaar.regular_adelicAddHaar F

def affineHomeo (c : (AdeleRing (𝓞 F) F)ˣ) (u₀ : AdeleRing (𝓞 F) F) :
    AdeleRing (𝓞 F) F ≃ₜ AdeleRing (𝓞 F) F where
  toEquiv := c.mulLeft.trans (Equiv.addRight u₀)
  continuous_toFun := by
    show Continuous fun u => (c : AdeleRing (𝓞 F) F) * u + u₀
    exact (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := by
    show Continuous fun v => ((c⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (v + -u₀)
    exact continuous_const.mul (continuous_id.add continuous_const)

theorem affineHomeo_apply (c : (AdeleRing (𝓞 F) F)ˣ) (u₀ u : AdeleRing (𝓞 F) F) :
    affineHomeo F c u₀ u = (c : AdeleRing (𝓞 F) F) * u + u₀ := by
  rfl

theorem measurePreserving_mul_principal (a : Fˣ) :
    MeasurePreserving (fun u : AdeleRing (𝓞 F) F =>
      ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * u)
      (adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F) := by
  have := regular_adelicAddHaar F
  set c : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a with hc
  refine ⟨measurable_const_mul _, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_mul _) hs]
  have hpre : (fun u : AdeleRing (𝓞 F) F => (c : AdeleRing (𝓞 F) F) * u) ⁻¹' s = c⁻¹ • s := by
    ext u
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul (adelicAddHaar (𝓞 F) F) c⁻¹ s, map_inv, hc,
    NumberField.AdeleRing.distribHaarChar_algebraMap F a, inv_one, ENNReal.coe_one, one_mul]

theorem main (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F), h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u)
    (a : Fˣ) (u₀ : AdeleRing (𝓞 F) F) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ
  set c : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a with hc
  set T := affineHomeo F c u₀ with hTdef
  have hTapp : ∀ u, T u = algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀ := fun u => rfl

  have hmp : MeasurePreserving T μ μ := by
    have h1 := measurePreserving_mul_principal F a
    have h2 : MeasurePreserving (fun v : AdeleRing (𝓞 F) F => v + u₀) μ μ :=
      measurePreserving_add_right μ u₀
    exact h2.comp h1
  have hmp' : MeasurePreserving T.toMeasurableEquiv μ μ := hmp
  have hqmp : Measure.QuasiMeasurePreserving T.toEquiv.symm μ μ :=
    (hmp'.symm T.toMeasurableEquiv).quasiMeasurePreserving

  let P := AdeleRing.principalSubgroup (𝓞 F) F
  have hmemc : ∀ g : ↥P, (c : AdeleRing (𝓞 F) F) * (g : AdeleRing (𝓞 F) F) ∈ P := by
    rintro ⟨_, k, rfl⟩
    refine ⟨(a : F) * k, ?_⟩
    rw [map_mul]
    rfl
  have hmemci : ∀ g : ↥P,
      ((c⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (g : AdeleRing (𝓞 F) F) ∈ P := by
    rintro ⟨_, k, rfl⟩
    refine ⟨((a⁻¹ : Fˣ) : F) * k, ?_⟩
    rw [map_mul, hc, ← map_inv]
    rfl
  let e : ↥P ≃ ↥P :=
    { toFun := fun g => ⟨((c⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * g, hmemci g⟩
      invFun := fun g => ⟨(c : AdeleRing (𝓞 F) F) * g, hmemc g⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  have hef : ∀ g : ↥P, Function.Semiconj T.toEquiv (fun u => e g +ᵥ u) (fun u => g +ᵥ u) := by
    intro g u
    show (c : AdeleRing (𝓞 F) F) *
        (((c⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (g : AdeleRing (𝓞 F) F) + u) + u₀ =
      (g : AdeleRing (𝓞 F) F) + ((c : AdeleRing (𝓞 F) F) * u + u₀)
    rw [mul_add, ← mul_assoc, Units.mul_inv, one_mul, add_assoc]
  have hFD : IsAddFundamentalDomain ↥P (T.toEquiv '' adelicBox F) μ :=
    (isAddFundamentalDomain_adelicBox F μ).image_of_equiv T.toEquiv hqmp e hef
  have hinv : ∀ (g : ↥P) (x : AdeleRing (𝓞 F) F), h (g +ᵥ x) = h x := by
    rintro ⟨_, k, rfl⟩ x
    exact hper k x
  -- The pin's `setLIntegral_comp_emb` is replaced by its `Measurable`-taking sibling
  -- (`setLIntegral_comp_preimage`), the route that spends the statement's `hh`.
  have hmid : ∫⁻ u in adelicBox F, h (T u) ∂μ = ∫⁻ v in T '' adelicBox F, h v ∂μ := by
    nth_rewrite 1 [← Set.preimage_image_eq (adelicBox F) T.injective]
    exact hmp.setLIntegral_comp_preimage
      (T.measurableEmbedding.measurableSet_image' (measurableSet_adelicBox F)) hh
  calc ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀) ∂μ
      = ∫⁻ u in adelicBox F, h (T u) ∂μ := by rfl
    _ = ∫⁻ v in T '' adelicBox F, h v ∂μ := hmid
    _ = ∫⁻ v in adelicBox F, h v ∂μ :=
      hFD.setLIntegral_eq (isAddFundamentalDomain_adelicBox F μ) h hinv

end PeriodicBoxIntegral

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
    (F : Type) [Field F] [NumberField F]
    (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F), h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u)
    (a : Fˣ) (u₀ : AdeleRing (𝓞 F) F) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) :=
  PeriodicBoxIntegral.main F h hh hper a u₀

namespace CondBoxIntegral
namespace BoxChangeOfVariables

section Core
variable {G : Type*} [AddGroup G] [Countable G] {α : Type*} [AddAction G α] [MeasurableSpace α]
  [MeasurableConstVAdd G α] {μ : Measure α} [VAddInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem setIntegral_comp_eq_of_isAddFundamentalDomain
    {s t : Set α} (hs : IsAddFundamentalDomain G s μ) (ht : IsAddFundamentalDomain G t μ)
    {T : α → α} (hT : MeasurePreserving T μ μ) (hTe : MeasurableEmbedding T) (hst : T ⁻¹' t = s)
    {f : α → E} (hf : ∀ (g : G) (x : α), f (g +ᵥ x) = f x) :
    ∫ x in s, f (T x) ∂μ = ∫ x in s, f x ∂μ := by
  calc ∫ x in s, f (T x) ∂μ = ∫ x in T ⁻¹' t, f (T x) ∂μ := by rw [hst]
    _ = ∫ y in t, f y ∂μ := hT.setIntegral_preimage_emb hTe f t
    _ = ∫ x in s, f x ∂μ := ht.setIntegral_eq hs hf

theorem integral_cond_comp_eq_of_isAddFundamentalDomain
    {s t : Set α} (hs : IsAddFundamentalDomain G s μ) (ht : IsAddFundamentalDomain G t μ)
    {T : α → α} (hT : MeasurePreserving T μ μ) (hTe : MeasurableEmbedding T) (hst : T ⁻¹' t = s)
    {f : α → E} (hf : ∀ (g : G) (x : α), f (g +ᵥ x) = f x) :
    ∫ x, f (T x) ∂(ProbabilityTheory.cond μ s) = ∫ x, f x ∂(ProbabilityTheory.cond μ s) := by
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  rw [setIntegral_comp_eq_of_isAddFundamentalDomain hs ht hT hTe hst hf]

end Core

section Adelic
variable (F : Type) [Field F] [NumberField F]

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  refine Function.Surjective.countable
    (f := fun k : F =>
      (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) ?_
  rintro ⟨x, k, rfl⟩
  exact ⟨k, rfl⟩

theorem preimage_mul_algebraMap_preimage_inv (a : F) (ha : a ≠ 0) (B : Set (AdeleRing (𝓞 F) F)) :
    (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹'
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x) ⁻¹' B) = B := by
  ext x
  simp only [Set.mem_preimage, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]

def mulAlgebraMapMeasurableEquiv
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [MeasurableMul (AdeleRing (𝓞 F) F)]
    (a : F) (ha : a ≠ 0) : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F where
  toFun x := algebraMap F (AdeleRing (𝓞 F) F) a * x
  invFun x := algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x
  left_inv x := by
    show algebraMap F _ a⁻¹ * (algebraMap F _ a * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  right_inv x := by
    show algebraMap F _ a * (algebraMap F _ a⁻¹ * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  measurable_toFun := measurable_const_mul _
  measurable_invFun := measurable_const_mul _

theorem integral_cond_comp_mul_algebraMap_of_isAddFundamentalDomain
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : Set (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0)
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) B μ)
    (hBinv : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x) ⁻¹' B) μ)
    (hT : MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x) ∂(ProbabilityTheory.cond μ B)
      = ∫ x, f x ∂(ProbabilityTheory.cond μ B) := by
  have := countable_principalSubgroup F
  have : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) :=
    ⟨fun c => measurable_const_add (c : AdeleRing (𝓞 F) F)⟩
  have : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : AdeleRing (𝓞 F) F) s⟩
  have hf' : ∀ (g : AdeleRing.principalSubgroup (𝓞 F) F) (x : AdeleRing (𝓞 F) F),
      f (g +ᵥ x) = f x := by
    rintro ⟨_, k, rfl⟩ x
    exact hf k x
  exact integral_cond_comp_eq_of_isAddFundamentalDomain hB hBinv hT
    (mulAlgebraMapMeasurableEquiv F a ha).measurableEmbedding
    (preimage_mul_algebraMap_preimage_inv F a ha B) hf'

end Adelic

end CondBoxIntegral.BoxChangeOfVariables

attribute [local instance] NumberField.AdelicHaar.adeleBorel
theorem NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap
    (F : Type) [Field F] [NumberField F]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x)
    (a : F) (ha : a ≠ 0) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x)
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
      = ∫ x, f x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) := by
  have : BorelSpace (AdeleRing (𝓞 F) F) := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  have := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  exact CondBoxIntegral.BoxChangeOfVariables.integral_cond_comp_mul_algebraMap_of_isAddFundamentalDomain
    F (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) a ha
    (AdelicBox.isAddFundamentalDomain_adelicBox F _)
    (NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F _
      a⁻¹ (inv_ne_zero ha))
    (NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar F a ha)
    hf
