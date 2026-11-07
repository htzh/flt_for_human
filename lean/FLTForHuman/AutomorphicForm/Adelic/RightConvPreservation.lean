/-
  What right convolution preserves.

  Right convolution `rightConv F φ f` by a factorisable test function `f` keeps the structures the
  cuspidal side of the adelic theory is built from:

  * `isCuspidalFn_rightConv`: if `φ` is continuous and cuspidal for the production pins of a set `D`,
    a family of open subgroups `U` and Hecke generators `gen`, then so is `rightConv F φ f` — the
    constant term of a convolution kills the unipotent average, which is the cuspidality of `φ`;
  * `isKfSmooth_rightConv`: `rightConv F φ f` is `K_f`-smooth, i.e. invariant under a compact open
    subgroup of the finite adèles, because `f` is: `f` is locally constant with compact support, so
    it is invariant under some `K_f ⊆ GL₂(𝔸_fin)`, and the invariance passes through the integral;
  * `rightConv_rightConv_eq_rightConv_rightConv_comp_inv`: associativity of convolution in the form
    `(φ * f) * h = φ * (h * f∘inv)` — the `GL₂(𝔸)` convolution algebra's product, with the inverse
    twist on the right factor.

  Transcribed from the pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_isCuspidalFn_rightConv.lean`
  * `P2M/Sol/S_AutomorphicForm_isKfSmooth_rightConv.lean`
  * `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv.lean`

  The pin's helper `G2Aux.constantTerm_eq_zero_of_eq_integral_kernel` (the Fubini step that turns a
  convolution's constant term into an integral of `φ`'s) is public here, at the pin's name.

  **Wiring.** `spec/check_port.py` owns the three public declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_isCuspidalFn_rightConv.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isCuspidalFn_rightConv.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isKfSmooth_rightConv.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isKfSmooth_rightConv.lean
  spec-pin: Theorems/Thm_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.Topology.Algebra.LocallyConstantCompactSupport
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace G2Aux

/-- The constant term of an integral of right translates of a cuspidal function vanishes. -/
theorem constantTerm_eq_zero_of_eq_integral_kernel
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [SFinite ν]
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {G : Type*} [Group G] (u : Q → G) (r : X → G) (k : X → ℂ) (ψ Ψ : G → ℂ)
    (hψ : IsCuspidalFn ν u ψ)
    (hΨ : ∀ h : G, Ψ h = ∫ x, k x * ψ (h * r x) ∂μ)
    (g : G)
    (hint : Integrable (fun p : Q × X => k p.2 * ψ (u p.1 * g * r p.2)) (ν.prod μ)) :
    constantTerm ν u Ψ g = 0 := by
  simp only [constantTerm, constantTermIntegrand, hΨ]
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun q x => k x * ψ (u q * g * r x)) hint
  rw [hswap]
  have h0 : ∀ x : X, ∫ q, k x * ψ (u q * g * r x) ∂ν = 0 := fun x => by
    rw [integral_const_mul]
    simp_rw [mul_assoc]
    have hzero := hψ (g * r x)
    simp only [constantTerm, constantTermIntegrand] at hzero
    rw [hzero, mul_zero]
  simp [h0]

end G2Aux

theorem isCuspidalFn_rightConv
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 (rightConv F φ f) := by
  classical
  have _scA : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology F
  have _scG : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  let _measA : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  have _borelA : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  have _addHaar : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure :=
    isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have _haar : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  let ν₀ : Measure (AdeleRing (𝓞 F) F) :=
    ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)
  have _prob : IsProbabilityMeasure ν₀ := isProbabilityMeasure_cond_adelicBox F
  change IsCuspidalFn ν₀ unipotentGL2 (rightConv F φ f)
  have hcusp' : IsCuspidalFn ν₀ unipotentGL2 φ := hcusp
  obtain ⟨hfc, hfsupp⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  intro g
  refine G2Aux.constantTerm_eq_zero_of_eq_integral_kernel ν₀
    (adelicGLHaar (Fin 2) (𝓞 F) F) unipotentGL2 id f φ (rightConv F φ f) hcusp'
    (fun h => ?_) g ?_
  · simp only [rightConv, id]
    exact integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
  · obtain ⟨Cb, hCb, hboxCb⟩ := exists_isCompact_adelicBox_subset F
    have hmap : Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        unipotentGL2 p.1 * g * p.2 :=
      ((continuous_unipotentGL2.comp continuous_fst).mul continuous_const).mul continuous_snd
    obtain ⟨M₀, hM₀⟩ := ((hCb.prod hfsupp).image hmap).exists_bound_of_continuousOn
      (f := φ) hcont.continuousOn
    set M := max M₀ 0 with hM
    have hMφ : ∀ (q : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), q ∈ adelicBox F →
        x ∈ tsupport f → ‖φ (unipotentGL2 q * g * x)‖ ≤ M := fun q x hq hx =>
      (hM₀ _ ⟨(q, x), ⟨hboxCb hq, hx⟩, rfl⟩).trans (le_max_left _ _)
    have hae : ∀ᵐ p ∂(ν₀.prod (adelicGLHaar (Fin 2) (𝓞 F) F)), p.1 ∈ adelicBox F := by
      have h1 : ∀ᵐ q ∂ν₀, q ∈ adelicBox F :=
        ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
      exact (Measure.quasiMeasurePreserving_fst).ae h1
    have hfint : Integrable f (adelicGLHaar (Fin 2) (𝓞 F) F) :=
      hfc.integrable_of_hasCompactSupport hfsupp
    have hf2 : Integrable (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => f p.2)
        (ν₀.prod (adelicGLHaar (Fin 2) (𝓞 F) F)) := by
      simpa using (integrable_const (1 : ℂ)).mul_prod hfint
    have hcont2 : Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        φ (unipotentGL2 p.1 * g * p.2) := hcont.comp hmap
    refine (hf2.norm.mul_const M).mono' (hf2.aestronglyMeasurable.mul hcont2.aestronglyMeasurable)
      (hae.mono fun p hp => ?_)
    rw [norm_mul, id]
    by_cases hx : p.2 ∈ tsupport f
    · exact mul_le_mul_of_nonneg_left (hMφ p.1 p.2 hp hx) (norm_nonneg _)
    · have hzero : f p.2 = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hzero, hM]

theorem isKfSmooth_rightConv
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsKfSmooth F (rightConv F φ f) := by
  classical
  obtain ⟨fa, ff, _hfa, hff, hfac⟩ := hf
  obtain ⟨V, hV1, hV⟩ :=
    IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hff.1 hff.2
  have h1V : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ V := mem_of_mem_nhds hV1
  set V' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := V ∩ (fun u => u⁻¹) ⁻¹' V with hV'
  have hV'1 : V' ∈ nhds (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
    refine Filter.inter_mem hV1 ?_
    exact continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hV1)
  have hleftf : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ V' →
      ∀ y : AdelicGL2 (𝓞 F) F, f (k⁻¹ * y) = f y := by
    intro k hk hkV y
    rw [hfac, hfac y, map_mul, map_mul, map_inv, map_inv, hk, inv_one, one_mul]
    congr 1
    have hstep := hV (glFin (𝓞 F) F k)⁻¹ hkV.2 1 h1V (glFin (𝓞 F) F y)
    simpa using hstep
  have _haar : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hinv : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ V' →
      ∀ g : AdelicGL2 (𝓞 F) F, rightConv F φ f (g * k) = rightConv F φ f g := by
    intro k hk hkV g
    show (∫ x, φ (g * k * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    have h := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
      (fun x => φ (g * k * x) * f x) k⁻¹
    rw [← h]
    congr 1
    funext x
    rw [hleftf k hk hkV x]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hcont : Continuous fun k : ↥(finiteAdelicGL2Subgroup F) =>
      glFin (𝓞 F) F (k : AdelicGL2 (𝓞 F) F) :=
    (continuous_glFin (𝓞 F) F).comp continuous_subtype_val
  have hW : (fun k : ↥(finiteAdelicGL2Subgroup F) =>
      glFin (𝓞 F) F (k : AdelicGL2 (𝓞 F) F)) ⁻¹' V' ∈
      nhds (1 : ↥(finiteAdelicGL2Subgroup F)) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hV'1)
  refine Filter.mem_of_superset hW ?_
  intro k hk
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  refine FLT.SmoothVectors.RightTranslationFn.ext fun g => ?_
  rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk]
  exact hinv k ((mem_finiteAdelicGL2Subgroup_iff F k).mp k.2) hk g

theorem rightConv_rightConv_eq_rightConv_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (f h : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (rightConv F h fun x => f x⁻¹) := by
  have _scG : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have _haar : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  funext g
  show (∫ y, (∫ x, φ (g * y * x) * f x ∂μ) * h y ∂μ) =
    ∫ z, φ (g * z) * (∫ x, h (z * x) * f x⁻¹ ∂μ) ∂μ
  have h1 : ∀ y : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∫ x, φ (g * y * x) * f x ∂μ) = ∫ x, φ (g * x) * f (y⁻¹ * x) ∂μ := by
    intro y
    rw [← integral_mul_left_eq_self (fun x => φ (g * x) * f (y⁻¹ * x)) y]
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : ∀ z : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∫ x, h (z * x) * f x⁻¹ ∂μ) = ∫ y, h y * f (y⁻¹ * z) ∂μ := by
    intro z
    rw [← integral_mul_left_eq_self (fun y => h y * f (y⁻¹ * z)) z]
    simp only [mul_inv_rev, inv_mul_cancel_right]
  simp_rw [h1, h2, ← integral_mul_const, ← integral_const_mul]
  have hswap := integral_integral_swap (μ := μ) (ν := μ)
    (f := fun y x => φ (g * x) * f (y⁻¹ * x) * h y) ?_
  · calc (∫ y, ∫ x, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ)
        = ∫ x, ∫ y, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ := hswap
      _ = ∫ z, ∫ y, φ (g * z) * (h y * f (y⁻¹ * z)) ∂μ ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun z => integral_congr_ae (ae_of_all _ fun y => ?_))
          simp only []
          ring
  · have hcont : Continuous (Function.uncurry fun y x : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        φ (g * x) * f (y⁻¹ * x) * h y) := by
      refine ((hφ.comp (continuous_const.mul continuous_snd)).mul
        (hfc.comp ((continuous_fst.inv).mul continuous_snd))).mul (hhc.comp continuous_fst)
    have hsupp : HasCompactSupport (Function.uncurry fun y x : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        φ (g * x) * f (y⁻¹ * x) * h y) := by
      refine HasCompactSupport.intro (hhs.prod (hhs.mul hfs)) ?_
      rintro ⟨y, x⟩ hyx
      simp only [Function.uncurry_apply_pair]
      by_cases hy : y ∈ tsupport h
      · have hfx : f (y⁻¹ * x) = 0 := by
          by_contra hne
          have hmem := Set.mul_mem_mul hy (subset_tsupport _ (Function.mem_support.mpr hne))
          rw [mul_inv_cancel_left] at hmem
          exact hyx ⟨hy, hmem⟩
        rw [hfx, mul_zero, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact hcont.integrable_of_hasCompactSupport hsupp

end AutomorphicForm
