/-
  The `L²`-continuity of right convolution.

  Right convolution `φ ↦ rightConv F φ f` is bounded in the `L²` seminorm and continuous in the group
  variable, uniformly over the `L²`-bounded automorphic functions. Three statements:

  * `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul`: the pointwise bound
    `‖rightConv K φ f g‖ ≤ ‖f‖₂ · ‖φ‖₂(restrict ((· * g) '' tsupport f))` — a Young/Hölder estimate on the
    support of `f`;
  * `exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain`:
    for `f` factorizable, a compact `Kc` and `ε > 0` there is a neighbourhood `V` of `1` such that
    `‖rightConv K φ f (g * h) - rightConv K φ f g‖ ≤ ε · ‖φ‖₂(Φ₀)` for `h ∈ V`, `g ∈ Kc` — uniform
    continuity of the convolution orbit, the input of `isCompactOperator_lift_rightConv_comp_cuspSubcarrier`;
  * `MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le`:
    the abstract lemma behind the covering step — an equicontinuous, pointwise bounded family on a tight
    finite measure space has a finite `ε`-dense subset in the `eLpNorm` distance.

  Transcribed from the pin's three `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`, 78 + 209
  + 139 lines). The third is generic (`MeasureTheory` namespace, no adelic content), and is homed here
  because this module is its only consumer.

  The 209 file's private support lemmas travel with it, at the pin's statements: the two uniform
  continuity estimates `EquiFD.exists_nhds_one_forall_mem_tsupport_norm_sub_lt` and
  `EquiFD.exists_nhds_one_forall_norm_comp_inv_mul_sub_le` (`S_…_of_isFundamentalDomain.lean:28,51`,
  both checker-`ok`), and `MeasureTheory.exists_forall_norm_le_of_equicontinuous_of_isCompact`
  (`S_MeasureTheory_…_le.lean:14`, checker-`ok`).

  **Deviation.** `EquiFD.eLpNorm_two_eq` (`S_…_of_isFundamentalDomain.lean:71`) is the one pin
  statement that is not ported verbatim, and it is `private` here. In mathlib `v4.34.0` `eLpNorm` is
  junk (`∞`) for a function that is not a.e. strongly measurable, so the pin's unconditional identity
  is false and the lemma needs `AEStronglyMeasurable φ ν`; the pin's proof body is unchanged apart
  from that argument. It is a helper of the 209 row, not one of the three headlines, and nothing
  public depends on its statement.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain.lean
  spec-pin: Theorems/Thm_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le.lean
  spec-pin: P2M/Sol/S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.LsXiBound
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm MeasureTheory
open IsDedekindDomain Filter
open scoped ENNReal Topology Pointwise
open scoped BoundedContinuousFunction

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace EquiFD

section UC

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {E : Type*} [SeminormedAddCommGroup E]

/-- Uniform continuity of the right translate, measured on the support of `f`. -/
theorem exists_nhds_one_forall_mem_tsupport_norm_sub_lt (f : G → E) (hf : Continuous f)
    (hfs : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 (1 : G), ∀ h ∈ V, ∀ z ∈ tsupport f, ‖f (h * z) - f z‖ < δ := by
  have hK : IsCompact (tsupport f) := hfs
  refine hK.induction_on (p := fun s => ∃ V ∈ 𝓝 (1 : G), ∀ h ∈ V, ∀ z ∈ s, ‖f (h * z) - f z‖ < δ)
    ⟨Set.univ, Filter.univ_mem, fun h _ z hz => hz.elim⟩
    (fun s t hst ht => by
      obtain ⟨V, hV, hVt⟩ := ht
      exact ⟨V, hV, fun h hh z hz => hVt h hh z (hst hz)⟩)
    (fun s t hs ht => by
      obtain ⟨V, hV, hVs⟩ := hs
      obtain ⟨V', hV', hVt⟩ := ht
      exact ⟨V ∩ V', Filter.inter_mem hV hV', fun h hh z hz => hz.elim (fun hz => hVs h hh.1 z hz)
        (fun hz => hVt h hh.2 z hz)⟩) ?_
  intro x _
  have hcont : Continuous fun p : G × G => f (p.1 * p.2) - f p.2 :=
    (hf.comp (continuous_fst.mul continuous_snd)).sub (hf.comp continuous_snd)
  have hmem : {p : G × G | ‖f (p.1 * p.2) - f p.2‖ < δ} ∈ 𝓝 ((1 : G), x) := by
    refine (hcont.norm.isOpen_preimage _ isOpen_Iio).mem_nhds ?_
    simp [hδ]
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp hmem
  exact ⟨W, mem_nhdsWithin_of_mem_nhds hW, U, hU, fun h hh z hz => hUW (Set.mk_mem_prod hh hz)⟩

/-- Uniform continuity of the translate `h⁻¹ * ·` on the whole space, one-sided. -/
theorem exists_nhds_one_forall_norm_comp_inv_mul_sub_le (f : G → E) (hf : Continuous f)
    (hfs : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 (1 : G), ∀ h ∈ V, ∀ y, ‖f (h⁻¹ * y) - f y‖ ≤ δ := by
  obtain ⟨V, hV, hVf⟩ := exists_nhds_one_forall_mem_tsupport_norm_sub_lt f hf hfs hδ
  refine ⟨V ∩ V⁻¹, Filter.inter_mem hV (inv_mem_nhds_one G hV), fun h hh y => ?_⟩
  have hzero : ∀ w, w ∉ tsupport f → f w = 0 := fun w hw =>
    Classical.not_not.mp fun hne => hw (subset_tsupport f (Function.mem_support.mpr hne))
  by_cases hy : y ∈ tsupport f
  · have := hVf h⁻¹ hh.2 y hy
    exact this.le
  · by_cases hy' : h⁻¹ * y ∈ tsupport f
    · have := hVf h hh.1 (h⁻¹ * y) hy'
      rw [mul_inv_cancel_left] at this
      rw [norm_sub_rev]
      exact this.le
    · rw [hzero y hy, hzero _ hy', sub_zero, norm_zero]
      exact hδ.le

end UC

/-- The `L²` seminorm as a `lintegral` of the squared norm, at the exponent `2`. -/
private theorem eLpNorm_two_eq {X : Type*} [MeasurableSpace X] (φ : X → ℂ) (ν : Measure X)
    (hφ : AEStronglyMeasurable φ ν) :
    eLpNorm φ 2 ν = (∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hφ,
    ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rfl

end EquiFD

namespace AutomorphicForm

theorem norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    ‖rightConv K φ f g‖ ≤
      (eLpNorm f 2 (adelicGLHaar (Fin 2) (𝓞 K) K)).toReal *
        (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict ((fun x => g * x) '' tsupport f))).toReal :=
by
  have hBS := borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hHM := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set T := tsupport f with hT
  have hTc : IsCompact T := hfs
  let F : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ := fun x => ‖φ (g * x)‖
  let G : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ := fun x => ‖f x‖
  have hφg : Continuous fun x => φ (g * x) := hφ.comp (continuous_const.mul continuous_id)
  have hFc : Continuous F := continuous_norm.comp hφg
  have hGc : Continuous G := continuous_norm.comp hf
  have hF2 : MemLp F (ENNReal.ofReal 2) (μ.restrict T) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hFc.aestronglyMeasurable).mpr ?_
    exact (hFc.pow 2).continuousOn.integrableOn_compact hTc
  have hG2 : MemLp G (ENNReal.ofReal 2) (μ.restrict T) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hGc.aestronglyMeasurable).mpr ?_
    exact (hGc.pow 2).continuousOn.integrableOn_compact hTc
  have h1 : ‖rightConv K φ f g‖ ≤ ∫ x in T, F x * G x ∂μ := by
    rw [rightConv_apply]
    show ‖∫ x, φ (g * x) * f x ∂μ‖ ≤ _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact norm_mul _ _
  have h2 : ∫ x in T, F x * G x ∂μ
      ≤ (∫ x in T, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ x in T, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hF2 hG2
  have hGint : (∫ x in T, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = (eLpNorm f 2 μ).toReal := by
    have hmem : MemLp f 2 μ := hf.memLp_of_hasCompactSupport hfs
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _),
      ENNReal.toReal_ofNat, ← one_div]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (fun x hx => by
      show ‖f x‖ ^ (2 : ℝ) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, Real.zero_rpow two_ne_zero])]
  have hFint : (∫ x in T, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      = (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' T))).toReal := by
    have hmp : MeasurePreserving (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) => g * x) μ μ :=
      measurePreserving_mul_left μ g
    have hemb : MeasurableEmbedding (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) => g * x) :=
      (Homeomorph.mulLeft g).measurableEmbedding
    have hcv : ∫ y in (fun x => g * x) '' T, ‖φ y‖ ^ (2 : ℝ) ∂μ = ∫ x in T, F x ^ (2 : ℝ) ∂μ :=
      hmp.setIntegral_image_emb hemb (fun y => ‖φ y‖ ^ (2 : ℝ)) T
    have hTc' : IsCompact ((fun x => g * x) '' T) := hTc.image (continuous_const.mul continuous_id)
    have hmem : MemLp φ 2 (μ.restrict ((fun x => g * x) '' T)) := by
      refine (memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable).mpr ?_
      exact ((continuous_norm.comp hφ).pow 2).continuousOn.integrableOn_compact hTc'
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _),
      ENNReal.toReal_ofNat, ← one_div, hcv]
  calc ‖rightConv K φ f g‖ ≤ ∫ x in T, F x * G x ∂μ := h1
    _ ≤ (∫ x in T, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ x in T, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := h2
    _ = (eLpNorm f 2 μ).toReal * (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' T))).toReal := by
        rw [hFint, hGint, mul_comm]


theorem exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    {Kc : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hKc : IsCompact Kc)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
          ∀ g ∈ Kc, ∀ h ∈ V,
            ‖rightConv K φ f (g * h) - rightConv K φ f g‖ ≤
              ε * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf

  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 K) K)
  have h1V₀ : (1 : AdelicGL2 (𝓞 K) K) ∈ V₀ := mem_of_mem_nhds hV₀
  set S₀ : Set (AdelicGL2 (𝓞 K) K) := tsupport f with hS₀
  have hS₀c : IsCompact S₀ := hfs
  set S' : Set (AdelicGL2 (𝓞 K) K) := V₀ * S₀ with hS'
  have hS'c : IsCompact S' := hV₀c.mul hS₀c
  have hS'cl : IsClosed S' := hS'c.isClosed
  have hS'm : MeasurableSet S' := hS'cl.measurableSet
  have hS₀S' : S₀ ⊆ S' := fun z hz => ⟨1, h1V₀, z, hz, one_mul z⟩
  set R : Set (AdelicGL2 (𝓞 K) K) := Kc * S' with hR
  have hRc : IsCompact R := hKc.mul hS'c

  obtain ⟨N, hN⟩ :=
    AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
      K χ hRc α β hβ hαβ Φ₀ hΦ₀

  set aE : ℝ≥0∞ := μ S' ^ (2 : ℝ≥0∞).toReal⁻¹ with haE
  have haE_top : aE ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hS'c.measure_lt_top.ne
  set a : ℝ := aE.toReal with ha
  set bE : ℝ≥0∞ := ENNReal.ofReal N ^ (1 / 2 : ℝ) with hbE
  have hbE_top : bE ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  set b : ℝ := bE.toReal with hb
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (a * b + 1) with hδ
  have hab1 : 0 < a * b + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hε hab1

  obtain ⟨V₁, hV₁, hV₁f⟩ := EquiFD.exists_nhds_one_forall_norm_comp_inv_mul_sub_le f hfc hfs hδ0
  refine ⟨V₀ ∩ V₁, Filter.inter_mem hV₀ hV₁, fun φ hls hcont hmem g hg h hh => ?_⟩

  set fh : AdelicGL2 (𝓞 K) K → ℂ := fun y => f (h⁻¹ * y) with hfh
  have hfh_cont : Continuous fh := hfc.comp (continuous_const_mul h⁻¹)
  have hfh_supp : HasCompactSupport fh := hfs.comp_homeomorph (Homeomorph.mulLeft h⁻¹)
  set k : AdelicGL2 (𝓞 K) K → ℂ := fh - f with hk
  have hk_cont : Continuous k := hfh_cont.sub hfc
  have hk_supp : HasCompactSupport k := hfh_supp.sub hfs
  have hk_zero : ∀ y, y ∉ S' → k y = 0 := by
    intro y hy
    have hzero : ∀ w, w ∉ S₀ → f w = 0 := fun w hw =>
      Classical.not_not.mp fun hne => hw (subset_tsupport f (Function.mem_support.mpr hne))
    have hy₀ : y ∉ S₀ := fun hy₀ => hy (hS₀S' hy₀)
    have hy₁ : h⁻¹ * y ∉ S₀ := fun hy₁ => hy ⟨h, hh.1, h⁻¹ * y, hy₁, mul_inv_cancel_left h y⟩
    show f (h⁻¹ * y) - f y = 0
    rw [hzero _ hy₁, hzero _ hy₀, sub_zero]
  have hk_bound : ∀ y, ‖k y‖ ≤ δ := fun y => hV₁f h hh.2 y
  have htsupp_k : tsupport k ⊆ S' :=
    closure_minimal (fun y hy => Classical.not_not.mp fun hy' => hy (hk_zero y hy')) hS'cl

  have hstep1 : rightConv K φ f (g * h) = rightConv K φ fh g := by
    show ∫ x, φ (g * h * x) * f x ∂μ = ∫ y, φ (g * y) * f (h⁻¹ * y) ∂μ
    rw [← integral_mul_left_eq_self (fun y => φ (g * y) * f (h⁻¹ * y)) h]
    simp only [mul_assoc, inv_mul_cancel_left]

  have hint : ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, Continuous ψ → HasCompactSupport ψ →
      Integrable (fun y => φ (g * y) * ψ y) μ := fun ψ hψ hψs =>
    ((hcont.comp (continuous_const_mul g)).mul hψ).integrable_of_hasCompactSupport hψs.mul_left
  have hstep2 : rightConv K φ f (g * h) - rightConv K φ f g = rightConv K φ k g := by
    rw [hstep1]
    show (∫ y, φ (g * y) * fh y ∂μ) - (∫ y, φ (g * y) * f y ∂μ) = ∫ y, φ (g * y) * k y ∂μ
    rw [← integral_sub (hint fh hfh_cont hfh_supp) (hint f hfc hfs)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (g * y) * fh y - φ (g * y) * f y = φ (g * y) * (fh - f) y
    rw [Pi.sub_apply, mul_sub]

  have hCS := norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul K φ k hcont hk_cont hk_supp g

  have hk4 : (eLpNorm k 2 μ).toReal ≤ a * δ := by
    have hind : k = S'.indicator k := by
      funext y; by_cases hy : y ∈ S'
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hk_zero y hy]
    have h1 : eLpNorm k 2 μ ≤ aE * ENNReal.ofReal δ := by
      rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict hS'm]
      refine (eLpNorm_le_of_ae_bound (C := δ)
        (hk_cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall hk_bound)).trans ?_
      rw [Measure.restrict_apply_univ]
    have h2 : aE * ENNReal.ofReal δ ≠ ⊤ := ENNReal.mul_ne_top haE_top ENNReal.ofReal_ne_top
    calc (eLpNorm k 2 μ).toReal ≤ (aE * ENNReal.ofReal δ).toReal := ENNReal.toReal_mono h2 h1
      _ = a * δ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0.le]

  have hk5 : (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' tsupport k))).toReal ≤
      b * (eLpNorm φ 2 (μ.restrict Φ₀)).toReal := by
    have hsub : (fun x => g * x) '' tsupport k ⊆ R := by
      rintro _ ⟨y, hy, rfl⟩
      exact Set.mul_mem_mul hg (htsupp_k hy)
    have h1 : eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' tsupport k)) ≤ eLpNorm φ 2 (μ.restrict R) :=
      eLpNorm_mono_measure φ (Measure.restrict_mono hsub le_rfl)
    have h2 : eLpNorm φ 2 (μ.restrict R) ≤ bE * eLpNorm φ 2 (μ.restrict Φ₀) := by
      rw [EquiFD.eLpNorm_two_eq φ _ hcont.aestronglyMeasurable,
        EquiFD.eLpNorm_two_eq φ _ hcont.aestronglyMeasurable, hbE,
        ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact ENNReal.rpow_le_rpow (hN φ hls hcont) (by norm_num)
    have h3 : bE * eLpNorm φ 2 (μ.restrict Φ₀) ≠ ⊤ := ENNReal.mul_ne_top hbE_top hmem.eLpNorm_ne_top
    calc (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' tsupport k))).toReal
        ≤ (bE * eLpNorm φ 2 (μ.restrict Φ₀)).toReal := ENNReal.toReal_mono h3 (h1.trans h2)
      _ = b * (eLpNorm φ 2 (μ.restrict Φ₀)).toReal := by rw [ENNReal.toReal_mul]

  set E₀ : ℝ := (eLpNorm φ 2 (μ.restrict Φ₀)).toReal with hE₀
  have hE₀0 : 0 ≤ E₀ := ENNReal.toReal_nonneg
  rw [hstep2]
  calc ‖rightConv K φ k g‖
      ≤ (eLpNorm k 2 μ).toReal * (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' tsupport k))).toReal := hCS
    _ ≤ (a * δ) * (b * E₀) := mul_le_mul hk4 hk5 ENNReal.toReal_nonneg (by positivity)
    _ = (a * b / (a * b + 1)) * (ε * E₀) := by rw [hδ]; field_simp
    _ ≤ 1 * (ε * E₀) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_one hab1]; linarith
    _ = ε * E₀ := one_mul _


end AutomorphicForm

namespace MeasureTheory

/-- A compact set carries a uniform bound for a pointwise bounded equicontinuous family. -/
theorem exists_forall_norm_le_of_equicontinuous_of_isCompact
    {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E] {ι : Type*}
    (u : ι → X → E) (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ i, ∀ x ∈ K, ‖u i x‖ ≤ B := by
  refine hK.induction_on (p := fun s => ∃ B : ℝ, ∀ i, ∀ x ∈ s, ‖u i x‖ ≤ B)
    ⟨0, fun i x hx => hx.elim⟩
    (fun s t hst h => by obtain ⟨B, hB⟩ := h; exact ⟨B, fun i x hx => hB i x (hst hx)⟩)
    (fun s t h h' => by
      obtain ⟨B, hB⟩ := h; obtain ⟨B', hB'⟩ := h'
      exact ⟨max B B', fun i x hx => hx.elim (fun h => (hB i x h).trans (le_max_left _ _))
        (fun h => (hB' i x h).trans (le_max_right _ _))⟩) ?_
  intro x _
  obtain ⟨C₀, hC₀⟩ := hpt x
  have h1 : ∀ᶠ y in 𝓝 x, ∀ i, dist (u i x) (u i y) < 1 :=
    Metric.equicontinuousAt_iff_right.mp (hequi x) 1 one_pos
  refine ⟨{y | ∀ i, dist (u i x) (u i y) < 1}, mem_nhdsWithin_of_mem_nhds h1, C₀ + 1, fun i y hy => ?_⟩
  have hyi := hy i
  rw [dist_eq_norm] at hyi
  exact (norm_le_insert (u i x) (u i y)).trans (add_le_add (hC₀ i) hyi.le)

theorem exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {ι : Type*} (u : ι → X → E) (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ∞)
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ K : Set X, IsCompact K ∧ μ Kᶜ < η)
    (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀)
    (C : ℝ) (hbound : ∀ i, ∀ᵐ x ∂μ, ‖u i x‖ ≤ C)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ i, ∃ j ∈ s, eLpNorm (u i - u j) p μ < ε := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => (hι.false i).elim⟩
  inhabit ι
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  set q : ℝ := p.toReal with hq
  have hp0 : p ≠ 0 := (one_pos.trans_le hp₁).ne'
  have hq_pos : 0 < q := ENNReal.toReal_pos hp0 hp

  obtain ⟨n, hn_pos, hn⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt (a := ENNReal.ofReal (C + C)) ENNReal.ofReal_ne_top hε2
  obtain ⟨K, hK, hμK⟩ := htight ((n : ℝ≥0∞) ^ q)
    (ENNReal.rpow_pos_of_nonneg (ENNReal.coe_pos.2 hn_pos) hq_pos.le)
  have hKm : MeasurableSet K := hK.measurableSet

  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_equicontinuous_of_isCompact u hequi hpt hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let v : ι → (K →ᵇ E) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x : K => u i x, (hequi.continuous i).comp continuous_subtype_val⟩
  have hv : ∀ i (x : K), v i x = u i x := fun i x => rfl
  have hequiK : Equicontinuous (fun i => ⇑(v i)) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro δ hδ
    have h := Metric.equicontinuousAt_iff_right.mp (hequi (x₀ : X)) δ hδ
    rw [nhds_subtype]
    exact (h.comap Subtype.val).mono fun y hy i => hy i
  set A : Set (K →ᵇ E) := Set.range v with hA
  have hA_equi : Equicontinuous (fun a : A => ⇑(a : K →ᵇ E)) := by
    have : (fun a : A => ⇑(a : K →ᵇ E)) = (fun i => ⇑(v i)) ∘ (fun a : A => a.2.choose) := by
      funext a; simp only [Function.comp_apply]; rw [a.2.choose_spec]
    rw [this]; exact hequiK.comp _
  have hA_cpt : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : E) B) (isCompact_closedBall 0 B) A
      (fun g x hg => by
        obtain ⟨i, rfl⟩ := hg
        rw [Metric.mem_closedBall, dist_zero_right, hv]
        exact hB i x x.2)
      hA_equi
  have hA_tb : TotallyBounded A := hA_cpt.totallyBounded.subset subset_closure

  obtain ⟨d, hd_pos, hd⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := μ Set.univ ^ q⁻¹)
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hq_pos.le) (measure_ne_top μ Set.univ)) hε2
  obtain ⟨t, htA, htfin, hAt⟩ := Metric.finite_approx_of_totallyBounded hA_tb d (NNReal.coe_pos.2 hd_pos)
  let inv : (K →ᵇ E) → ι := Function.invFun v
  have hinv : ∀ y ∈ A, v (inv y) = y := fun y hy => Function.invFun_eq hy
  refine ⟨htfin.toFinset.image inv, fun i => ?_⟩
  obtain ⟨y, hyt, hiy⟩ := Set.mem_iUnion₂.mp (hAt ⟨i, rfl⟩)
  refine ⟨inv y, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hyt), ?_⟩
  have hvj : v (inv y) = y := hinv y (htA hyt)
  have hdist : ∀ x ∈ K, ‖u i x - u (inv y) x‖ ≤ d := fun x hx => by
    rw [← dist_eq_norm, ← hv i ⟨x, hx⟩, ← hv (inv y) ⟨x, hx⟩]
    refine (BoundedContinuousFunction.dist_coe_le_dist _).trans ?_
    rw [hvj]
    exact (Metric.mem_ball.1 hiy).le

  have hmeas : ∀ k, AEStronglyMeasurable (u k) μ := fun k => (hequi.continuous k).aestronglyMeasurable
  set g : X → E := u i - u (inv y) with hg
  have hgm : AEStronglyMeasurable g (μ.restrict K) :=
    (hmeas i).sub (hmeas (inv y)) |>.mono_measure Measure.restrict_le_self
  have hgm' : AEStronglyMeasurable g (μ.restrict Kᶜ) :=
    (hmeas i).sub (hmeas (inv y)) |>.mono_measure Measure.restrict_le_self
  have h1 : eLpNorm (K.indicator g) p μ ≤ μ Set.univ ^ q⁻¹ * ENNReal.ofReal d := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hKm]
    refine (eLpNorm_le_of_ae_bound hgm (C := (d : ℝ)) ?_).trans ?_
    · rw [ae_restrict_iff' hKm]
      exact Filter.Eventually.of_forall fun x hx => hdist x hx
    · rw [Measure.restrict_apply_univ]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow (measure_mono (Set.subset_univ K))
        (inv_nonneg.2 hq_pos.le)) _
  have h2 : eLpNorm (Kᶜ.indicator g) p μ ≤ μ Kᶜ ^ q⁻¹ * ENNReal.ofReal (C + C) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hKm.compl]
    refine (eLpNorm_le_of_ae_bound hgm' (C := C + C) ?_).trans (by rw [Measure.restrict_apply_univ])
    refine ae_restrict_of_ae ?_
    filter_upwards [hbound i, hbound (inv y)] with x hxi hxj
    exact (norm_sub_le _ _).trans (add_le_add hxi hxj)
  have hsum : eLpNorm g p μ ≤ eLpNorm (K.indicator g) p μ + eLpNorm (Kᶜ.indicator g) p μ := by
    have h := eLpNorm_add_le (f := K.indicator g) (g := Kᶜ.indicator g) (μ := μ) hp₁
    rwa [Set.indicator_self_add_compl] at h
  have hlt1 : μ Set.univ ^ q⁻¹ * ENNReal.ofReal d < ε / 2 := by
    rw [ENNReal.ofReal_coe_nnreal, mul_comm]; exact hd
  have hlt2 : μ Kᶜ ^ q⁻¹ * ENNReal.ofReal (C + C) < ε / 2 := by
    refine lt_of_le_of_lt (mul_le_mul_left ?_ _) hn
    calc μ Kᶜ ^ q⁻¹ ≤ ((n : ℝ≥0∞) ^ q) ^ q⁻¹ := ENNReal.rpow_le_rpow hμK.le (inv_nonneg.2 hq_pos.le)
      _ = n := ENNReal.rpow_rpow_inv hq_pos.ne' _
  calc eLpNorm (u i - u (inv y)) p μ = eLpNorm g p μ := rfl
    _ ≤ eLpNorm (K.indicator g) p μ + eLpNorm (Kᶜ.indicator g) p μ := hsum
    _ ≤ μ Set.univ ^ q⁻¹ * ENNReal.ofReal d + μ Kᶜ ^ q⁻¹ * ENNReal.ofReal (C + C) := add_le_add h1 h2
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hlt1 hlt2
    _ = ε := ENNReal.add_halves ε

end MeasureTheory
