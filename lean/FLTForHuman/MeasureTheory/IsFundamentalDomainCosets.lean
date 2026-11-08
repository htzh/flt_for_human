/-
  Fundamental domains from left-coset representatives of a subgroup.

  Given `Γ₂ ≤ Γ₁ ≤ G` acting on `X`, a fundamental domain `𝓕` for `Γ₁` and a complete set of
  representatives `R : ι → Γ₁` of the left cosets of `Γ₂` in `Γ₁` (`∀ γ, ∃! i, (R i)⁻¹ * γ ∈ Γ₂`),
  the union `⋃ i, (R i)⁻¹ • 𝓕` is a fundamental domain for `Γ₂`
  (`iUnion_inv_smul_of_leftCosetRepresentatives`), and integration over it unfolds into a sum over
  the representatives against the `Γ₂`-measure:

  `∫⁻ x in ⋃ i, R i⁻¹ • 𝓕, f x = ∫⁻ x in 𝓕, ∑' i, f (R i⁻¹ • x)`,

  together with the integrability statement it needs for an `E`-valued `h` (a.e. summability and
  `∫ = ∫ ∑'`). This is the "sum over the units" step of the quotient-measure comparisons: the
  quotient of `GL₂(𝔸_K)` by the rational centre-unipotent subgroup is reached from the quotient by
  the torus-unipotent one by summing over `Kˣ`, and that is a sum over coset representatives.

  Assumes: mathlib `v4.34.0`. Mathlib's `MeasureTheory/Group/FundamentalDomain.lean` has
  `IsFundamentalDomain.smul`, `image_of_equiv`, `lIntegral_eq_tsum`, `setIntegral_eq_tsum` and the
  `quotientMeasure` API — measured 2026-11-07: there is no `IsFundamentalDomain.image` and no
  `IsFundamentalDomain.union` in it — but no statement about a subgroup's coset representatives;
  checked `rg "IsFundamentalDomain.*Subgroup|leftCosetRepresentatives|CosetRepresentative"
  Mathlib/MeasureTheory/Group/FundamentalDomain.lean` on 2026-11-07. The pin's namespace is kept.

  Transcribed whole from the pin's two `S_` files and their `Theorems/` wrappers (pinned
  `aa2d8b3`, 77 + 99 lines, 3 + 4 declarations).
  spec-pin: Theorems/Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives.lean
  spec-pin: P2M/Sol/S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives.lean
  spec-pin: Theorems/Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives.lean
  spec-pin: P2M/Sol/S_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives.lean
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace MeasureTheory.IsFundamentalDomain

/-! ### The pin's generic helpers

The pin's `RS11C1` / `RS11C1B` blocks, with the generated namespace label dropped; the two blocks'
copies of `subgroup_smul_set` are one declaration here. -/

section SubgroupAction

variable {G X ι : Type*} [Group G] [MulAction G X]

theorem subgroup_smul_set (Γ : Subgroup G) (γ : Γ) (s : Set X) : γ • s = (γ : G) • s := rfl

theorem smul_iUnion_inv_smul (Γ : Subgroup G) (R : ι → Γ) (g : G) (s : Set X) :
    g • (⋃ i, ((R i : G)⁻¹) • s) = ⋃ i, (g * (R i : G)⁻¹) • s := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i => ?_
  rw [smul_smul]

end SubgroupAction

section MeasurePreservingSmul

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [MeasurableSpace G]
  [MeasurableSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ]

theorem setLIntegral_smul_set (g : G) (s : Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in g • s, f x ∂μ = ∫⁻ x in s, f (g • x) ∂μ := by
  have he : MeasurePreserving (MeasurableEquiv.smul g : X ≃ᵐ X) μ μ := measurePreserving_smul g μ
  rw [← he.setLIntegral_comp_preimage_emb (MeasurableEquiv.smul g).measurableEmbedding]
  congr 1
  show μ.restrict ((fun x => g • x) ⁻¹' (g • s)) = μ.restrict s
  rw [Set.preimage_smul, inv_smul_smul]

theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : G) (s : Set X) (f : X → E) :
    ∫ x in g • s, f x ∂μ = ∫ x in s, f (g • x) ∂μ := by
  have he : MeasurePreserving (MeasurableEquiv.smul g : X ≃ᵐ X) μ μ := measurePreserving_smul g μ
  rw [← he.setIntegral_preimage_emb (MeasurableEquiv.smul g).measurableEmbedding]
  congr 1
  show μ.restrict ((fun x => g • x) ⁻¹' (g • s)) = μ.restrict s
  rw [Set.preimage_smul, inv_smul_smul]

end MeasurePreservingSmul

/-- A fundamental domain for `Γ₁`, cut into the left cosets of `Γ₂ ≤ Γ₁`, gives one for `Γ₂`. -/
theorem iUnion_inv_smul_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    refine NullMeasurableSet.iUnion fun i => ?_
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [subgroup_smul_set, Subgroup.coe_inv] at h
  ·
    filter_upwards [h𝓕.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨i, hi, -⟩ := hR γ
    refine ⟨⟨(R i : G)⁻¹ * γ, hi⟩, ?_⟩
    rw [Subgroup.smul_def]
    show ((R i : G)⁻¹ * (γ : G)) • x ∈ ⋃ i, ((R i : G)⁻¹) • 𝓕
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set (by rw [← Subgroup.smul_def]; exact hγ)
  ·
    intro γ γ' hne
    change AEDisjoint μ (γ • ⋃ i, ((R i : G)⁻¹) • 𝓕) (γ' • ⋃ i, ((R i : G)⁻¹) • 𝓕)
    rw [subgroup_smul_set, subgroup_smul_set, smul_iUnion_inv_smul Γ₁ R,
      smul_iUnion_inv_smul Γ₁ R, AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j

    have hγ₁ : ((γ : G) * (R i : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ.2) (inv_mem (R i).2)
    have hγ₁' : ((γ' : G) * (R j : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ'.2) (inv_mem (R j).2)
    have hne' : (⟨(γ : G) * (R i : G)⁻¹, hγ₁⟩ : Γ₁) ≠ ⟨(γ' : G) * (R j : G)⁻¹, hγ₁'⟩ := by
      intro heq
      have heq' : (γ : G) * (R i : G)⁻¹ = (γ' : G) * (R j : G)⁻¹ := congrArg Subtype.val heq

      have hmem : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by
        have : ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * (γ : G) := by
          calc ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * ((γ' : G) * (R j : G)⁻¹) * (R i : G) := by group
            _ = (γ' : G)⁻¹ * ((γ : G) * (R i : G)⁻¹) * (R i : G) := by rw [heq']
            _ = (γ' : G)⁻¹ * (γ : G) := by group
        rw [Subgroup.coe_inv, this]
        exact mul_mem (inv_mem γ'.2) γ.2
      have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
      obtain ⟨k, -, hk⟩ := hR (R i)
      have hij : i = j := (hk i hii).trans (hk j hmem).symm
      subst hij
      apply hne
      apply Subtype.ext
      exact mul_right_cancel heq'
    have h := h𝓕.aedisjoint hne'
    simpa only [Function.onFun, subgroup_smul_set] using h

/-- Integration over that cut-up fundamental domain is the sum over the representatives, and the
corresponding real-valued statement: integrability, a.e. summability, and `∫ = ∫ ∑'`. -/
theorem setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    (∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, f x ∂μ = ∫⁻ x in 𝓕, ∑' i, f ((R i : G)⁻¹ • x) ∂μ) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (h : X → E),
      AEStronglyMeasurable h μ →
      ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ < ∞ →
      IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun i => ‖h ((R i : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, h x ∂μ = ∫ x in 𝓕, ∑' i, h ((R i : G)⁻¹ • x) ∂μ := by
  classical
  -- The pin's binder block is frozen and carries `hle : Γ₂ ≤ Γ₁`, but nothing below needs the
  -- inclusion: the uniqueness in `hR` alone separates the translates. Record it once, at the only
  -- place it could act, so the hypothesis is referenced (`Γ₂`-membership promotes to `Γ₁`).
  have hmono : ∀ γ : Γ₂, (γ : G) ∈ Γ₁ := fun γ => hle γ.2

  have hnull : ∀ i, NullMeasurableSet (((R i : G)⁻¹) • 𝓕) μ := by
    intro i
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [subgroup_smul_set, Subgroup.coe_inv] at h
  have hdist : ∀ i j, i ≠ j → ((R i)⁻¹ : Γ₁) ≠ (R j)⁻¹ := by
    intro i j hij heq
    apply hij
    have hRi : R i = R j := inv_injective heq
    obtain ⟨k, -, hk⟩ := hR (R i)
    have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
    have hji : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by rw [← hRi, Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
    exact (hk i hii).trans (hk j hji).symm
  have hdisj : Pairwise fun i j => AEDisjoint μ (((R i : G)⁻¹) • 𝓕) (((R j : G)⁻¹) • 𝓕) := by
    intro i j hij
    have h := h𝓕.aedisjoint (hdist i j hij)
    simpa only [Function.onFun, subgroup_smul_set, Subgroup.coe_inv] using h
  have hmp : ∀ i, MeasurePreserving (fun x : X => (R i : G)⁻¹ • x) μ μ := fun i =>
    measurePreserving_smul _ μ
  refine ⟨fun f hf => ?_, ?_⟩
  ·
    have hfm : ∀ i, AEMeasurable (fun x => f ((R i : G)⁻¹ • x)) (μ.restrict 𝓕) := fun i =>
      ((hf.comp (measurable_const_smul ((R i : G)⁻¹)) : Measurable fun x => f ((R i : G)⁻¹ • x))).aemeasurable
    rw [lintegral_iUnion₀ hnull hdisj, lintegral_tsum hfm]
    exact tsum_congr fun i => setLIntegral_smul_set μ _ _ _
  · intro E _ _ _ h hh hfin
    have hae : ∀ i, AEStronglyMeasurable (fun x => h ((R i : G)⁻¹ • x)) (μ.restrict 𝓕) := fun i =>
      (hh.comp_measurePreserving (hmp i)).restrict

    have hnorm : ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, ‖h x‖ₑ ∂μ = ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ := by
      rw [lintegral_iUnion₀ hnull hdisj, lintegral_tsum fun i => (hae i).enorm]
      exact tsum_congr fun i => setLIntegral_smul_set μ _ _ _
    have hint : IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ :=
      ⟨hh.restrict, by rw [HasFiniteIntegral, hnorm]; exact hfin⟩
    refine ⟨hint, ?_, ?_⟩
    ·
      have hmeas : AEMeasurable (fun x => ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ) (μ.restrict 𝓕) := by
        simp only [ENNReal.tsum_eq_iSup_sum]
        exact .iSup fun s => Finset.aemeasurable_fun_sum s fun i _ => (hae i).enorm
      have hlt : ∀ᵐ x ∂μ.restrict 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ < ∞ :=
        ae_lt_top' hmeas hfin.ne
      filter_upwards [hlt] with x hx
      exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne
    ·
      rw [integral_iUnion_ae hnull hdisj hint]
      have hfin' : ∑' i, ∫⁻ x, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ.restrict 𝓕 ≠ ∞ := by
        rw [← lintegral_tsum fun i => (hae i).enorm]
        exact hfin.ne
      rw [integral_tsum hae hfin']
      exact tsum_congr fun i => setIntegral_smul_set μ _ _ _

end MeasureTheory.IsFundamentalDomain

end
