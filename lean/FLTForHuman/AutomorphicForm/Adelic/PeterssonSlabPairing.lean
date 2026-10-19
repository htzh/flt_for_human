/-
  The weighted-Petersson pairing (listed, tier 1).

  The shared proof body behind the pin ready node
  `AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain`
  (node 6896): covariance of `peterssonIntegral` under the right regular action on the span
  of the translates of a realisation, non-degeneracy of `peterssonIntegral F s S R'.toFun R'.toFun`,
  and the packaging of `peterssonIntegral` as a genuine sesquilinear form on
  `trSpan R.toFun ⊔ trSpan R'.toFun` against `trSpan R'.toFun`, together with the
  central-character-twisted covariance (`hcovW`) and the span construction.

  The pin `S_` file transcribes in three pieces, all here: the generic measure-theory
  prelude `FundamentalDomainSlab` (pin lines 24–375); the adelic vocabulary (pin lines
  377–974); the engine `main` (pin line 844) public; and the headline itself, stated
  verbatim from the pin `Theorems/` wrapper and proved by `main`, to which the SC1
  covering (`AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre`) is
  supplied — exactly as the pin's `solution` does. The module is listed, so the checker
  verifies the headline against the wrapper and `main` against the pin's private `main`
  through the dotted fallback.

  **Shared centre-cut prelude (tier 3).** The same prelude is the shared home of the three
  centre-cut fundamental-domain nodes: `DetNormSlab.lean` (automorphy transfer, 325 pin
  lines) and the two `MeasurableFundamentalDomainCover.lean` twins (267/266). The
  declarations they name are public here with `-- pin:` markers into the three S files
  (`setLIntegral_fd_le_of_cover`, `smulInvariantMeasure_restrict`,
  `aestronglyMeasurable_of_cover_translates`, `setLIntegral_biUnion_translates_le`,
  `memLp_two_of_lintegral`, `lintegral_lt_top_of_memLp_two`,
  `exists_measurableSet_isFundamentalDomain_subset`, `setLIntegral_fd_le_sum_mul`,
  `cover_of_forall`, `dn`, `slab`, `μH`, `Γp`, the `dn_*` lemmas,
  `subtype_mul_mem_slab`, `measurableSet_slab`, `preimage_subtype_mul_slab`,
  `smulInvariantMeasure_slab`, `CoveredBy`, `coveredBy_of_forall`,
  `memLp_of_coveredBy`). The marker names a pin file `SOURCES` does not read, so the
  checker exempts them and `spec/UNWIRED-PUBLIC.md` registers them; the three façades are
  the only wired declarations. The rest of the prelude stays `private`.

  Reuse, do not re-prove: `NumberField.TateGlobal.exists_norm_pow_mult_eq`
  (`FLTForHuman/NumberTheory/NumberField/TateGlobal/ArchNorm.lean`). The pin's private copy
  has `r` implicit, so the pin call `exists_norm_pow_mult_eq v hr` becomes
  `exists_norm_pow_mult_eq v r hr` (and the landed lemma returns the nonzero conjunct the
  pin re-derived). `exists_norm_eq` is pin-`private`; it is re-derived `private` here. The
  already-homed definitions are stated, not re-derived: `peterssonIntegral`,
  `SmoothCuspRealizationAt`, `IsGenuineCuspRealizationAt`, `productionPinsOf`,
  `ideleNorm_det_globalPoints`, `ideleNorm`, `globalPoints`, `centreCutSiegelSet`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`);
  port mathlib `v4.34.0`.
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonIntegral
import FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabCoveringTheorems
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDet
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchNorm
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace FundamentalDomainSlab

open scoped Pointwise ENNReal

section FDAction

variable {H α : Type*} [Group H] [MulAction H α] [MeasurableSpace α] [MeasurableConstSMul H α]
  [Countable H] {ν : Measure α} [SMulInvariantMeasure H α ν]

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.setLIntegral_fd_le_of_cover (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:38)
theorem setLIntegral_fd_le_of_cover {S E : Set α} (hS : IsFundamentalDomain H S ν)
    (hcov : S ⊆ ⋃ γ : H, (γ • ·) ⁻¹' E) (F : α → ℝ≥0∞) (hF : ∀ (γ : H) (w : α), F (γ • w) = F w) :
    ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in E, F w ∂ν := by
  calc ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in ⋃ γ : H, S ∩ (γ • ·) ⁻¹' E, F w ∂ν := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (hcov hw)
        exact Set.mem_iUnion.mpr ⟨γ, hw, hγ⟩
    _ ≤ ∑' γ : H, ∫⁻ w in S ∩ (γ • ·) ⁻¹' E, F w ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : H, ∫⁻ w in γ • S ∩ E, F w ∂ν := by
        refine tsum_congr fun γ => ?_
        have hpre : (fun w : α => γ • w) ⁻¹' (γ • S ∩ E) = S ∩ (γ • ·) ⁻¹' E := by
          rw [Set.preimage_inter, Set.preimage_smul, inv_smul_smul]
        rw [← (measurePreserving_smul γ ν).setLIntegral_comp_preimage_emb
          (measurableEmbedding_const_smul γ) F (γ • S ∩ E), hpre]
        simp_rw [hF]
    _ = ∫⁻ w in E, F w ∂ν := by
        rw [hS.setLIntegral_eq_tsum F E]
        exact tsum_congr fun γ => by rw [Set.inter_comm]

private theorem exists_measure_smul_inter_ne_zero {S U : Set α} (hS : IsFundamentalDomain H S ν)
    (hU : ν U ≠ 0) : ∃ γ : H, ν (γ • U ∩ S) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hU ((hS.measure_eq_tsum U).trans (ENNReal.tsum_eq_zero.mpr h))

end FDAction

section Transfer

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  [Countable G] {ν : Measure α} [SMulInvariantMeasure G α ν]

-- pin: P2MW.S_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.exists_measurableSet_isFundamentalDomain_subset (P2M/Sol/S_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.lean:37)
theorem exists_measurableSet_isFundamentalDomain_subset {S T E : Set α}
    (hS : IsFundamentalDomain G S ν) (hST : S ⊆ T)
    (hE : MeasurableSet E) (hcov : ∀ x ∈ T, ∃ g : G, g • x ∈ E) :
    ∃ F : Set α, MeasurableSet F ∧ F ⊆ E ∧ IsFundamentalDomain G F ν := by
  classical

  set S₁ := fundamentalInterior G S with hS₁def
  have hS₁ : IsFundamentalDomain G S₁ ν := hS.fundamentalInterior
  have hS₁S : S₁ ⊆ S := fundamentalInterior_subset
  have hdisj₁ : Pairwise (Function.onFun Disjoint fun g : G => g • S₁) := pairwise_disjoint_fundamentalInterior G S
  obtain ⟨S₂, hS₂S₁, hS₂m, hS₂ae⟩ := hS₁.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hnull : ν (S₁ \ S₂) = 0 := (ae_eq_set.mp hS₂ae).2
  have hdisj₂ : ∀ g : G, g ≠ 1 → ∀ x ∈ S₂, g • x ∉ S₂ := by
    intro g hg x hx hgx
    have h := hdisj₁ hg
    rw [Function.onFun, one_smul] at h
    exact Set.disjoint_left.mp h (Set.smul_mem_smul_set (hS₂S₁ hx)) (hS₂S₁ hgx)

  obtain ⟨f, hf⟩ := Countable.exists_injective_nat G
  let Q : G → Set α := fun g => S₂ ∩ {x : α | g • x ∈ E} ∩ {x : α | ∀ g' : G, g' • x ∈ E → f g ≤ f g'}
  have hQm : ∀ g, MeasurableSet (Q g) := by
    intro g
    have h1 : MeasurableSet {x : α | g • x ∈ E} := (measurable_const_smul g) hE
    have h2 : MeasurableSet {x : α | ∀ g' : G, g' • x ∈ E → f g ≤ f g'} := by
      have : {x : α | ∀ g' : G, g' • x ∈ E → f g ≤ f g'} = ⋂ g' : G, ({x : α | g' • x ∈ E}ᶜ ∪ {_x | f g ≤ f g'}) := by
        ext x; simp [Set.mem_iInter, imp_iff_not_or]
      rw [this]
      exact MeasurableSet.iInter fun g' => ((measurable_const_smul g') hE).compl.union (MeasurableSet.const _)
    exact (hS₂m.inter h1).inter h2
  have hQdisj : ∀ g g' : G, ∀ x, x ∈ Q g → x ∈ Q g' → g = g' := by
    intro g g' x hx hx'
    exact hf (le_antisymm (hx.2 g' hx'.1.2) (hx'.2 g hx.1.2))
  have hQcov : ∀ x ∈ S₂, ∃ g, x ∈ Q g := by
    intro x hx
    have hxT : x ∈ T := hST (hS₁S (hS₂S₁ hx))
    have hne : ∃ n, ∃ g : G, g • x ∈ E ∧ f g = n := by
      obtain ⟨g, hg⟩ := hcov x hxT; exact ⟨f g, g, hg, rfl⟩
    obtain ⟨g, hgE, hgn⟩ := Nat.find_spec hne
    refine ⟨g, ⟨hx, hgE⟩, fun g' hg' => ?_⟩
    rw [hgn]
    exact Nat.find_min' hne ⟨g', hg', rfl⟩

  let F : Set α := ⋃ g : G, g • Q g
  have hFm : MeasurableSet F := MeasurableSet.iUnion fun g => (hQm g).const_smul g
  have hFE : F ⊆ E := by
    intro x hx
    obtain ⟨g, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hx
    exact hq.1.2

  have hFfree : ∀ x ∈ F, ∀ d : G, d ≠ 1 → d • x ∉ F := by
    intro x hx d hd hdx
    obtain ⟨g, hxg⟩ := Set.mem_iUnion.mp hx
    obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hxg
    obtain ⟨g', hxg'⟩ := Set.mem_iUnion.mp hdx
    obtain ⟨q', hq', hq'eq⟩ := Set.mem_smul_set.mp hxg'

    have hrel : q' = (g'⁻¹ * d * g) • q := by
      rw [mul_smul, mul_smul, ← hq'eq, inv_smul_smul]
    by_cases he : g'⁻¹ * d * g = 1
    · rw [he, one_smul] at hrel
      subst hrel
      have hgg' : g = g' := hQdisj g g' q' hq hq'
      subst hgg'
      apply hd
      have : d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      rw [this, he]; group
    · exact hdisj₂ _ he q hq.1.1 (hrel ▸ hq'.1.1)
  refine ⟨F, hFm, hFE, ⟨hFm.nullMeasurableSet, ?_, ?_⟩⟩
  ·
    have hbad : ∀ᵐ x ∂ν, ∀ g : G, g • x ∉ S₁ \ S₂ := by
      have : ν (⋃ g : G, (fun x => g • x) ⁻¹' (S₁ \ S₂)) = 0 := by
        refine measure_iUnion_null fun g => ?_
        rw [Set.preimage_smul]
        exact measure_smul_null hnull g⁻¹
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) this
      simp only [Set.mem_ofPred_eq, not_forall, not_not] at hx
      obtain ⟨g, hg⟩ := hx
      exact Set.mem_iUnion.mpr ⟨g, hg⟩
    filter_upwards [hS₁.ae_covers, hbad] with x hx hx'
    obtain ⟨g, hg⟩ := hx
    have hg₂ : g • x ∈ S₂ := by
      by_contra h; exact hx' g ⟨hg, h⟩
    obtain ⟨g₀, hg₀⟩ := hQcov _ hg₂
    exact ⟨g₀ * g, Set.mem_iUnion.mpr ⟨g₀, Set.mem_smul_set.mpr ⟨g • x, hg₀, (mul_smul g₀ g x).symm⟩⟩⟩
  ·
    intro g h hgh
    refine Disjoint.aedisjoint (Set.disjoint_left.mpr fun x hxg hxh => ?_)
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hxg
    obtain ⟨y', hy', hyy'⟩ := Set.mem_smul_set.mp hxh
    have : (g⁻¹ * h) • y' = y := by rw [mul_smul, hyy', inv_smul_smul]
    exact hFfree y' hy' (g⁻¹ * h) (fun h1 => hgh (inv_mul_eq_one.mp h1)) (this ▸ hy)
end Transfer

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.smulInvariantMeasure_restrict (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:63)
theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {T : Set G} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ G (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

variable [MeasurableMul G]

private theorem isFundamentalDomain_image_mul_right (Γ : Subgroup G) (μ : Measure G)
    [μ.IsMulRightInvariant] {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T))
    (g : G) (hTT' : (fun w : G => w * g⁻¹) ⁻¹' T = T') :
    IsFundamentalDomain ↥Γ ((fun w : G => w * g) '' S) (μ.restrict T') := by
  have hmp : MeasurePreserving (fun w : G => w * g⁻¹) (μ.restrict T') (μ.restrict T) := by
    rw [← hTT']
    exact (measurePreserving_mul_right μ g⁻¹).restrict_preimage_emb (measurableEmbedding_mulRight g⁻¹) T
  have h := hS.image_of_equiv (ν := μ.restrict T') (Equiv.mulRight g)
    (by simpa using hmp.quasiMeasurePreserving) (Equiv.refl _)
    (fun γ w => show (γ : G) * w * g = (γ : G) * (w * g) from mul_assoc _ _ _)
  simpa using h

private theorem isFundamentalDomain_image_mul_left (Γ : Subgroup G) (μ : Measure G)
    [μ.IsMulLeftInvariant] {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T))
    (z : G) (hz : ∀ γ : ↥Γ, z * (γ : G) = (γ : G) * z)
    (hTT' : (fun w : G => z⁻¹ * w) ⁻¹' T = T') :
    IsFundamentalDomain ↥Γ ((fun w : G => z * w) '' S) (μ.restrict T') := by
  have hmp : MeasurePreserving (fun w : G => z⁻¹ * w) (μ.restrict T') (μ.restrict T) := by
    rw [← hTT']
    exact (measurePreserving_mul_left μ z⁻¹).restrict_preimage_emb (measurableEmbedding_mulLeft z⁻¹) T
  have h := hS.image_of_equiv (ν := μ.restrict T') (Equiv.mulLeft z)
    (by simpa using hmp.quasiMeasurePreserving) (Equiv.refl _)
    (fun γ w => show z * ((γ : G) * w) = (γ : G) * (z * w) by rw [← mul_assoc, hz γ, mul_assoc])
  simpa using h

private theorem setIntegral_mul_right_eq_of_isFundamentalDomain
    (Γ : Subgroup G) [Countable ↥Γ] [MeasurableConstSMul ↥Γ G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [SMulInvariantMeasure ↥Γ G μ]
    {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T)) (hST : S ⊆ T)
    (g z : G) (hz : ∀ γ : ↥Γ, z * (γ : G) = (γ : G) * z)
    (hT' : MeasurableSet T') (hΓT' : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T' = T')
    (hgT : (fun w : G => w * g⁻¹) ⁻¹' T = T') (hzT : (fun w : G => z⁻¹ * w) ⁻¹' T = T')
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : G → E)
    (hΦΓ : ∀ (γ : ↥Γ) (w : G), Φ (γ • w) = Φ w) (hΦz : ∀ w, Φ (z * w) = Φ w) :
    ∫ w in S, Φ (w * g) ∂μ = ∫ w in S, Φ w ∂μ := by
  have : SMulInvariantMeasure ↥Γ G (μ.restrict T') := smulInvariantMeasure_restrict Γ μ hT' hΓT'
  have hFDg := isFundamentalDomain_image_mul_right Γ μ hS g hgT
  have hFDz := isFundamentalDomain_image_mul_left Γ μ hS z hz hzT
  have hSg : (fun w => w * g) '' S ⊆ T' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hgT]
    show w * g * g⁻¹ ∈ T
    rw [mul_inv_cancel_right]
    exact hST hw
  have hSz : (fun w => z * w) '' S ⊆ T' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hzT]
    show z⁻¹ * (z * w) ∈ T
    rw [inv_mul_cancel_left]
    exact hST hw
  calc ∫ w in S, Φ (w * g) ∂μ
      = ∫ w in (fun w => w * g) '' S, Φ w ∂μ :=
        ((measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) Φ S).symm
    _ = ∫ w in (fun w => w * g) '' S, Φ w ∂(μ.restrict T') := by
        rw [Measure.restrict_restrict_of_subset hSg]
    _ = ∫ w in (fun w => z * w) '' S, Φ w ∂(μ.restrict T') := hFDg.setIntegral_eq hFDz fun γ w => hΦΓ γ w
    _ = ∫ w in (fun w => z * w) '' S, Φ w ∂μ := by
        rw [Measure.restrict_restrict_of_subset hSz]
    _ = ∫ w in S, Φ (z * w) ∂μ :=
        (measurePreserving_mul_left μ z).setIntegral_image_emb (measurableEmbedding_mulLeft z) Φ S
    _ = ∫ w in S, Φ w ∂μ := by simp_rw [hΦz]

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.aestronglyMeasurable_of_cover_translates (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:74)
theorem aestronglyMeasurable_of_cover_translates (μ : Measure G) [μ.IsMulLeftInvariant]
    {D X : Set G} {f : G → ℂ} (hf : AEStronglyMeasurable f (μ.restrict D))
    {ι : Type*} [Countable ι] (a : ι → G) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (hfa : ∀ (i : ι) (w : G), f (a i * w) = c i * f w) (hX : X ⊆ ⋃ i, (fun w => a i * w) ⁻¹' D) :
    AEStronglyMeasurable f (μ.restrict X) := by
  have hpiece : ∀ i, AEStronglyMeasurable f (μ.restrict ((fun w => a i * w) ⁻¹' D)) := by
    intro i
    have hmp : MeasurePreserving (fun w => a i * w) (μ.restrict ((fun w => a i * w) ⁻¹' D))
        (μ.restrict D) :=
      (measurePreserving_mul_left μ (a i)).restrict_preimage_emb (measurableEmbedding_mulLeft (a i)) D
    have h1 : AEStronglyMeasurable (f ∘ fun w => a i * w) (μ.restrict ((fun w => a i * w) ⁻¹' D)) :=
      hf.comp_measurePreserving hmp
    have h2 : (fun w => (c i)⁻¹ * (f ∘ fun w => a i * w) w) = f := by
      funext w
      simp only [Function.comp_apply, hfa, ← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]
    rw [← h2]
    exact h1.const_mul _
  exact (AEStronglyMeasurable.iUnion hpiece).mono_measure (Measure.restrict_mono hX le_rfl)

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.setLIntegral_biUnion_translates_le (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:93)
theorem setLIntegral_biUnion_translates_le (μ : Measure G) [μ.IsMulLeftInvariant]
    {D : Set G} (F : G → ℝ≥0∞) {ι : Type*} (I : Finset ι) (b : ι → G) (k : ι → ℝ≥0∞)
    (hk : ∀ i, k i ≠ ∞) (hFb : ∀ (i : ι) (w : G), F (b i * w) = k i * F w) :
    ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ ≤ ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := by
  have hpiece : ∀ i, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ = k i * ∫⁻ w in D, F w ∂μ := by
    intro i
    rw [← (measurePreserving_mul_left μ (b i)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (b i)) F D]
    simp_rw [hFb]
    exact lintegral_const_mul' (k i) _ (hk i)
  calc ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ
      ≤ ∫⁻ w in ⋃ i : ↥I, (fun w => b i * w) '' D, F w ∂μ := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hw⟩
    _ ≤ ∑' i : ↥I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := by
        rw [tsum_fintype, Finset.sum_coe_sort I fun i => ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ]
    _ = ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := Finset.sum_congr rfl fun i _ => hpiece i

private theorem memLp_comp_mul_right (μ : Measure G) [μ.IsMulRightInvariant] {S : Set G}
    {f : G → ℂ} (h : G) (hf : MemLp f 2 (μ.restrict ((fun w => w * h) '' S))) :
    MemLp (fun z => f (z * h)) 2 (μ.restrict S) :=
  hf.comp_measurePreserving
    ((measurePreserving_mul_right μ h).restrict_image_emb (measurableEmbedding_mulRight h) S)

end Group

section Positivity

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [BorelSpace G]

private theorem setIntegral_pos_of_isFundamentalDomain (Γ : Subgroup G) [Countable ↥Γ]
    [MeasurableConstSMul ↥Γ G] (μ : Measure G) [μ.IsOpenPosMeasure] {S T : Set G}
    [SMulInvariantMeasure ↥Γ G (μ.restrict T)]
    (hS : IsFundamentalDomain ↥Γ S (μ.restrict T)) (F : G → ℝ)
    (hF0 : ∀ w, 0 ≤ F w) (hFΓ : ∀ (γ : ↥Γ) (w : G), F (γ • w) = F w)
    (hint : IntegrableOn F S μ) {U : Set G} (hUo : IsOpen U) (hUne : U.Nonempty) (hUT : U ⊆ T)
    (hUF : ∀ w ∈ U, 0 < F w) : 0 < ∫ w in S, F w ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun w => hF0 w) hint]
  have hU : (μ.restrict T) U ≠ 0 := by
    rw [Measure.restrict_apply hUo.measurableSet, Set.inter_eq_self_of_subset_left hUT]
    exact (hUo.measure_pos μ hUne).ne'
  obtain ⟨γ, hγ⟩ := exists_measure_smul_inter_ne_zero hS hU
  have hsub : γ • U ∩ S ⊆ Function.support F ∩ S := by
    rintro w ⟨⟨u, hu, rfl⟩, hw⟩
    exact ⟨show F (γ • u) ≠ 0 by rw [hFΓ γ u]; exact (hUF u hu).ne', hw⟩
  refine pos_iff_ne_zero.mpr fun h0 => hγ (nonpos_iff_eq_zero.mp ?_)
  calc (μ.restrict T) (γ • U ∩ S) ≤ μ (γ • U ∩ S) := Measure.le_iff'.mp Measure.restrict_le_self _
    _ ≤ μ (Function.support F ∩ S) := measure_mono hsub
    _ = 0 := h0

end Positivity

section Pairing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem integrable_mul_conj_mul {x y : α → ℂ} {wt : α → ℝ} (hx : MemLp x 2 μ)
    (hy : MemLp y 2 μ) (hwt : AEStronglyMeasurable wt μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖wt a‖ ≤ C) :
    Integrable (fun a => x a * (starRingEnd ℂ) (y a) * ((wt a : ℝ) : ℂ)) μ := by
  have hxa := hx.aestronglyMeasurable
  have hya := hy.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => x a * (starRingEnd ℂ) (y a) * ((wt a : ℝ) : ℂ)) μ :=
    (hxa.mul (Complex.continuous_conj.comp_aestronglyMeasurable hya)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hwt)
  have hx2 : Integrable (fun a => ‖x a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hxa).mp hx
  have hy2 : Integrable (fun a => ‖y a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hya).mp hy
  refine Integrable.mono' ((hx2.add hy2).const_mul (max C 0)) hmeas ?_
  filter_upwards [hC] with a ha
  simp only [Pi.add_apply]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real]
  have h2 : ‖x a‖ * ‖y a‖ ≤ ‖x a‖ ^ 2 + ‖y a‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x a‖ - ‖y a‖), norm_nonneg (x a), norm_nonneg (y a)]
  calc ‖x a‖ * ‖y a‖ * ‖wt a‖ ≤ (‖x a‖ ^ 2 + ‖y a‖ ^ 2) * max C 0 :=
        mul_le_mul h2 (ha.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = max C 0 * (‖x a‖ ^ 2 + ‖y a‖ ^ 2) := mul_comm _ _

private theorem integrable_norm_sq_mul {f : α → ℂ} {wt : α → ℝ} (hf : MemLp f 2 μ)
    (hwt : AEStronglyMeasurable wt μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖wt a‖ ≤ C) :
    Integrable (fun a => ‖f a‖ ^ 2 * wt a) μ := by
  have hf2 : Integrable (fun a => ‖f a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  refine Integrable.mono' (hf2.const_mul (max C 0)) (hf2.aestronglyMeasurable.mul hwt) ?_
  filter_upwards [hC] with a ha
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖f a‖ ^ 2 * ‖wt a‖ ≤ ‖f a‖ ^ 2 * max C 0 :=
        mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (sq_nonneg _)
    _ = max C 0 * ‖f a‖ ^ 2 := mul_comm _ _

private theorem integral_mul_conj_mul_self (f : α → ℂ) (wt : α → ℝ) :
    ∫ a, f a * (starRingEnd ℂ) (f a) * ((wt a : ℝ) : ℂ) ∂μ = ((∫ a, ‖f a‖ ^ 2 * wt a ∂μ : ℝ) : ℂ) := by
  have h : ∀ a, f a * (starRingEnd ℂ) (f a) * ((wt a : ℝ) : ℂ) = ((‖f a‖ ^ 2 * wt a : ℝ) : ℂ) := fun a => by
    rw [Complex.mul_conj, Complex.ofReal_mul, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  exact integral_ofReal

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.memLp_two_of_lintegral (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:118)
theorem memLp_two_of_lintegral {f : α → ℂ} (h1 : AEStronglyMeasurable f μ)
    (h2 : ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞) : MemLp f 2 μ := by
  rw [memLp_iff]
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top h1).mpr ?_
  simpa only [ENNReal.toReal_ofNat] using h2

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lintegral_lt_top_of_memLp_two (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:123)
theorem lintegral_lt_top_of_memLp_two {f : α → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hf.aestronglyMeasurable).mp hf
  simpa only [ENNReal.toReal_ofNat] using h

end Pairing

section Spans

variable {G : Type*} [Group G]

private abbrev trSpan (f : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun z => f (z * h))

private theorem self_mem_trSpan (f : G → ℂ) : f ∈ trSpan f :=
  Submodule.subset_span ⟨1, funext fun z => congrArg f (mul_one z)⟩

private def rt (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun x := fun z => x (z * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem translate_mem_trSpan {f x : G → ℂ} (hx : x ∈ trSpan f) (g : G) :
    (fun z => x (z * g)) ∈ trSpan f := by
  have h : Submodule.map (rt g) (trSpan f) ≤ trSpan f := by
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, funext fun z => congrArg f (mul_assoc z g h).symm⟩
  exact h (Submodule.mem_map_of_mem hx)

private theorem translate_mem_sup {f f' x : G → ℂ} (hx : x ∈ trSpan f ⊔ trSpan f') (g : G) :
    (fun z => x (z * g)) ∈ trSpan f ⊔ trSpan f' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  exact Submodule.mem_sup.mpr ⟨_, translate_mem_trSpan ha g, _, translate_mem_trSpan hb g, rfl⟩

private theorem apply_mul_of_mem_trSpan {f x : G → ℂ} (a : G) (c : ℂ) (hf : ∀ w, f (a * w) = c * f w)
    (hx : x ∈ trSpan f) : ∀ w, x (a * w) = c * x w := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    intro w
    show f (a * w * h) = c * f (w * h)
    rw [mul_assoc, hf]
  | zero => intro w; simp
  | add y z _ _ hy hz => intro w; rw [Pi.add_apply, Pi.add_apply, hy w, hz w, mul_add]
  | smul r y _ hy => intro w; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hy w]; ring

private theorem apply_mul_of_mem_sup {f f' x : G → ℂ} (a : G) (c : ℂ) (hf : ∀ w, f (a * w) = c * f w)
    (hf' : ∀ w, f' (a * w) = c * f' w) (hx : x ∈ trSpan f ⊔ trSpan f') : ∀ w, x (a * w) = c * x w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  intro w
  rw [Pi.add_apply, Pi.add_apply, apply_mul_of_mem_trSpan a c hf hy w, apply_mul_of_mem_trSpan a c hf' hz w,
    mul_add]

private theorem apply_mul_eq_of_mem_trSpan {f x : G → ℂ} (a : G) (hf : ∀ w, f (a * w) = f w)
    (hx : x ∈ trSpan f) : ∀ w, x (a * w) = x w := fun w => by
  rw [apply_mul_of_mem_trSpan a 1 (fun w => by rw [one_mul]; exact hf w) hx w, one_mul]

private theorem apply_mul_eq_of_mem_sup {f f' x : G → ℂ} (a : G) (hf : ∀ w, f (a * w) = f w)
    (hf' : ∀ w, f' (a * w) = f' w) (hx : x ∈ trSpan f ⊔ trSpan f') : ∀ w, x (a * w) = x w := fun w => by
  rw [apply_mul_of_mem_sup a 1 (fun w => by rw [one_mul]; exact hf w) (fun w => by rw [one_mul]; exact hf' w) hx w,
    one_mul]

variable [MeasurableSpace G]

private theorem memLp_of_mem_trSpan {μ : Measure G} {f x : G → ℂ}
    (hgen : ∀ h : G, MemLp (fun z => f (z * h)) 2 μ) (hx : x ∈ trSpan f) : MemLp x 2 μ := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨h, rfl⟩ := hy; exact hgen h
  | zero => exact MemLp.zero'
  | add y z _ _ hy hz => exact hy.add hz
  | smul r y _ hy => exact hy.const_smul r

private theorem memLp_of_mem_sup {μ : Measure G} {f f' x : G → ℂ}
    (hgen : ∀ h : G, MemLp (fun z => f (z * h)) 2 μ) (hgen' : ∀ h : G, MemLp (fun z => f' (z * h)) 2 μ)
    (hx : x ∈ trSpan f ⊔ trSpan f') : MemLp x 2 μ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact (memLp_of_mem_trSpan hgen hy).add (memLp_of_mem_trSpan hgen' hz)

end Spans

section Forms

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem exists_sesqForm_eq_on (W V : Submodule ℂ M) (B : M → M → ℂ)
    (hadd₁ : ∀ x₁ ∈ W, ∀ x₂ ∈ W, ∀ y ∈ V, B (x₁ + x₂) y = B x₁ y + B x₂ y)
    (hsmul₁ : ∀ (a : ℂ) (x y : M), B (a • x) y = a * B x y)
    (hadd₂ : ∀ x ∈ W, ∀ y₁ ∈ V, ∀ y₂ ∈ V, B x (y₁ + y₂) = B x y₁ + B x y₂)
    (hsmul₂ : ∀ (a : ℂ) (x y : M), B x (a • y) = (starRingEnd ℂ) a * B x y) :
    ∃ P : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, ∀ x ∈ W, ∀ y ∈ V, P x y = B x y := by
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  obtain ⟨V', hV'⟩ := Submodule.exists_isCompl V
  let pW : M →ₗ[ℂ] ↥W := Submodule.projectionOnto W W' hW'
  let pV : M →ₗ[ℂ] ↥V := Submodule.projectionOnto V V' hV'
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => B (pW x) (pV y)) ?_ ?_ ?_ ?_, ?_⟩
  · intro x₁ x₂ y
    show B (pW (x₁ + x₂)) (pV y) = B (pW x₁) (pV y) + B (pW x₂) (pV y)
    rw [map_add, Submodule.coe_add]
    exact hadd₁ _ (pW x₁).2 _ (pW x₂).2 _ (pV y).2
  · intro a x y
    show B (pW (a • x)) (pV y) = (RingHom.id ℂ) a • B (pW x) (pV y)
    rw [map_smul, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    exact hsmul₁ a _ _
  · intro x y₁ y₂
    show B (pW x) (pV (y₁ + y₂)) = B (pW x) (pV y₁) + B (pW x) (pV y₂)
    rw [map_add, Submodule.coe_add]
    exact hadd₂ _ (pW x).2 _ (pV y₁).2 _ (pV y₂).2
  · intro a x y
    show B (pW x) (pV (a • y)) = (starRingEnd ℂ) a • B (pW x) (pV y)
    rw [map_smul, Submodule.coe_smul, smul_eq_mul]
    exact hsmul₂ a _ _
  · intro x hx y hy
    show B (pW x) (pV y) = B x y
    rw [show (pW x : M) = x from congrArg Subtype.val (Submodule.projectionOnto_apply_left hW' ⟨x, hx⟩),
      show (pV y : M) = y from congrArg Subtype.val (Submodule.projectionOnto_apply_left hV' ⟨y, hy⟩)]

end Forms

end FundamentalDomainSlab

namespace AutomorphicForm
namespace PeterssonSlabPairing

open NumberField.TateGlobal FundamentalDomainSlab
open scoped ENNReal

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.dn (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:145)
abbrev dn (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.slab (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:148)
abbrev slab (F : Type) [Field F] [NumberField F] (a b : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.μH (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:151)
abbrev μH (F : Type) [Field F] [NumberField F] : Measure (AdelicGL2 (𝓞 F) F) :=
  adelicGLHaar (Fin 2) (𝓞 F) F

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.Γp (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:154)
abbrev Γp (F : Type) [Field F] [NumberField F] : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (globalPoints (𝓞 F) F).range

private abbrev pairFn (s : ℝ) (x y : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun w => x w * (starRingEnd ℂ) (y w) * ((dn w ^ (-s) : ℝ) : ℂ)

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.instCountableF (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:157)
scoped instance instCountableF : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

private scoped instance instCountableΓ : Countable ↥(Γp F) := by
  have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable

private theorem dn_pos (g : AdelicGL2 (𝓞 F) F) : 0 < dn g := ideleNorm_pos _

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.dn_mul (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:167)
theorem dn_mul (g h : AdelicGL2 (𝓞 F) F) : dn (g * h) = dn g * dn h := by
  show ideleNorm F _ = _
  rw [map_mul, ideleNorm_mul]

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.dn_globalPoints_mul (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:171)
theorem dn_globalPoints_mul (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    dn (globalPoints (𝓞 F) F γ * g) = dn g := by
  rw [dn_mul]
  show ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.dn_subtype_mul (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:177)
theorem dn_subtype_mul (γ : ↥(Γp F)) (g : AdelicGL2 (𝓞 F) F) : dn ((γ : AdelicGL2 (𝓞 F) F) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact dn_globalPoints_mul γ' g

private theorem dn_one : dn (1 : AdelicGL2 (𝓞 F) F) = 1 := by
  show ideleNorm F (Matrix.GeneralLinearGroup.det 1) = 1
  rw [map_one]
  unfold ideleNorm
  rw [map_one, NNReal.coe_one]

private theorem dn_inv (g : AdelicGL2 (𝓞 F) F) : dn g⁻¹ = (dn g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← dn_mul, mul_inv_cancel, dn_one])

private theorem dn_centralScalar (n : (AdeleRing (𝓞 F) F)ˣ) :
    dn (centralScalar (𝓞 F) F n) = ideleNorm F n ^ 2 := by
  show ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F n)) = _
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  unfold ideleNorm
  rw [map_pow, NNReal.coe_pow]

private theorem dn_centralScalar_mul (n : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    dn (centralScalar (𝓞 F) F n * g) = ideleNorm F n ^ 2 * dn g := by
  rw [dn_mul, dn_centralScalar]

-- pin: P2MW.S_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.continuous_dn (P2M/Sol/S_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.lean:174)
theorem continuous_dn : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det F

private theorem continuous_dn_rpow (s : ℝ) : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g ^ s) :=
  continuous_dn.rpow_const fun g => Or.inl (dn_pos g).ne'

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.subtype_mul_mem_slab (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:181)
theorem subtype_mul_mem_slab (γ : ↥(Γp F)) {a b : ℝ} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ slab F a b) :
    (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b := by
  show dn ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ Set.Icc a b
  rw [dn_subtype_mul]
  exact hg

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.measurableSet_slab (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:187)
theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab F a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F a b

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.preimage_subtype_mul_slab (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:190)
theorem preimage_subtype_mul_slab (γ : ↥(Γp F)) (a b : ℝ) :
    (fun w : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * w) ⁻¹' slab F a b = slab F a b := by
  ext w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [show ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * w)) = dn w from
    dn_subtype_mul γ w]

private theorem preimage_mul_right_slab (g : AdelicGL2 (𝓞 F) F) {a b : ℝ} :
    (fun w : AdelicGL2 (𝓞 F) F => w * g⁻¹) ⁻¹' slab F a b = slab F (a * dn g) (b * dn g) := by
  ext w
  have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det (w * g⁻¹)) = dn w / dn g := by
    rw [div_eq_mul_inv, ← dn_inv g]
    exact dn_mul w g⁻¹
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
  rw [h1, le_div_iff₀ (dn_pos g), div_le_iff₀ (dn_pos g)]

private theorem preimage_mul_left_slab (n : (AdeleRing (𝓞 F) F)ˣ) {a b : ℝ} :
    (fun w : AdelicGL2 (𝓞 F) F => (centralScalar (𝓞 F) F n)⁻¹ * w) ⁻¹' slab F a b
      = slab F (a * ideleNorm F n ^ 2) (b * ideleNorm F n ^ 2) := by
  ext w
  have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det ((centralScalar (𝓞 F) F n)⁻¹ * w))
      = dn w / ideleNorm F n ^ 2 := by
    rw [div_eq_mul_inv, ← dn_centralScalar, ← dn_inv, mul_comm (dn w)]
    exact dn_mul _ w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
  rw [h1, le_div_iff₀ (pow_pos (ideleNorm_pos n) 2), div_le_iff₀ (pow_pos (ideleNorm_pos n) 2)]

private theorem image_mul_right_subset_slab {S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} (hS : S ⊆ slab F a b)
    (g : AdelicGL2 (𝓞 F) F) : (fun w => w * g) '' S ⊆ slab F (a * dn g) (b * dn g) := by
  rintro _ ⟨w, hw, rfl⟩
  have h := hS hw
  show dn (w * g) ∈ Set.Icc (a * dn g) (b * dn g)
  rw [dn_mul]
  exact ⟨mul_le_mul_of_nonneg_right h.1 (dn_pos g).le, mul_le_mul_of_nonneg_right h.2 (dn_pos g).le⟩

private theorem rpow_le_of_mem_slab {a b : ℝ} (ha : 0 < a) (s : ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ slab F a b) : ‖dn g ^ s‖ ≤ max (a ^ s) (b ^ s) := by
  have h : a ≤ dn g ∧ dn g ≤ b := hg
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (dn_pos g).le s)]
  rcases le_or_gt 0 s with hs | hs
  · exact (Real.rpow_le_rpow (dn_pos g).le h.2 hs).trans (le_max_right _ _)
  · refine le_trans ?_ (le_max_left _ _)
    rw [← neg_neg s, Real.rpow_neg (dn_pos g).le, Real.rpow_neg ha.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le h.1 (neg_nonneg.mpr hs.le))

private theorem centralScalar_comm_subtype (n : (AdeleRing (𝓞 F) F)ˣ) (γ : ↥(Γp F)) :
    centralScalar (𝓞 F) F n * (γ : AdelicGL2 (𝓞 F) F) = (γ : AdelicGL2 (𝓞 F) F) * centralScalar (𝓞 F) F n :=
  (mul_centralScalar_comm n _).symm

omit [NumberField F] in

private theorem exists_norm_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 < r) : ∃ a : v.Completion, ‖a‖ = r := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r, ?_⟩
    have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
      (map_zero _) ((InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r)
    rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv, RingEquiv.apply_symm_apply,
      Real.norm_eq_abs, abs_of_pos hr] at h
    exact h.symm
  · refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (r : ℂ), ?_⟩
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (r : ℂ))
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv, RingEquiv.apply_symm_apply,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    exact h.symm

private theorem exists_ideleNorm_eq {t : ℝ} (ht : 0 < t) :
    ∃ n : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F n = t := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨a, ha0, ha⟩ := NumberField.TateGlobal.exists_norm_pow_mult_eq v₀ t ht
  refine ⟨NumberField.AdelicVolume.archCentralUnit F v₀ (Units.mk0 a ha0), ?_⟩
  rw [show ideleNorm F (NumberField.AdelicVolume.archCentralUnit F v₀ (Units.mk0 a ha0)) = _ from
    NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl F _
      (NumberField.AdelicVolume.archCentralUnit_snd v₀ _)]
  rw [Finset.prod_eq_single v₀ (fun w _ hw => by
      rw [NumberField.AdelicVolume.archCentralUnit_fst_of_ne v₀ _ hw, norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ v₀) h)]
  rw [NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_mk0, ha]

private theorem exists_dn_centralScalar_eq {t : ℝ} (ht : 0 < t) :
    ∃ n : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F n ^ 2 = t := by
  obtain ⟨n, hn⟩ := exists_ideleNorm_eq (F := F) (Real.sqrt_pos.mpr ht)
  exact ⟨n, by rw [hn, Real.sq_sqrt ht.le]⟩

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.smulInvariantMeasure_slab (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:197)
theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp F) (AdelicGL2 (𝓞 F) F) ((μH F).restrict (slab F a b)) :=
  smulInvariantMeasure_restrict (Γp F) (μH F) (measurableSet_slab a b) (fun γ => preimage_subtype_mul_slab γ a b)

set_option linter.style.haveILetI false in
-- pin: P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample.setLIntegral_fd_le_sum_mul (P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample.lean:151)
theorem setLIntegral_fd_le_sum_mul {D S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F a b))) (hSs : S ⊆ slab F a b)
    (hX : ∀ g ∈ slab F a b, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈ D) :
    ∫⁻ w in S, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F)
      ≤ (∑ n ∈ N, (‖χ n‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ w in D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) := by
  haveI := smulInvariantMeasure_slab (F := F) a b
  have hcovE : S ⊆ ⋃ γ : ↥(Γp F), (γ • ·) ⁻¹'
      ((⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b) := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩,
      Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
    exact subtype_mul_mem_slab ⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ (hSs hg)
  have hF : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F),
      (‖f (γ • w)‖₊ : ℝ≥0∞) ^ 2 = (‖f w‖₊ : ℝ≥0∞) ^ 2 := by
    rintro ⟨_, γ, rfl⟩ w
    show (‖f (globalPoints (𝓞 F) F γ * w)‖₊ : ℝ≥0∞) ^ 2 = _
    rw [hΓ]
  calc ∫⁻ w in S, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F)
      = ∫⁻ w in S, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂((μH F).restrict (slab F a b)) := by
        rw [Measure.restrict_restrict_of_subset hSs]
    _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b,
          (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂((μH F).restrict (slab F a b)) :=
        setLIntegral_fd_le_of_cover hS hcovE _ hF
    _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
    _ ≤ ∑ n ∈ N, (‖χ n‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ w in D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) :=
        setLIntegral_biUnion_translates_le (μH F) _ N (fun n => centralScalar (𝓞 F) F n)
          (fun n => (‖χ n‖₊ : ℝ≥0∞) ^ 2) (fun n => ENNReal.pow_ne_top ENNReal.coe_ne_top)
          (fun n w => by rw [hZ, nnnorm_mul, ENNReal.coe_mul, mul_pow])
    _ = (∑ n ∈ N, (‖χ n‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ w in D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) := by
        rw [Finset.sum_mul]


-- pin: P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample.cover_of_forall (P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample.lean:187)
theorem cover_of_forall {D : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, globalPoints (𝓞 F) F γ * g ∈ (· * centralScalar (𝓞 F) F n) '' D) :
    ∀ g ∈ slab F a b, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈ D := by
  intro g hg
  obtain ⟨γ, n, hn, y, hy, hyx⟩ := h g hg
  refine ⟨γ, n, hn, ?_⟩
  rw [← hyx]
  show (centralScalar (𝓞 F) F n)⁻¹ * (y * centralScalar (𝓞 F) F n) ∈ D
  rw [mul_centralScalar_comm n y, inv_mul_cancel_left]
  exact hy


private theorem pairFn_invariant (s : ℝ) {x y : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hxΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), x (globalPoints (𝓞 F) F γ * w) = x w)
    (hxZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), x (centralScalar (𝓞 F) F n * w) = χ n * x w)
    (hyΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), y (globalPoints (𝓞 F) F γ * w) = y w)
    (hyZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), y (centralScalar (𝓞 F) F n * w) = χ n * y w)
    (hχ : ∀ n : (AdeleRing (𝓞 F) F)ˣ, ‖χ n‖ = ideleNorm F n ^ s) :
    (∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F), pairFn s x y ((γ : AdelicGL2 (𝓞 F) F) * w) = pairFn s x y w) ∧
    (∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F),
      pairFn s x y (centralScalar (𝓞 F) F n * w) = pairFn s x y w) := by
  refine ⟨?_, fun n w => ?_⟩
  · rintro ⟨_, γ, rfl⟩ w
    show x (globalPoints (𝓞 F) F γ * w) * (starRingEnd ℂ) (y (globalPoints (𝓞 F) F γ * w))
        * ((dn (globalPoints (𝓞 F) F γ * w) ^ (-s) : ℝ) : ℂ) = x w * (starRingEnd ℂ) (y w) * ((dn w ^ (-s) : ℝ) : ℂ)
    rw [hxΓ, hyΓ, dn_globalPoints_mul]
  · show x (centralScalar (𝓞 F) F n * w) * (starRingEnd ℂ) (y (centralScalar (𝓞 F) F n * w))
        * ((dn (centralScalar (𝓞 F) F n * w) ^ (-s) : ℝ) : ℂ) = x w * (starRingEnd ℂ) (y w) * ((dn w ^ (-s) : ℝ) : ℂ)
    rw [hxZ, hyZ, dn_centralScalar_mul, map_mul (starRingEnd ℂ),
      Real.mul_rpow (pow_nonneg (ideleNorm_pos n).le 2) (dn_pos w).le, Complex.ofReal_mul]
    have h1 : ideleNorm F n ^ s * ideleNorm F n ^ (-s) = 1 := by
      rw [← Real.rpow_add (ideleNorm_pos n), add_neg_cancel, Real.rpow_zero]
    have hkeyR : (ideleNorm F n ^ s) ^ 2 * (ideleNorm F n ^ 2) ^ (-s) = 1 := by
      rw [pow_two, pow_two, Real.mul_rpow (ideleNorm_pos n).le (ideleNorm_pos n).le]
      calc ideleNorm F n ^ s * ideleNorm F n ^ s * (ideleNorm F n ^ (-s) * ideleNorm F n ^ (-s))
          = (ideleNorm F n ^ s * ideleNorm F n ^ (-s)) * (ideleNorm F n ^ s * ideleNorm F n ^ (-s)) := by ring
        _ = 1 := by rw [h1, one_mul]
    have hkey : χ n * (starRingEnd ℂ) (χ n) * (((ideleNorm F n ^ 2) ^ (-s) : ℝ) : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ n, ← Complex.ofReal_mul, hkeyR, Complex.ofReal_one]
    calc χ n * x w * ((starRingEnd ℂ) (χ n) * (starRingEnd ℂ) (y w))
          * ((((ideleNorm F n ^ 2) ^ (-s) : ℝ) : ℂ) * ((dn w ^ (-s) : ℝ) : ℂ))
        = (χ n * (starRingEnd ℂ) (χ n) * (((ideleNorm F n ^ 2) ^ (-s) : ℝ) : ℂ))
            * (x w * (starRingEnd ℂ) (y w) * ((dn w ^ (-s) : ℝ) : ℂ)) := by ring
      _ = x w * (starRingEnd ℂ) (y w) * ((dn w ^ (-s) : ℝ) : ℂ) := by rw [hkey, one_mul]

private theorem pairFn_translate (s : ℝ) (x y : AdelicGL2 (𝓞 F) F → ℂ) (g w : AdelicGL2 (𝓞 F) F) :
    pairFn s (fun z => x (z * g)) (fun z => y (z * g)) w = ((dn g ^ s : ℝ) : ℂ) * pairFn s x y (w * g) := by
  show x (w * g) * (starRingEnd ℂ) (y (w * g)) * ((dn w ^ (-s) : ℝ) : ℂ)
      = ((dn g ^ s : ℝ) : ℂ) * (x (w * g) * (starRingEnd ℂ) (y (w * g)) * ((dn (w * g) ^ (-s) : ℝ) : ℂ))
  rw [dn_mul, Real.mul_rpow (dn_pos w).le (dn_pos g).le, Complex.ofReal_mul]
  have h : ((dn g ^ s : ℝ) : ℂ) * ((dn g ^ (-s) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (dn_pos g), add_neg_cancel, Real.rpow_zero, Complex.ofReal_one]
  calc x (w * g) * (starRingEnd ℂ) (y (w * g)) * ((dn w ^ (-s) : ℝ) : ℂ)
      = (((dn g ^ s : ℝ) : ℂ) * ((dn g ^ (-s) : ℝ) : ℂ))
          * (x (w * g) * (starRingEnd ℂ) (y (w * g)) * ((dn w ^ (-s) : ℝ) : ℂ)) := by rw [h, one_mul]
    _ = ((dn g ^ s : ℝ) : ℂ) * (x (w * g) * (starRingEnd ℂ) (y (w * g))
          * (((dn w ^ (-s) : ℝ) : ℂ) * ((dn g ^ (-s) : ℝ) : ℂ))) := by ring

private theorem peterssonIntegral_eq (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S x y = ∫ w in S, pairFn s x y w ∂(μH F) := rfl

private theorem peterssonIntegral_translate [(μH F).IsMulRightInvariant] {S : Set (AdelicGL2 (𝓞 F) F)} {α β : ℝ}
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F α β))) (hSs : S ⊆ slab F α β) (s : ℝ)
    {x y : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hxΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), x (globalPoints (𝓞 F) F γ * w) = x w)
    (hxZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), x (centralScalar (𝓞 F) F n * w) = χ n * x w)
    (hyΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), y (globalPoints (𝓞 F) F γ * w) = y w)
    (hyZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), y (centralScalar (𝓞 F) F n * w) = χ n * y w)
    (hχ : ∀ n : (AdeleRing (𝓞 F) F)ˣ, ‖χ n‖ = ideleNorm F n ^ s) (g : AdelicGL2 (𝓞 F) F) :
    peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g))
      = ((dn g ^ s : ℝ) : ℂ) * peterssonIntegral F s S x y := by
  obtain ⟨hΓ, hZ⟩ := pairFn_invariant s hxΓ hxZ hyΓ hyZ hχ
  obtain ⟨n, hn⟩ := exists_dn_centralScalar_eq (F := F) (dn_pos g)
  rw [peterssonIntegral_eq, peterssonIntegral_eq]
  simp_rw [pairFn_translate s x y g]
  rw [integral_const_mul]
  congr 1
  refine setIntegral_mul_right_eq_of_isFundamentalDomain (Γp F) (μH F) hS hSs
    g (centralScalar (𝓞 F) F n) (centralScalar_comm_subtype n) (measurableSet_slab (α * dn g) (β * dn g))
    (fun γ => preimage_subtype_mul_slab γ _ _) (preimage_mul_right_slab g) ?_ (pairFn s x y) hΓ (hZ n)
  rw [preimage_mul_left_slab, hn]

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.CoveredBy (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:201)
def CoveredBy (D : Set (AdelicGL2 (𝓞 F) F)) (N : Finset (AdeleRing (𝓞 F) F)ˣ)
    (X : Set (AdelicGL2 (𝓞 F) F)) : Prop :=
  ∀ g ∈ X, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
    (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈ D

private theorem CoveredBy.mono {D : Set (AdelicGL2 (𝓞 F) F)} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {X X' : Set (AdelicGL2 (𝓞 F) F)} (h : CoveredBy D N X) (hX : X' ⊆ X) : CoveredBy D N X' :=
  fun g hg => h g (hX hg)

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.coveredBy_of_forall (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:210)
theorem coveredBy_of_forall {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)} {a b : ℝ}
    {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂) :
    CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F a b) := by
  intro g hg
  obtain ⟨γ, n, hn, x, hx, y, hy, hyx⟩ := h g hg
  refine ⟨γ, n, hn, ?_⟩
  rw [← hyx]
  show (centralScalar (𝓞 F) F n)⁻¹ * (y * (centralScalar (𝓞 F) F n * x)) ∈ _
  rw [← mul_assoc y, mul_centralScalar_comm n y, mul_assoc, inv_mul_cancel_left]
  exact Set.mem_iUnion₂.mpr ⟨x, hx, y, hy, rfl⟩

-- pin: P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.memLp_of_coveredBy (P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean:226)
theorem memLp_of_coveredBy {D S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hmem : MemLp f 2 ((μH F).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F a b))) (hSs : S ⊆ slab F a b)
    (hX : CoveredBy D N (slab F a b)) : MemLp f 2 ((μH F).restrict S) := by
  have hcov' : ∀ g ∈ slab F a b, ∃ γ : ↥(Γp F), ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ D := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g hg
    exact ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩, n, hn, h⟩
  have hfa : ∀ (i : ↥(Γp F) × ↥N) (w : AdelicGL2 (𝓞 F) F),
      f ((centralScalar (𝓞 F) F (i.2 : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * (i.1 : AdelicGL2 (𝓞 F) F) * w)
        = χ (i.2 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ * f w := by
    rintro ⟨⟨_, γ, rfl⟩, n, hn⟩ w
    show f ((centralScalar (𝓞 F) F n)⁻¹ * globalPoints (𝓞 F) F γ * w) = χ n⁻¹ * f w
    rw [← map_inv, mul_assoc, hZ, hΓ]

  have h1 : AEStronglyMeasurable f ((μH F).restrict S) := by
    refine aestronglyMeasurable_of_cover_translates (μH F) hmem.aestronglyMeasurable
      (fun i : ↥(Γp F) × ↥N =>
        (centralScalar (𝓞 F) F (i.2 : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * (i.1 : AdelicGL2 (𝓞 F) F))
      (fun i => χ (i.2 : (AdeleRing (𝓞 F) F)ˣ)⁻¹) (fun i => hχ _) hfa fun g hg => ?_
    obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨⟨γ, n, hn⟩, ?_⟩
    show (centralScalar (𝓞 F) F n)⁻¹ * (γ : AdelicGL2 (𝓞 F) F) * g ∈ D
    rwa [mul_assoc]

  have h2 : ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ∞ := by
    have := smulInvariantMeasure_slab (F := F) a b
    have hcovE : S ⊆ ⋃ γ : ↥(Γp F), (γ • ·) ⁻¹'
        ((⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b) := fun g hg => by
      obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
      refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
      exact subtype_mul_mem_slab γ (hSs hg)
    have hF : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F), ‖f (γ • w)‖ₑ ^ (2 : ℝ) = ‖f w‖ₑ ^ (2 : ℝ) := by
      rintro ⟨_, γ, rfl⟩ w
      show ‖f (globalPoints (𝓞 F) F γ * w)‖ₑ ^ (2 : ℝ) = _
      rw [hΓ]
    have hD : ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ∞ := lintegral_lt_top_of_memLp_two hmem
    calc ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F)
        = ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) := by
          rw [Measure.restrict_restrict_of_subset hSs]
      _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b,
            ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) :=
          setLIntegral_fd_le_of_cover hS hcovE _ hF
      _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
          lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
      _ ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
          setLIntegral_biUnion_translates_le (μH F) _ N (fun n => centralScalar (𝓞 F) F n)
            (fun n => ‖χ n‖ₑ ^ (2 : ℝ)) (fun n => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
            (fun n w => by rw [hZ, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])
      _ < ∞ := by
          refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ hD
          exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
  exact memLp_two_of_lintegral h1 h2

private theorem memLp_translate_of_cover [(μH F).IsMulRightInvariant] {D S : Set (AdelicGL2 (𝓞 F) F)}
    {α β : ℝ} (hα : 0 < α) {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hmem : MemLp f 2 ((μH F).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F α β))) (hSs : S ⊆ slab F α β)
    (hcov : ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, CoveredBy D N (slab F a b))
    (h : AdelicGL2 (𝓞 F) F) : MemLp (fun z => f (z * h)) 2 ((μH F).restrict S) := by
  obtain ⟨N, hN⟩ := hcov (α * dn h) (β * dn h) (mul_pos hα (dn_pos h))
  refine memLp_comp_mul_right (μH F) h ?_
  exact memLp_of_coveredBy hmem hΓ hZ hχ
    (isFundamentalDomain_image_mul_right (Γp F) (μH F) hS h (preimage_mul_right_slab h))
    (image_mul_right_subset_slab hSs h) hN

private theorem integrable_pairFn {S : Set (AdelicGL2 (𝓞 F) F)} {α β : ℝ} (hα : 0 < α) (hSs : S ⊆ slab F α β)
    (s : ℝ) {x y : AdelicGL2 (𝓞 F) F → ℂ} (hx : MemLp x 2 ((μH F).restrict S)) (hy : MemLp y 2 ((μH F).restrict S)) :
    Integrable (pairFn s x y) ((μH F).restrict S) := by
  refine integrable_mul_conj_mul hx hy (continuous_dn_rpow (-s)).aestronglyMeasurable
    (C := max (α ^ (-s)) (β ^ (-s))) ?_
  exact ae_restrict_of_ae_restrict_of_subset hSs
    ((ae_restrict_mem (measurableSet_slab α β)).mono fun w hw => rpow_le_of_mem_slab hα (-s) hw)

private theorem integrable_norm_sq_wt {S : Set (AdelicGL2 (𝓞 F) F)} {α β : ℝ} (hα : 0 < α) (hSs : S ⊆ slab F α β)
    (s : ℝ) {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : MemLp f 2 ((μH F).restrict S)) :
    Integrable (fun w => ‖f w‖ ^ 2 * dn w ^ (-s)) ((μH F).restrict S) := by
  refine integrable_norm_sq_mul hf (continuous_dn_rpow (-s)).aestronglyMeasurable
    (C := max (α ^ (-s)) (β ^ (-s))) ?_
  exact ae_restrict_of_ae_restrict_of_subset hSs
    ((ae_restrict_mem (measurableSet_slab α β)).mono fun w hw => rpow_le_of_mem_slab hα (-s) hw)

private theorem peterssonIntegral_self (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S f f = ((∫ w in S, ‖f w‖ ^ 2 * dn w ^ (-s) ∂(μH F) : ℝ) : ℂ) := by
  rw [peterssonIntegral_eq]
  exact integral_mul_conj_mul_self f (fun w => dn w ^ (-s))

private theorem setIntegral_norm_sq_wt_pos {S : Set (AdelicGL2 (𝓞 F) F)} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F α β))) (s : ℝ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hf : Continuous f)
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0) (hne : ∃ g, f g ≠ 0)
    (hint : Integrable (fun w => ‖f w‖ ^ 2 * dn w ^ (-s)) ((μH F).restrict S)) :
    0 < ∫ w in S, ‖f w‖ ^ 2 * dn w ^ (-s) ∂(μH F) := by
  have := smulInvariantMeasure_slab (F := F) α β
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨n, hn⟩ := exists_dn_centralScalar_eq (F := F) (t := (α + β) / 2 / dn g₀)
    (by have := dn_pos g₀; positivity)
  have hg₁ : dn (centralScalar (𝓞 F) F n * g₀) = (α + β) / 2 := by
    rw [dn_centralScalar_mul, hn, div_mul_cancel₀ _ (dn_pos g₀).ne']
  refine setIntegral_pos_of_isFundamentalDomain (Γp F) (μH F) (T := slab F α β) hS
    (fun w => ‖f w‖ ^ 2 * dn w ^ (-s)) (fun w => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (dn_pos w).le _))
    ?_ hint (U := {g | dn g ∈ Set.Ioo α β} ∩ {g | f g ≠ 0}) ?_ ?_ ?_ ?_
  · rintro ⟨_, γ, rfl⟩ w
    show ‖f (globalPoints (𝓞 F) F γ * w)‖ ^ 2 * dn (globalPoints (𝓞 F) F γ * w) ^ (-s) = _
    rw [hΓ, dn_globalPoints_mul]
  · exact (isOpen_Ioo.preimage continuous_dn).inter (isOpen_compl_singleton.preimage hf)
  · refine ⟨centralScalar (𝓞 F) F n * g₀, ?_, ?_⟩
    · show dn (centralScalar (𝓞 F) F n * g₀) ∈ Set.Ioo α β
      rw [hg₁]
      constructor <;> linarith
    · show f (centralScalar (𝓞 F) F n * g₀) ≠ 0
      rw [hZ]
      exact mul_ne_zero (hχ n) hg₀
  · exact fun g hg => Set.Ioo_subset_Icc_self hg.1
  · exact fun w hw => mul_pos (pow_pos (norm_pos_iff.mpr hw.2) 2) (Real.rpow_pos_of_pos (dn_pos w) _)

private theorem peterssonIntegral_add_left (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) {x₁ x₂ y : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : Integrable (pairFn s x₁ y) ((μH F).restrict S)) (h₂ : Integrable (pairFn s x₂ y) ((μH F).restrict S)) :
    peterssonIntegral F s S (x₁ + x₂) y = peterssonIntegral F s S x₁ y + peterssonIntegral F s S x₂ y := by
  rw [peterssonIntegral_eq, peterssonIntegral_eq, peterssonIntegral_eq, ← integral_add h₁ h₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [pairFn, Pi.add_apply]
  ring

private theorem peterssonIntegral_smul_left (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (a : ℂ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S (a • x) y = a * peterssonIntegral F s S x y := by
  rw [peterssonIntegral_eq, peterssonIntegral_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [pairFn, Pi.smul_apply, smul_eq_mul]
  ring

private theorem peterssonIntegral_add_right (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) {x y₁ y₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : Integrable (pairFn s x y₁) ((μH F).restrict S)) (h₂ : Integrable (pairFn s x y₂) ((μH F).restrict S)) :
    peterssonIntegral F s S x (y₁ + y₂) = peterssonIntegral F s S x y₁ + peterssonIntegral F s S x y₂ := by
  rw [peterssonIntegral_eq, peterssonIntegral_eq, peterssonIntegral_eq, ← integral_add h₁ h₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [pairFn, Pi.add_apply, map_add]
  ring

private theorem peterssonIntegral_smul_right (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (a : ℂ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S x (a • y) = (starRingEnd ℂ) a * peterssonIntegral F s S x y := by
  rw [peterssonIntegral_eq, peterssonIntegral_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [pairFn, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private def cc {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {B : Set (AdeleRing (𝓞 F) F)}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ)
    (n : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((R.centralChar ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)

private theorem cc_ne_zero {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {B : Set (AdeleRing (𝓞 F) F)}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ)
    (n : (AdeleRing (𝓞 F) F)ˣ) : cc R n ≠ 0 :=
  Units.ne_zero _

private theorem unpack {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {B : Set (AdeleRing (𝓞 F) F)}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ) :
    (∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g) ∧
    (∀ (n : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (centralScalar (𝓞 F) F n * g) = cc R n * R.toFun g) ∧
    MemLp R.toFun 2 ((μH F).restrict D) := by
  have h : LsXiMemberAt (𝓞 F) F (μH F) (productionPinsOf F D U gen B).Z R.centralChar D R.toFun :=
    R.smoothCusp.1.1
  rw [lsXiMemberAt_iff] at h
  exact ⟨h.1.left_invariant, fun n g => h.1.central_transform ⟨n, Subgroup.mem_top n⟩ g, h.2⟩

-- pin: main (S_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean:844)
theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (π π' : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π.toRawCentral)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral R')
    (s : ℝ)
    (hs : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      ‖((R'.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F x ^ s)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [hri : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant]
    (hN : ∀ (a b : ℝ), 0 < a →
      ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
          ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
            globalPoints (𝓞 F) F γ * g ∈
              (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂) :
    (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
          peterssonIntegral F s S x y) ∧
    peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 ∧
    (R.centralChar = R'.centralChar →
      (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
            Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
            peterssonIntegral F s S x y) ∧
      ∃ P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          P (fun z => x (z * g)) (fun z => y (z * g)) =
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y) ∧
        (∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
          P y y ≠ 0) ∧
        ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          P x y = peterssonIntegral F s S x y) := by

  obtain ⟨hRΓ, hRZ, hRmem⟩ := unpack R
  obtain ⟨hR'Γ, hR'Z, hR'mem⟩ := unpack R'
  have hR'cont : Continuous R'.toFun := hR'
  have hs' : ∀ n : (AdeleRing (𝓞 F) F)ˣ, ‖cc R' n‖ = ideleNorm F n ^ s := hs

  have hcovN : ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F a b) :=
    fun a b ha => (hN a b ha).imp fun N h => coveredBy_of_forall h

  have hgenR : ∀ h, MemLp (fun z => R.toFun (z * h)) 2 ((μH F).restrict S) :=
    memLp_translate_of_cover hα hRmem hRΓ hRZ (cc_ne_zero R) hS hSs hcovN
  have hgenR' : ∀ h, MemLp (fun z => R'.toFun (z * h)) 2 ((μH F).restrict S) :=
    memLp_translate_of_cover hα hR'mem hR'Γ hR'Z (cc_ne_zero R') hS hSs hcovN
  have hVmem : ∀ y ∈ trSpan R'.toFun, MemLp y 2 ((μH F).restrict S) :=
    fun y hy => memLp_of_mem_trSpan hgenR' hy
  have hWmem : ∀ x ∈ trSpan R.toFun ⊔ trSpan R'.toFun, MemLp x 2 ((μH F).restrict S) :=
    fun x hx => memLp_of_mem_sup hgenR hgenR' hx

  have hcovV : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ trSpan R'.toFun → y ∈ trSpan R'.toFun →
      peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((dn g ^ s : ℝ) : ℂ) * peterssonIntegral F s S x y := by
    intro g x y hx hy
    exact peterssonIntegral_translate hS hSs s
      (fun γ => apply_mul_eq_of_mem_trSpan (globalPoints (𝓞 F) F γ) (hR'Γ γ) hx)
      (fun n => apply_mul_of_mem_trSpan (centralScalar (𝓞 F) F n) (cc R' n) (hR'Z n) hx)
      (fun γ => apply_mul_eq_of_mem_trSpan (globalPoints (𝓞 F) F γ) (hR'Γ γ) hy)
      (fun n => apply_mul_of_mem_trSpan (centralScalar (𝓞 F) F n) (cc R' n) (hR'Z n) hy)
      hs' g

  have hpos : peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 := by
    have hmemS : MemLp R'.toFun 2 ((μH F).restrict S) := hVmem _ (self_mem_trSpan _)
    rw [peterssonIntegral_self]
    exact Complex.ofReal_ne_zero.mpr (setIntegral_norm_sq_wt_pos hα hαβ hS s hR'cont hR'Γ hR'Z
      (cc_ne_zero R') R'.exists_ne_zero (integrable_norm_sq_wt hα hSs s hmemS)).ne'
  refine ⟨hcovV, hpos, fun hω => ?_⟩

  have hRZ' : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (centralScalar (𝓞 F) F n * g) = cc R' n * R.toFun g := by
    intro n g
    rw [hRZ n g]
    simp only [cc, hω]

  have hcovW : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ trSpan R.toFun ⊔ trSpan R'.toFun → y ∈ trSpan R'.toFun →
      peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((dn g ^ s : ℝ) : ℂ) * peterssonIntegral F s S x y := by
    intro g x y hx hy
    exact peterssonIntegral_translate hS hSs s
      (fun γ => apply_mul_eq_of_mem_sup (globalPoints (𝓞 F) F γ) (hRΓ γ) (hR'Γ γ) hx)
      (fun n => apply_mul_of_mem_sup (centralScalar (𝓞 F) F n) (cc R' n) (hRZ' n) (hR'Z n) hx)
      (fun γ => apply_mul_eq_of_mem_trSpan (globalPoints (𝓞 F) F γ) (hR'Γ γ) hy)
      (fun n => apply_mul_of_mem_trSpan (centralScalar (𝓞 F) F n) (cc R' n) (hR'Z n) hy)
      hs' g

  have hint : ∀ x ∈ trSpan R.toFun ⊔ trSpan R'.toFun, ∀ y ∈ trSpan R'.toFun,
      Integrable (pairFn s x y) ((μH F).restrict S) :=
    fun x hx y hy => integrable_pairFn hα hSs s (hWmem x hx) (hVmem y hy)
  obtain ⟨P, hP⟩ := exists_sesqForm_eq_on (trSpan R.toFun ⊔ trSpan R'.toFun) (trSpan R'.toFun)
    (peterssonIntegral F s S)
    (fun x₁ hx₁ x₂ hx₂ y hy => peterssonIntegral_add_left s S (hint x₁ hx₁ y hy) (hint x₂ hx₂ y hy))
    (peterssonIntegral_smul_left s S)
    (fun x hx y₁ hy₁ y₂ hy₂ => peterssonIntegral_add_right s S (hint x hx y₁ hy₁) (hint x hx y₂ hy₂))
    (peterssonIntegral_smul_right s S)
  refine ⟨hcovW, P, fun g x y hx hy => ?_, ⟨R'.toFun, self_mem_trSpan _, ?_⟩, fun x y hx hy => hP x hx y hy⟩
  · rw [hP _ (translate_mem_sup hx g) _ (translate_mem_trSpan hy g), hP x hx y hy]
    exact hcovW g x y hx hy
  · rw [hP _ (Submodule.mem_sup_right (self_mem_trSpan _)) _ (self_mem_trSpan _)]
    exact hpos

end PeterssonSlabPairing
end AutomorphicForm

/- The headline: stated verbatim from the pin `Theorems/` wrapper and proved by `main` above,
   supplying the SC1 covering
   (`AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre`) — exactly as the
   pin's `solution` does. -/

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped NumberField

namespace AutomorphicForm

theorem exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (π π' : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π.toRawCentral)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral R')
    (s : ℝ)
    (hs : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      ‖((R'.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F x ^ s)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
          peterssonIntegral F s S x y) ∧
    peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 ∧
    (R.centralChar = R'.centralChar →
      (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
            Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
            peterssonIntegral F s S x y) ∧
      ∃ P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          P (fun z => x (z * g)) (fun z => y (z * g)) =
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y) ∧
        (∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
          P y y ≠ 0) ∧
        ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          P x y = peterssonIntegral F s S x y) := by
  have := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  exact PeterssonSlabPairing.main c u d₁ d₂ T π π' R R' hR' s hs α β hα hαβ S hSs hS
    fun a b ha =>
      exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov a b ha

end AutomorphicForm
