/-
  The `SL(2, ℤ)`-translates of the standard fundamental domain: the set of points
  at which exactly two translates meet, and the resulting double-counting identity
  for integrals over `𝒟`.

  FLT provenance, pinned `aa2d8b3`: `Definitions/Def_AutomorphicForm_ModularFundamentalDomain.lean`
  lines 13–189 — the whole module except its four trailing "gate" theorems
  (`gate_not_isFundamentalDomain_sl2z`, `gate_two_routes`,
  `gate_factor_two_load_bearing`, `gate_two_routes_ne_zero_ne_top`), which are
  deferred: they are the only consumers of the exact-volume formula
  `volume 𝒟 = ofReal (π/3)`. The three facts borrowed from the pin's
  exact-volume / L2 modules are carried here `private`:
  `volume_fd_diff_fdo`, `volume_fdo_eq_volume_fd` (from
  `Def_AutomorphicForm_Gamma0ExactVolume.lean:12–70`) and
  `measurableSet_smul_fd` (from `Def_AutomorphicForm_L2ProductionInstance.lean:19–22`).

  The cut is the playbook §2.3 exception at one level deep: the pin reaches those
  three facts through `Gamma0ExactVolume` (176 lines) → `FundamentalDomainExactVolume`
  (236) → `EisensteinScattering` (278) and `L2ProductionInstance` (111) →
  `L2AutomorphicCarrier` (147) + `TruncatedDomainPartition` (488), 1,436 lines in
  all, of which the needed facts are three short measure-theoretic lemmas. Those
  modules and the four gate theorems are registered as deferred in
  `CARRY-FORWARD.md`; every declaration of the ported module itself remains public.
-/
import FLTForHuman.AutomorphicForm.UpperHalfPlane.FundamentalDomainVolume
import FLTForHuman.AutomorphicForm.UpperHalfPlane.Gamma0FundamentalSet
import FLTForHuman.AutomorphicForm.UpperHalfPlane.HyperbolicMeasure

set_option autoImplicit false

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal Modular

noncomputable section

namespace FLT.ModularFundamentalDomain

open FLT.HyperbolicMeasure FLT.FundamentalDomainVolume

/-! ### The three exact-volume facts and the two instances (cut from the deferred modules) -/

-- From `Def_AutomorphicForm_L2ProductionInstance.lean:27–31` (deferred).
private instance countable_sl2z : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  inferInstanceAs (Countable { A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1 })

private theorem volume_eq_zero_of_image_null {s : Set ℍ}
    (h : volume ((↑) '' s : Set ℂ) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

private theorem volume_re_eq_zero (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hset : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Set.mem_prod]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem volume_normSq_eq_one : volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have hsub : {z : ℂ | Complex.normSq z = 1} ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [Metric.mem_sphere, dist_zero_right]
    nlinarith [Complex.normSq_eq_norm_sq z, norm_nonneg z]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 1)

private theorem volume_fd_diff_fdo : volume ((𝒟 : Set ℍ) \ 𝒟ᵒ) = 0 := by
  apply volume_eq_zero_of_image_null
  apply measure_mono_null (t := {z : ℂ | Complex.normSq z = 1} ∪
    ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}))
  · rintro w ⟨z, ⟨⟨hn, hr⟩, hz⟩, rfl⟩
    simp only [ModularGroup.fdo, Set.mem_ofPred_eq, not_and_or, not_lt] at hz
    rcases hz with hz | hz
    · exact Or.inl (le_antisymm hz hn)
    · right
      have : |z.re| = 1 / 2 := le_antisymm hr hz
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp this with h | h
      · exact Or.inl (by simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_re]; exact h)
      · exact Or.inr (by simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_re]; exact h)
  · refine measure_union_null volume_normSq_eq_one (measure_union_null ?_ ?_) <;>
      exact volume_re_eq_zero _

private theorem volume_fdo_eq_volume_fd : volume (𝒟ᵒ : Set ℍ) = volume (𝒟 : Set ℍ) := by
  refine le_antisymm (measure_mono ModularGroup.fdo_subset_fd) ?_
  calc volume (𝒟 : Set ℍ) = volume (𝒟ᵒ ∪ (𝒟 : Set ℍ) \ 𝒟ᵒ) := by
        rw [Set.union_sdiff_cancel ModularGroup.fdo_subset_fd]
    _ ≤ volume (𝒟ᵒ : Set ℍ) + volume ((𝒟 : Set ℍ) \ 𝒟ᵒ) := measure_union_le _ _
    _ = volume (𝒟ᵒ : Set ℍ) := by rw [volume_fd_diff_fdo, add_zero]

private theorem measurableSet_smul_fd (γ : SL(2, ℤ)) : MeasurableSet (γ • (𝒟 : Set ℍ)) :=
  (ModularGroup.isClosed_fd.smul γ).measurableSet

/-! ### The translates of `𝒟` -/

theorem neg_one_smul_eq (z : ℍ) : (-1 : SL(2, ℤ)) • z = z := by
  rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, SL_neg_smul, one_smul]

theorem neg_one_smul_set_eq (s : Set ℍ) : (-1 : SL(2, ℤ)) • s = s := by
  ext z
  simp only [Set.mem_smul_set]
  constructor
  · rintro ⟨w, hw, rfl⟩; rwa [neg_one_smul_eq]
  · exact fun hz => ⟨z, hz, neg_one_smul_eq z⟩

theorem one_ne_neg_one : (1 : SL(2, ℤ)) ≠ -1 := by
  intro h
  have h00 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at h00

theorem inv_neg_eq (γ : SL(2, ℤ)) : (-γ)⁻¹ = -γ⁻¹ :=
  (eq_inv_of_mul_eq_one_left (by rw [neg_mul_neg, inv_mul_cancel])).symm

theorem inv_neg_one : (-1 : SL(2, ℤ))⁻¹ = -1 := by
  rw [inv_neg_eq, inv_one]

theorem ne_neg_self (γ : SL(2, ℤ)) : γ ≠ -γ := by
  intro h
  apply one_ne_neg_one
  calc (1 : SL(2, ℤ)) = γ⁻¹ * γ := (inv_mul_cancel γ).symm
    _ = γ⁻¹ * (-γ) := by rw [← h]
    _ = -(γ⁻¹ * γ) := by rw [mul_neg]
    _ = -1 := by rw [inv_mul_cancel]

theorem smul_fd_inter_fd_subset {γ : SL(2, ℤ)} (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    γ • (𝒟 : Set ℍ) ∩ 𝒟 ⊆ (𝒟 : Set ℍ) \ 𝒟ᵒ := by
  rintro z ⟨hzγ, hz⟩
  refine ⟨hz, fun hzo => ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hzγ
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hzγ with h | h
  · exact h1 (by rw [← inv_inv γ, h, inv_one])
  · exact h2 (by rw [← inv_inv γ, h, inv_neg_one])

theorem volume_smul_fd_inter_fd {γ : SL(2, ℤ)} (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    volume (γ • (𝒟 : Set ℍ) ∩ 𝒟) = 0 :=
  measure_mono_null (smul_fd_inter_fd_subset h1 h2) volume_fd_diff_fdo

def goodSet : Set ℍ := {z | ∃ γ : SL(2, ℤ), γ • z ∈ (𝒟ᵒ : Set ℍ)}

theorem volume_compl_goodSet : volume (goodSetᶜ : Set ℍ) = 0 := by
  have hsub : (goodSetᶜ : Set ℍ) ⊆ ⋃ γ : SL(2, ℤ), γ • ((𝒟 : Set ℍ) \ 𝒟ᵒ) := by
    intro z hz
    simp only [Set.mem_compl_iff, goodSet, Set.mem_ofPred_eq, not_exists] at hz
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    refine Set.mem_iUnion.mpr ⟨g⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact ⟨hg, hz g⟩
  refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
  rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
  exact volume_fd_diff_fdo

theorem setOf_smul_mem_fd_eq_pair {z : ℍ} (hz : z ∈ goodSet) :
    ∃ δ : SL(2, ℤ), {γ : SL(2, ℤ) | γ • z ∈ (𝒟 : Set ℍ)} = {δ, -δ} := by
  obtain ⟨δ, hδ⟩ := hz
  refine ⟨δ, Set.Subset.antisymm ?_ ?_⟩
  · intro γ hγ
    have key : (γ * δ⁻¹) • (δ • z) ∈ (𝒟 : Set ℍ) := by
      rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]
      exact hγ
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hδ key with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · refine Or.inr ?_
      have hγδ : γ = -1 * δ := by
        rw [← h, mul_assoc, inv_mul_cancel, mul_one]
      rw [Set.mem_singleton_iff, hγδ, neg_one_mul]
  · rintro γ hγ
    rcases Set.mem_insert_iff.mp hγ with rfl | hγ
    · exact ModularGroup.fdo_subset_fd hδ
    · rw [Set.mem_singleton_iff] at hγ
      subst hγ
      show (-δ) • z ∈ (𝒟 : Set ℍ)
      rw [SL_neg_smul δ z]
      exact ModularGroup.fdo_subset_fd hδ

theorem setOf_mem_smul_fd_eq_pair {z : ℍ} (hz : z ∈ goodSet) :
    ∃ δ : SL(2, ℤ), {γ : SL(2, ℤ) | z ∈ γ • (𝒟 : Set ℍ)} = {δ, -δ} := by
  obtain ⟨ε, hε⟩ := setOf_smul_mem_fd_eq_pair hz
  refine ⟨ε⁻¹, ?_⟩
  ext γ
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hmem : γ⁻¹ • z ∈ (𝒟 : Set ℍ) ↔ γ⁻¹ ∈ ({ε, -ε} : Set SL(2, ℤ)) := by
    rw [← hε]; rfl
  rw [hmem]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [← inv_inv γ, h])
    · exact Or.inr (by rw [← inv_inv γ, h, inv_neg_eq])
  · rintro (rfl | rfl)
    · exact Or.inl (by rw [inv_inv])
    · exact Or.inr (by rw [inv_neg_eq, inv_inv])

theorem tsum_indicator_smul_fd {z : ℍ} (hz : z ∈ goodSet) :
    ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z = 2 := by
  obtain ⟨δ, hδ⟩ := setOf_mem_smul_fd_eq_pair hz
  have hpair : ∀ γ : SL(2, ℤ), z ∈ γ • (𝒟 : Set ℍ) ↔ (γ = δ ∨ γ = -δ) := by
    intro γ
    constructor
    · intro h
      have : γ ∈ ({δ, -δ} : Set SL(2, ℤ)) := hδ ▸ h
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    · intro h
      have : γ ∈ ({δ, -δ} : Set SL(2, ℤ)) := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
      rw [← hδ] at this
      exact this
  have hsupp : ∀ γ : SL(2, ℤ), γ ∉ ({δ, -δ} : Finset SL(2, ℤ)) →
      (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z = 0 := by
    intro γ hγ
    rw [Set.indicator_apply_eq_zero]
    intro hmem
    exact absurd (Finset.mem_insert.mpr (((hpair γ).mp hmem).imp id Finset.mem_singleton.mpr))
      hγ
  rw [tsum_eq_sum hsupp, Finset.sum_pair (ne_neg_self δ),
    Set.indicator_of_mem ((hpair δ).mpr (Or.inl rfl)),
    Set.indicator_of_mem ((hpair (-δ)).mpr (Or.inr rfl))]
  exact one_add_one_eq_two

theorem setLIntegral_smul_fd (γ : SL(2, ℤ)) (F : ℍ → ℝ≥0∞) :
    ∫⁻ w in (𝒟 : Set ℍ), F (γ • w) ∂volume = ∫⁻ u in γ • (𝒟 : Set ℍ), F u ∂volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  have hmp : MeasurePreserving (fun w : ℍ => γ • w) volume volume :=
    ⟨hemb.measurable, by
      ext s hs
      rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
        FLT.HyperbolicMeasure.volume_smul_sl2z]⟩
  rw [hmp.setLIntegral_comp_emb hemb F (𝒟 : Set ℍ)]
  rfl

theorem tsum_setLIntegral_fd_smul (F : ℍ → ℝ≥0∞) (hF : Measurable F) :
    ∑' γ : SL(2, ℤ), ∫⁻ w in (𝒟 : Set ℍ), F (γ • w) ∂volume =
      2 * ∫⁻ z, F z ∂volume := by
  calc ∑' γ : SL(2, ℤ), ∫⁻ w in (𝒟 : Set ℍ), F (γ • w) ∂volume
      = ∑' γ : SL(2, ℤ), ∫⁻ u in γ • (𝒟 : Set ℍ), F u ∂volume := by
        exact tsum_congr fun γ => setLIntegral_smul_fd γ F
    _ = ∑' γ : SL(2, ℤ), ∫⁻ u, (γ • (𝒟 : Set ℍ)).indicator F u ∂volume := by
        exact tsum_congr fun γ => (lintegral_indicator (measurableSet_smul_fd γ) F).symm
    _ = ∫⁻ u, ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator F u ∂volume := by
        exact (lintegral_tsum fun γ =>
          (hF.indicator (measurableSet_smul_fd γ)).aemeasurable).symm
    _ = ∫⁻ u, 2 * F u ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_compl_goodSet] with z hzc
        have hz : z ∈ goodSet := by simpa using hzc
        calc ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator F z
            = ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z * F z := by
              refine tsum_congr fun γ => ?_
              by_cases h : z ∈ γ • (𝒟 : Set ℍ) <;>
                simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
          _ = (∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z) * F z :=
              ENNReal.tsum_mul_right
          _ = 2 * F z := by rw [tsum_indicator_smul_fd hz]
    _ = 2 * ∫⁻ z, F z ∂volume := lintegral_const_mul 2 hF

theorem setLIntegral_fd_tsum_smul (F : ℍ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w in (𝒟 : Set ℍ), (∑' γ : SL(2, ℤ), F (γ • w)) ∂volume =
      2 * ∫⁻ z, F z ∂volume := by
  rw [← tsum_setLIntegral_fd_smul F hF]
  exact lintegral_tsum fun γ =>
    (hF.comp (Homeomorph.smul γ (α := ℍ)).measurable).aemeasurable.restrict

end FLT.ModularFundamentalDomain

end
