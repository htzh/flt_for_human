/-
  A compactly supported family of smooth functions has one compact support superset and one
  uniform seminorm bound:

      for `p ↦ f (c p + ℓ p x)` with `ℓ p` injective and the family compactly supported, all
      supports lie in one compact set and every seminorm `‖x‖ ^ k * ‖iteratedFDeriv ℝ n (…) x‖`
      is uniformly bounded on the compact parameter set.

  The portable half of the former `Analysis/DecayEstimates` module (2026-10-20); the model
  integral that shared it is a different subject and now lives in
  `Analysis/SpecialFunctions/Pow/Decay.lean`. The pin's block namespace
  `M4aP3B.Rows.UniformSeminorm` is a proof label and is gone: the two general lemmas are at
  root under their own names, and the pin's `solution` wrapper (`…_impl`, an exact duplicate of
  the headline) and its `gate_empty` case check are `private`.

  The mathematics: `hsupp` gives a closed ball containing the support of `f`; the affine maps
  `x ↦ c p + ℓ p x` with `‖ℓ p‖ ≤ Mc` and `c p` bounded take it into a fixed ball; the seminorm
  bound follows from the chain rule on the affine composition and from compactness of the
  parameter set.

  Assumes: mathlib `v4.34.0` only. Mathlib has no statement of this shape (`rg
  "exists_isCompact_tsupport_subset_and_norm_pow_mul" Mathlib/` is empty, 2026-10-20).

  spec-pin: Theorems/Thm_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport.lean
  spec-pin: P2M/Sol/S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport.lean
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter Topology

variable {E E' V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace P]

omit [FiniteDimensional ℝ E] [TopologicalSpace P] in

theorem norm_iteratedFDeriv_comp_affine_le {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : E') (L : E →L[ℝ] E') (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun x => f (a + L x)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a + L x)‖ * ‖L‖ ^ n := by
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun z => f (a + z)) := hf.comp (contDiff_const.add contDiff_id)
  have hfun : (fun x => f (a + L x)) = (fun z => f (a + z)) ∘ L := rfl
  rw [hfun, L.iteratedFDeriv_comp_right hfa x (i := n) (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  calc ‖(iteratedFDeriv ℝ n f (a + L x)).compContinuousLinearMap fun _ => L‖
      ≤ ‖iteratedFDeriv ℝ n f (a + L x)‖ * ∏ _i : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n f (a + L x)‖ * ‖L‖ ^ n := by rw [Finset.prod_const, Finset.card_fin]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in

theorem exists_pos_forall_mul_norm_le {Q : Set P} (hQ : IsCompact Q) {ℓ : P → E →L[ℝ] E'}
    (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ Q, ∀ x : E, m * ‖x‖ ≤ ‖ℓ p x‖ := by
  have hcpt : IsCompact (Q ×ˢ sphere (0 : E) 1) := hQ.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun q : P × E => ‖ℓ q.1 q.2‖) (Q ×ˢ sphere (0 : E) 1) :=
    ((hℓ.comp continuousOn_fst fun q hq => hq.1).clm_apply continuousOn_snd).norm

  have hscale : ∀ p (x : E), x ≠ 0 → ‖ℓ p x‖ = ‖x‖ * ‖ℓ p (‖x‖⁻¹ • x)‖ := by
    intro p x hx
    rw [map_smul, norm_smul, norm_inv, norm_norm, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx),
      one_mul]
  have hsph : ∀ x : E, x ≠ 0 → ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  rcases (Q ×ˢ sphere (0 : E) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have : (p, ‖x‖⁻¹ • x) ∈ Q ×ˢ sphere (0 : E) 1 := ⟨hp, hsph x hx⟩
      rw [he] at this
      exact this.elim
  · obtain ⟨q₀, hq₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
    have hpos : 0 < ‖ℓ q₀.1 q₀.2‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have hq2 : q₀.2 ≠ 0 := by
        have := hq₀.2; rw [mem_sphere_zero_iff_norm] at this
        intro hz; rw [hz, norm_zero] at this; exact one_ne_zero this.symm
      exact hq2 (hinj q₀.1 hq₀.1 (by rw [h0, map_zero]))
    refine ⟨‖ℓ q₀.1 q₀.2‖, hpos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · rw [hscale p x hx]
      have hm := hmin (a := (p, ‖x‖⁻¹ • x)) ⟨hp, hsph x hx⟩
      simp only at hm
      exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left hm (norm_nonneg x))

private theorem exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl
    {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    {Q : Set P} (hQ : IsCompact Q) {c : P → E'} {ℓ : P → E →L[ℝ] E'}
    (hc : ContinuousOn c Q) (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C := by

  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : E')
  obtain ⟨Mc, hMc⟩ := hQ.exists_bound_of_continuousOn hc
  obtain ⟨m, hm, hml⟩ := exists_pos_forall_mul_norm_le (E' := E') hQ hℓ hinj
  obtain ⟨Ml, hMl⟩ := hQ.exists_bound_of_continuousOn hℓ
  set ρ : ℝ := (R + Mc) / m with hρ

  have hsuppS : ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ closedBall (0 : E) ρ := by
    intro p hp
    refine closure_minimal ?_ isClosed_closedBall
    intro x hx
    rw [Function.mem_support] at hx
    have hK : c p + ℓ p x ∈ closedBall (0 : E') R := hR (subset_tsupport _ (Function.mem_support.2 hx))
    rw [mem_closedBall_zero_iff] at hK ⊢
    have h1 : ‖ℓ p x‖ ≤ R + Mc := by
      have := norm_le_norm_add_norm_sub' (ℓ p x) (c p + ℓ p x)

      have h' : ‖ℓ p x‖ ≤ ‖c p + ℓ p x‖ + ‖c p‖ := by
        calc ‖ℓ p x‖ = ‖(c p + ℓ p x) - c p‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖c p + ℓ p x‖ + ‖c p‖ := norm_sub_le _ _
      linarith [hMc p hp]
    have h2 := hml p hp x
    rw [hρ, le_div_iff₀ hm]
    linarith
  refine ⟨⟨closedBall 0 ρ, isCompact_closedBall 0 ρ, hsuppS⟩, fun k n => ?_⟩

  obtain ⟨Bn, hBn⟩ := (hsupp.iteratedFDeriv (𝕜 := ℝ) n).exists_bound_of_continuous
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hBn0 : 0 ≤ Bn := (norm_nonneg _).trans (hBn 0)
  refine ⟨|ρ| ^ k * (Bn * |Ml| ^ n), fun p hp x => ?_⟩
  have hC0 : 0 ≤ |ρ| ^ k * (Bn * |Ml| ^ n) := by positivity
  by_cases hx : x ∈ tsupport (fun x => f (c p + ℓ p x))
  ·
    have hxρ : ‖x‖ ≤ |ρ| := (mem_closedBall_zero_iff.1 (hsuppS p hp hx)).trans (le_abs_self ρ)
    have hD : ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ Bn * |Ml| ^ n := by
      refine (norm_iteratedFDeriv_comp_affine_le hf (c p) (ℓ p) n x).trans ?_
      exact mul_le_mul (hBn _) (pow_le_pow_left₀ (norm_nonneg _) ((hMl p hp).trans (le_abs_self _)) n)
        (by positivity) hBn0
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxρ k) hD (norm_nonneg _) (by positivity)
  ·
    have h0 : iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_iteratedFDeriv_subset n h)
    rw [h0, norm_zero, mul_zero]
    exact hC0

private theorem gate_empty {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    (c : P → E') (ℓ : P → E →L[ℝ] E') :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ (∅ : Set P), tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ (∅ : Set P), ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C :=
  exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl hf hsupp isCompact_empty
    (continuousOn_empty _) (continuousOn_empty _) (fun _ h => h.elim)


theorem exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
    {E E' V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace P] {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    {Q : Set P} (hQ : IsCompact Q) {c : P → E'} {ℓ : P → E →L[ℝ] E'}
    (hc : ContinuousOn c Q) (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C := by
  exact exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl
    hf hsupp hQ hc hℓ hinj
