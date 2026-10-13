/-
  The Euler-product bookkeeping: the monomial `mono`/`monoN`, the restricted sums
  `sigmaT` and their multiplicativity `sigmaT_insert`/`sigmaT_eq_prod_mul`, the
  tail estimate `norm_sigmaT_sub_one_le`, convergence `tendsto_sigmaT` and the
  Euler product identity `tsum_mono_mul_tprod_one_sub`; the second half contains
  the geometric bounds `sum_monoN_le_prod`, `summable_norm_div_one_sub` and the
  summability criterion `summable_norm_mono`.

  Transcribed from the pin's `Fold_EulerBookkeeping` sections
  (`M4aLocalCFT.EulerBookkeeping` namespace), declared lines 4367-4731 of file A,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped.  The pin's `mono`
  helper is promoted from `private` to `def` (`NumberField.TateGlobal.EulerBookkeeping.mono`),
  because `ShellBound`'s `norm_mono_baseFam`/`mono_baseFam_toNatVec` mention it in
  their statements; its name and body are unchanged.  The pin's deprecated `if_pos`/`if_neg` are
  spelled `ite_eq_left`/`ite_eq_right` (proof-only change).  No file-wide option
  beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.UnifPowBridge
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false

open Finsupp Filter Topology

noncomputable section

namespace NumberField
namespace TateGlobal
namespace EulerBookkeeping

variable {ι : Type*}

-- pin: mono (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4367)
def mono (a : ι → ℂ) (k : ι →₀ ℕ) : ℂ := k.prod fun i n => a i ^ n

-- pin: mono_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4370)
theorem mono_zero (a : ι → ℂ) : mono a 0 = 1 := Finsupp.prod_zero_index

-- pin: mono_add (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4372)
theorem mono_add (a : ι → ℂ) (k l : ι →₀ ℕ) : mono a (k + l) = mono a k * mono a l :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

-- pin: mono_single (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4375)
theorem mono_single (a : ι → ℂ) (i : ι) (n : ℕ) : mono a (single i n) = a i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

-- pin: norm_mono (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4378)
theorem norm_mono (a : ι → ℂ) (k : ι →₀ ℕ) : ‖mono a k‖ = k.prod fun i n => ‖a i‖ ^ n := by
  unfold mono Finsupp.prod
  rw [norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_pow _ _

section Restricted

variable (a : ι → ℂ) [DecidableEq ι]

-- pin: sigmaT (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4387)
def sigmaT (T : Finset ι) : ℂ := ∑' k : ι →₀ ℕ, if ∀ i ∈ T, k i = 0 then mono a k else 0

variable {a}

omit [DecidableEq ι] in
-- pin: sigmaT_empty (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4392)
theorem sigmaT_empty : sigmaT a ∅ = ∑' k, mono a k := by
  unfold sigmaT
  exact tsum_congr fun k => by simp

omit [DecidableEq ι] in
-- pin: summable_restrict (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4397)
theorem summable_restrict (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (p : (ι →₀ ℕ) → Prop) [DecidablePred p] :
    Summable fun k : ι →₀ ℕ => if p k then mono a k else 0 :=
  Summable.of_norm_bounded hF fun k => by
    split_ifs
    · exact le_rfl
    · simp

omit [DecidableEq ι] in
-- pin: summable_norm_of_summable_mono (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4405)
theorem summable_norm_of_summable_mono (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    Summable fun i => ‖a i‖ := by
  have h := hF.comp_injective (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0))
  refine h.congr fun i => ?_
  show ‖mono a (single i 1)‖ = ‖a i‖
  rw [mono_single, pow_one]

-- pin: sigmaT_insert (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4412)
theorem sigmaT_insert (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) {T : Finset ι} {i : ι} (hi : i ∉ T) :
    sigmaT a (insert i T) = (1 - a i) * sigmaT a T := by
  set FT : (ι →₀ ℕ) → ℂ := fun k => if ∀ j ∈ T, k j = 0 then mono a k else 0 with hFT
  set G1 : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k i = 0 then mono a k else 0 with hG1
  set G2 : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k i ≠ 0 then mono a k else 0 with hG2
  have hsplit : ∀ k, FT k = G1 k + G2 k := by
    intro k
    simp only [hFT, hG1, hG2]
    by_cases h1 : ∀ j ∈ T, k j = 0
    · by_cases h2 : k i = 0
      · rw [ite_eq_left h1, ite_eq_left ⟨h1, h2⟩, ite_eq_right (fun h => h.2 h2), add_zero]
      · rw [ite_eq_left h1, ite_eq_right (fun h => h2 h.2), ite_eq_left ⟨h1, h2⟩, zero_add]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.1), ite_eq_right (fun h => h1 h.1), add_zero]
  have hins : sigmaT a (insert i T) = ∑' k, G1 k := by
    unfold sigmaT
    refine tsum_congr fun k => ?_
    simp only [hG1, Finset.forall_mem_insert, and_comm]
  have hG1s : Summable G1 := by simpa [hG1] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k i = 0)
  have hG2s : Summable G2 := by simpa [hG2] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k i ≠ 0)
  set φ : (ι →₀ ℕ) → (ι →₀ ℕ) := fun k => k + single i 1 with hφ
  have hφinj : Function.Injective φ := add_left_injective (single i 1)
  have hsupp : Function.support G2 ⊆ Set.range φ := by
    intro k hk
    have hki : k i ≠ 0 := by
      by_contra h0
      apply hk
      simp [hG2, h0]
    refine ⟨k - single i 1, ?_⟩
    show k - single i 1 + single i 1 = k
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hki))
  have hcomp : ∀ k, G2 (φ k) = FT k * a i := by
    intro k
    have hTi : (∀ j ∈ T, ((k + single i 1 : ι →₀ ℕ)) j = 0) ↔ ∀ j ∈ T, k j = 0 := by
      refine forall₂_congr fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hji, add_zero]
    have hii : ((k + single i 1 : ι →₀ ℕ)) i ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]; exact Nat.succ_ne_zero _
    simp only [hG2, hFT, hφ, hTi, hii, ne_eq, not_false_eq_true, and_true]
    split_ifs
    · rw [mono_add, mono_single, pow_one]
    · rw [zero_mul]
  have hG2sum : ∑' k, G2 k = sigmaT a T * a i := by
    rw [← hφinj.tsum_eq hsupp]
    simp only [hcomp]
    rw [tsum_mul_right]
    rfl
  have hT : sigmaT a T = ∑' k, G1 k + ∑' k, G2 k := by
    rw [← (hG1s.hasSum.add hG2s.hasSum).tsum_eq]
    unfold sigmaT
    exact tsum_congr fun k => hsplit k
  rw [hins]
  have := hT
  rw [hG2sum] at this
  linear_combination -this

-- pin: sigmaT_eq_prod_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4468)
theorem sigmaT_eq_prod_mul (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (T : Finset ι) :
    sigmaT a T = (∏ i ∈ T, (1 - a i)) * ∑' k, mono a k := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul, sigmaT_empty]
  | insert i T hi ih => rw [sigmaT_insert hF hi, ih, Finset.prod_insert hi, mul_assoc]

-- pin: norm_sigmaT_sub_one_le (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4474)
theorem norm_sigmaT_sub_one_le (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (T : Finset ι) :
    ‖sigmaT a T - 1‖ ≤ (∑' i, if i ∈ T then 0 else ‖a i‖) * ∑' k, ‖mono a k‖ := by
  set R : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k ≠ 0 then mono a k else 0 with hR
  have hRs : Summable R := by simpa [hR] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k ≠ 0)
  have hRn : Summable fun k => ‖R k‖ := by
    refine Summable.of_norm_bounded hF fun k => ?_
    simp only [hR, norm_norm]
    split_ifs
    · exact le_rfl
    · simp
  have hsub : sigmaT a T - 1 = ∑' k, R k := by
    have h0 : ∀ k : ι →₀ ℕ, (if ∀ j ∈ T, k j = 0 then mono a k else 0)
        = (if k = 0 then (1 : ℂ) else 0) + R k := by
      intro k
      by_cases hk : k = 0
      · subst hk
        simp [hR, mono_zero]
      · simp only [hR, hk, ite_false, zero_add, ne_eq, not_false_eq_true, and_true]
    unfold sigmaT
    rw [tsum_congr h0, ((hasSum_ite_eq (0 : ι →₀ ℕ) (1 : ℂ)).add hRs.hasSum).tsum_eq]
    ring
  rw [hsub]
  refine (norm_tsum_le_tsum_norm hRn).trans ?_
  set A : Set (ι →₀ ℕ) := {k | (∀ j ∈ T, k j = 0) ∧ k ≠ 0} with hA
  have hRA : ∀ k, ‖R k‖ = A.indicator (fun k => ‖mono a k‖) k := by
    intro k
    simp only [hR, hA, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  rw [tsum_congr hRA, ← tsum_subtype]
  have hne : ∀ k : A, (k.1).support.Nonempty := fun k => Finsupp.support_nonempty_iff.mpr k.2.2
  set j : A → ι := fun k => (hne k).choose with hj
  have hjmem : ∀ k : A, j k ∈ (k.1).support := fun k => (hne k).choose_spec
  have hjpos : ∀ k : A, 1 ≤ k.1 (j k) := fun k => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (hjmem k))
  have hjT : ∀ k : A, j k ∉ T := by
    intro k hkT
    exact (Finsupp.mem_support_iff.mp (hjmem k)) (k.2.1 (j k) hkT)
  set e : A → ι × (ι →₀ ℕ) := fun k => (j k, k.1 - single (j k) 1) with he
  have hdecomp : ∀ k : A, k.1 - single (j k) 1 + single (j k) 1 = k.1 := fun k =>
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (hjpos k))
  have heinj : Function.Injective e := by
    intro k k' h
    simp only [he, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    rw [← hdecomp k, ← hdecomp k', h2, h1]
  set g : ι × (ι →₀ ℕ) → ℝ := fun p => (if p.1 ∈ T then 0 else ‖a p.1‖) * ‖mono a p.2‖ with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (by split_ifs <;> simp) (norm_nonneg _)
  have hcT : Summable fun i => if i ∈ T then (0 : ℝ) else ‖a i‖ := by
    refine Summable.of_norm_bounded (summable_norm_of_summable_mono hF) fun i => ?_
    split_ifs <;> simp
  have hcTn : Summable fun i => ‖if i ∈ T then (0 : ℝ) else ‖a i‖‖ := by
    refine hcT.norm.congr fun i => ?_
    rfl
  have hFn : Summable fun k : ι →₀ ℕ => ‖‖mono a k‖‖ := by simpa using hF
  have hgs : Summable g := by
    simpa [hg] using summable_mul_of_summable_norm hcTn hFn
  have hle : ∀ k : A, ‖mono a k.1‖ ≤ g (e k) := by
    intro k
    simp only [hg, he, hjT k, ite_false]
    conv_lhs => rw [← hdecomp k, mono_add, norm_mul, mono_single, pow_one, mul_comm]
  calc ∑' k : A, ‖mono a k.1‖
      ≤ ∑' p, g p := Summable.tsum_le_tsum_of_inj e heinj (fun p _ => hg0 p) hle (hF.subtype A) hgs
    _ = (∑' i, if i ∈ T then (0 : ℝ) else ‖a i‖) * ∑' k, ‖mono a k‖ := by
        rw [tsum_mul_tsum_of_summable_norm hcTn hFn]

-- pin: tendsto_sigmaT (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4539)
theorem tendsto_sigmaT (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    Tendsto (fun T : Finset ι => sigmaT a T) atTop (𝓝 1) := by
  have htail : Tendsto (fun T : Finset ι => ∑' i, if i ∈ T then (0 : ℝ) else ‖a i‖) atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero fun i => ‖a i‖
    refine h.congr fun T => ?_
    refine (tsum_subtype ({x | x ∉ T} : Set ι) (fun i => ‖a i‖)).trans ?_
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ T
    · rw [ite_eq_left hi, Set.indicator_of_notMem (by simpa using hi)]
    · rw [ite_eq_right hi, Set.indicator_of_mem (by simpa using hi)]
  have hbound := htail.mul_const (∑' k, ‖mono a k‖)
  rw [zero_mul] at hbound
  have h0 : Tendsto (fun T : Finset ι => sigmaT a T - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => norm_sigmaT_sub_one_le hF T) hbound
  have := h0.add_const 1
  simpa using this

end Restricted

section Main

variable {a : ι → ℂ}

-- pin: tsum_mono_mul_tprod_one_sub (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4563)
theorem tsum_mono_mul_tprod_one_sub (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    (∑' k, mono a k) * ∏' i, (1 - a i) = 1 := by
  classical
  have ha := summable_norm_of_summable_mono hF
  have hmult : Multipliable fun i => 1 - a i := by
    have h := Complex.multipliable_one_add_of_summable (f := fun i => -a i) (by simpa using ha.of_norm.neg)
    simpa [sub_eq_add_neg] using h
  have hprod : Tendsto (fun T : Finset ι => ∏ i ∈ T, (1 - a i)) atTop (𝓝 (∏' i, (1 - a i))) := by
    have h := hmult.hasProd
    rw [HasProd] at h
    simpa using h
  have h1 : Tendsto (fun T : Finset ι => sigmaT a T) atTop (𝓝 ((∏' i, (1 - a i)) * ∑' k, mono a k)) := by
    have h := hprod.mul_const (∑' k, mono a k)
    refine h.congr fun T => ?_
    rw [sigmaT_eq_prod_mul hF T]
  have h2 := tendsto_sigmaT hF
  have heq := tendsto_nhds_unique h1 h2
  rw [mul_comm] at heq
  exact heq

end Main

end EulerBookkeeping
end TateGlobal
end NumberField

end

noncomputable section

namespace NumberField
namespace TateGlobal
namespace EulerBookkeeping

variable {ι : Type*} {a : ι → ℂ}

-- pin: monoN (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4609)
def monoN (a : ι → ℂ) (k : ι →₀ ℕ) : ℝ := k.prod fun i n => ‖a i‖ ^ n

-- pin: monoN_eq_norm_mono (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4611)
theorem monoN_eq_norm_mono (k : ι →₀ ℕ) : monoN a k = ‖mono a k‖ := (norm_mono a k).symm

-- pin: monoN_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4613)
theorem monoN_nonneg (k : ι →₀ ℕ) : 0 ≤ monoN a k := by
  rw [monoN_eq_norm_mono]; exact norm_nonneg _

-- pin: monoN_add (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4616)
theorem monoN_add (k l : ι →₀ ℕ) : monoN a (k + l) = monoN a k * monoN a l :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

-- pin: monoN_single (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4619)
theorem monoN_single (i : ι) (n : ℕ) : monoN a (single i n) = ‖a i‖ ^ n :=
  Finsupp.prod_single_index (pow_zero _)

-- pin: monoN_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4622)
theorem monoN_zero : monoN a 0 = 1 := Finsupp.prod_zero_index

-- pin: sum_monoN_le_prod (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4624)
theorem sum_monoN_le_prod [DecidableEq ι] (h1 : ∀ i, ‖a i‖ < 1) (T : Finset ι) :
    ∀ u : Finset (ι →₀ ℕ), (∀ k ∈ u, k.support ⊆ T) → ∑ k ∈ u, monoN a k ≤ ∏ i ∈ T, (1 - ‖a i‖)⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
      intro u hu
      have hu0 : u ⊆ {0} := by
        intro k hk
        rw [Finset.mem_singleton, ← Finsupp.support_eq_empty]
        exact Finset.subset_empty.mp (hu k hk)
      calc ∑ k ∈ u, monoN a k ≤ ∑ k ∈ ({0} : Finset (ι →₀ ℕ)), monoN a k :=
            Finset.sum_le_sum_of_subset_of_nonneg hu0 fun k _ _ => monoN_nonneg k
        _ = 1 := by rw [Finset.sum_singleton, monoN_zero]
        _ = ∏ i ∈ (∅ : Finset ι), (1 - ‖a i‖)⁻¹ := (Finset.prod_empty).symm
  | insert i T hi ih =>
      intro u hu
      set φ : (ι →₀ ℕ) → ℕ × (ι →₀ ℕ) := fun k => (k i, k.erase i) with hφ
      have hφinj : Set.InjOn φ u := by
        intro k _ k' _ h
        simp only [hφ, Prod.mk.injEq] at h
        rw [← Finsupp.single_add_erase i k, ← Finsupp.single_add_erase i k', h.1, h.2]
      have hterm : ∀ k, monoN a k = ‖a i‖ ^ (φ k).1 * monoN a (φ k).2 := by
        intro k
        conv_lhs => rw [← Finsupp.single_add_erase i k, monoN_add, monoN_single]
      set N : Finset ℕ := u.image fun k => k i with hN
      set U : Finset (ι →₀ ℕ) := u.image fun k => k.erase i with hU
      have hUT : ∀ k' ∈ U, k'.support ⊆ T := by
        intro k' hk'
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hk'
        rw [Finsupp.support_erase]
        intro j hj
        have hj' := Finset.mem_erase.mp hj
        have := hu k hk hj'.2
        rcases Finset.mem_insert.mp this with h | h
        · exact (hj'.1 h).elim
        · exact h
      have himg : u.image φ ⊆ N ×ˢ U := by
        intro p hp
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hk, Finset.mem_image_of_mem _ hk⟩
      have hgeom : ∑ n ∈ N, ‖a i‖ ^ n ≤ (1 - ‖a i‖)⁻¹ := by
        rw [← tsum_geometric_of_lt_one (norm_nonneg _) (h1 i)]
        exact (summable_geometric_of_lt_one (norm_nonneg _) (h1 i)).sum_le_tsum N fun n _ => pow_nonneg (norm_nonneg _) n
      have hpos : ∀ j, 0 ≤ (1 - ‖a j‖)⁻¹ := fun j => inv_nonneg.mpr (sub_nonneg.mpr (h1 j).le)
      calc ∑ k ∈ u, monoN a k
          = ∑ k ∈ u, ‖a i‖ ^ (φ k).1 * monoN a (φ k).2 := Finset.sum_congr rfl fun k _ => hterm k
        _ = ∑ p ∈ u.image φ, ‖a i‖ ^ p.1 * monoN a p.2 :=
            (Finset.sum_image (f := fun p : ℕ × (ι →₀ ℕ) => ‖a i‖ ^ p.1 * monoN a p.2) hφinj).symm
        _ ≤ ∑ p ∈ N ×ˢ U, ‖a i‖ ^ p.1 * monoN a p.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ =>
              mul_nonneg (pow_nonneg (norm_nonneg _) _) (monoN_nonneg _)
        _ = (∑ n ∈ N, ‖a i‖ ^ n) * ∑ k' ∈ U, monoN a k' := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
        _ ≤ (1 - ‖a i‖)⁻¹ * ∏ j ∈ T, (1 - ‖a j‖)⁻¹ :=
            mul_le_mul hgeom (ih U hUT) (Finset.sum_nonneg fun k _ => monoN_nonneg k) (hpos i)
        _ = ∏ j ∈ insert i T, (1 - ‖a j‖)⁻¹ := by rw [Finset.prod_insert hi]

-- pin: summable_norm_div_one_sub (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4680)
theorem summable_norm_div_one_sub (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    Summable fun i => ‖a i‖ / (1 - ‖a i‖) := by
  have hsub : ∀ i, 0 < 1 - ‖a i‖ := fun i => sub_pos.mpr (h1 i)
  have hev : ∀ᶠ i in cofinite, ‖a i‖ < 1 / 2 := ha.tendsto_cofinite_zero (eventually_lt_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually (ha.mul_left 2) ?_
  filter_upwards [hev] with i hi
  have hx : 0 ≤ ‖a i‖ / (1 - ‖a i‖) := div_nonneg (norm_nonneg _) (hsub i).le
  rw [Real.norm_eq_abs, abs_of_nonneg hx, div_le_iff₀ (hsub i)]
  nlinarith [norm_nonneg (a i)]

-- pin: summable_norm_mono (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4690)
theorem summable_norm_mono (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    Summable fun k : ι →₀ ℕ => ‖mono a k‖ := by
  classical
  have hsub : ∀ i, 0 < 1 - ‖a i‖ := fun i => sub_pos.mpr (h1 i)
  set c : ι → ℝ := fun i => ‖a i‖ / (1 - ‖a i‖) with hc
  have hcs : Summable c := summable_norm_div_one_sub ha h1
  have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (norm_nonneg _) (hsub i).le
  have hfac : ∀ i, (1 - ‖a i‖)⁻¹ ≤ Real.exp (c i) := by
    intro i
    have heq : (1 - ‖a i‖)⁻¹ = c i + 1 := by
      simp only [hc]
      field_simp [(hsub i).ne']
      ring
    rw [heq]
    exact Real.add_one_le_exp (c i)
  refine (summable_of_sum_le (f := fun k : ι →₀ ℕ => monoN a k) (c := Real.exp (∑' i, c i))
    (fun k => monoN_nonneg k) fun u => ?_).congr fun k => monoN_eq_norm_mono k
  set T : Finset ι := u.biUnion fun k => k.support with hT
  have hu : ∀ k ∈ u, k.support ⊆ T := fun k hk => Finset.subset_biUnion_of_mem (fun k => k.support) hk
  calc ∑ k ∈ u, monoN a k ≤ ∏ i ∈ T, (1 - ‖a i‖)⁻¹ := sum_monoN_le_prod h1 T u hu
    _ ≤ ∏ i ∈ T, Real.exp (c i) :=
        Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (hsub i).le) fun i _ => hfac i
    _ = Real.exp (∑ i ∈ T, c i) := (Real.exp_sum T c).symm
    _ ≤ Real.exp (∑' i, c i) := Real.exp_le_exp.mpr (hcs.sum_le_tsum T fun i _ => hc0 i)

end EulerBookkeeping
end TateGlobal
end NumberField
