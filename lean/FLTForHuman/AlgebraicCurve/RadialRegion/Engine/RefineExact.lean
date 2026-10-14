/-
The `RadialRefine` development: a radial region refines to any finite break set.

The engine behind `AlgebraicCurve.RadialRegion.exists_refine_exact` — the merged
break finset `brk`, its order embedding `emb`, and the refinement `refineExact`
with its q/r/K/Kint/loop/range-φs/ncard/no-interior-break/arc-subset conclusions.
Transcribed verbatim from the pinned FLT `aa2d8b3` solution file; the pin's
`private` helpers stay `private` and every pin-public declaration stays public.
Public but unwired (tier 3): the headline lives in
`FLTForHuman/AlgebraicCurve/RadialRegion/RefineExact.lean`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean>
-/
import FLTForHuman.AlgebraicCurve.Defs.CellDissection
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

open AlgebraicCurve

namespace AlgebraicCurve.RadialRegion

noncomputable section

namespace RadialRefine

section Refine

variable (R : RadialRegion) (T : Finset ℝ)

private def brk : Finset ℝ := Finset.univ.image R.φs ∪ T

private theorem zero_mem_brk : (0 : ℝ) ∈ brk R T := by
  show (0 : ℝ) ∈ Finset.univ.image R.φs ∪ T
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, R.hφ0⟩))

private theorem two_pi_mem_brk : (2 * Real.pi) ∈ brk R T := by
  show (2 * Real.pi) ∈ Finset.univ.image R.φs ∪ T
  exact Finset.mem_union.mpr
    (Or.inl (Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, R.hφN⟩))

private theorem mem_brk_of_φs (i : Fin (R.N + 1)) : R.φs i ∈ brk R T := by
  show R.φs i ∈ Finset.univ.image R.φs ∪ T
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

private theorem brk_nonneg (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    ∀ z ∈ brk R T, 0 ≤ z := by
  intro z hz
  have hz' : z ∈ Finset.univ.image R.φs ∪ T := hz
  rcases Finset.mem_union.mp hz' with h | h
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
    rw [← R.hφ0]
    exact R.hmono.monotone (Fin.zero_le k)
  · exact (hT z h).1

private theorem brk_le (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    ∀ z ∈ brk R T, z ≤ 2 * Real.pi := by
  intro z hz
  have hz' : z ∈ Finset.univ.image R.φs ∪ T := hz
  rcases Finset.mem_union.mp hz' with h | h
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
    rw [← R.hφN]
    exact R.hmono.monotone (Fin.le_last k)
  · exact (hT z h).2

private def N' : ℕ := (brk R T).card - 1

private theorem brk_card : (brk R T).card = N' R T + 1 := by
  have h : 0 < (brk R T).card := Finset.card_pos.mpr ⟨0, zero_mem_brk R T⟩
  unfold N'
  omega

private def emb : Fin (N' R T + 1) → ℝ := ⇑((brk R T).orderEmbOfFin (brk_card R T))

private theorem emb_mem (i : Fin (N' R T + 1)) : emb R T i ∈ brk R T :=
  (brk R T).orderEmbOfFin_mem (brk_card R T) i

private theorem emb_surj {z : ℝ} (hz : z ∈ brk R T) : ∃ i, emb R T i = z := by
  have hz' : z ∈ Set.range ((brk R T).orderEmbOfFin (brk_card R T)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast hz
  obtain ⟨i, hi⟩ := hz'
  exact ⟨i, hi⟩

private theorem emb_strictMono : StrictMono (emb R T) :=
  ((brk R T).orderEmbOfFin (brk_card R T)).strictMono

private theorem emb_zero (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) : emb R T 0 = 0 := by
  have h1 := (brk R T).orderEmbOfFin_zero (brk_card R T) (Nat.succ_pos (N' R T))
  have h2 : (brk R T).min' ⟨0, zero_mem_brk R T⟩ = 0 :=
    le_antisymm ((brk R T).min'_le 0 (zero_mem_brk R T))
      ((brk R T).le_min' _ _ (brk_nonneg R T hT))
  rw [← h2]
  exact h1

private theorem emb_last (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    emb R T (Fin.last (N' R T)) = 2 * Real.pi := by
  have h1 := (brk R T).orderEmbOfFin_last (brk_card R T) (Nat.succ_pos (N' R T))
  have h2 : (brk R T).max' ⟨0, zero_mem_brk R T⟩ = 2 * Real.pi :=
    le_antisymm ((brk R T).max'_le _ _ (brk_le R T hT))
      ((brk R T).le_max' _ (two_pi_mem_brk R T))
  rw [← h2]
  exact h1

private theorem coe_brk : ((brk R T : Finset ℝ) : Set ℝ) = Set.range R.φs ∪ (T : Set ℝ) := by
  unfold brk
  simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]

private theorem range_emb : Set.range (emb R T) = Set.range R.φs ∪ (T : Set ℝ) := by
  unfold emb
  rw [Finset.range_orderEmbOfFin]
  exact coe_brk R T

private theorem harc (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) (k' : Fin (N' R T)) :
    ∃ k : Fin R.N,
      R.φs k.castSucc ≤ emb R T k'.castSucc ∧ emb R T k'.succ ≤ R.φs k.succ := by
  classical
  have hab : emb R T k'.castSucc < emb R T k'.succ := emb_strictMono R T Fin.castSucc_lt_succ
  set a := emb R T k'.castSucc with ha
  set b := emb R T k'.succ with hb
  have haS := emb_mem R T k'.castSucc
  have hbS := emb_mem R T k'.succ
  set lows : Finset (Fin (R.N + 1)) := Finset.univ.filter (fun k => R.φs k ≤ a)
    with hlows
  have hlne : lows.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [R.hφ0]
    exact brk_nonneg R T hT _ haS
  set k₀ : Fin (R.N + 1) := lows.max' hlne with hk₀def
  have hk₀ : R.φs k₀ ≤ a := (Finset.mem_filter.mp (lows.max'_mem hlne)).2
  have hk₀max : ∀ j : Fin (R.N + 1), R.φs j ≤ a → j ≤ k₀ := fun j hj =>
    lows.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  have hk₀lt : k₀ < Fin.last R.N := by
    rcases lt_or_eq_of_le (Fin.le_last k₀) with h | h
    · exact h
    · exfalso
      rw [h, R.hφN] at hk₀
      have hble := brk_le R T hT _ hbS
      linarith
  set k : Fin R.N := k₀.castPred hk₀lt.ne with hkdef
  have hkc : k.castSucc = k₀ := Fin.castSucc_castPred _ _
  refine ⟨k, by rw [hkc]; exact hk₀, ?_⟩
  have hlt : a < R.φs k.succ := by
    by_contra hcon
    push Not at hcon
    have h1 := hk₀max k.succ hcon
    rw [← hkc] at h1
    exact absurd Fin.castSucc_lt_succ (not_lt.mpr h1)
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := emb_surj R T (mem_brk_of_φs R T k.succ)
  have hj1 : k'.castSucc < j := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hlt
  have hj2 : j < k'.succ := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hcon
  rw [Fin.lt_def] at hj1 hj2
  rw [Fin.val_castSucc] at hj1
  rw [Fin.val_succ] at hj2
  omega

private theorem emb_consec (k' : Fin (N' R T)) :
    ∀ t ∈ brk R T, t ∉ Set.Ioo (emb R T k'.castSucc) (emb R T k'.succ) := by
  intro t ht hmem
  obtain ⟨j, hj⟩ := emb_surj R T ht
  have hj1 : k'.castSucc < j := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hmem.1
  have hj2 : j < k'.succ := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hmem.2
  rw [Fin.lt_def] at hj1 hj2
  rw [Fin.val_castSucc] at hj1
  rw [Fin.val_succ] at hj2
  omega

-- pin: refineExact (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:169)
noncomputable def refineExact (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) : RadialRegion where
  q := R.q
  r := R.r
  hcont := R.hcont
  hper := R.hper
  hpos := R.hpos
  N := N' R T
  φs := emb R T
  hφ0 := emb_zero R T hT
  hφN := emb_last R T hT
  hmono := emb_strictMono R T
  hC2 := fun k' => by
    obtain ⟨k, h1, h2⟩ := harc R T hT k'
    exact (R.hC2 k).mono (Set.Icc_subset_Icc h1 h2)

-- pin: refineExact_q (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:184)
theorem refineExact_q (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).q = R.q := rfl

-- pin: refineExact_r (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:187)
theorem refineExact_r (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).r = R.r := rfl

-- pin: refineExact_K (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:190)
theorem refineExact_K (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).K = R.K := rfl

-- pin: refineExact_Kint (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:193)
theorem refineExact_Kint (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).Kint = R.Kint := rfl

-- pin: refineExact_loop (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:196)
theorem refineExact_loop (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).loop = R.loop := rfl

-- pin: range_φs (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:199)
theorem range_φs (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    Set.range (refineExact R T hT).φs = Set.range R.φs ∪ (T : Set ℝ) :=
  range_emb R T

-- pin: N_add_one_ncard (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:203)
theorem N_add_one_ncard (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard := by
  rw [← coe_brk R T, Set.ncard_coe_finset]
  exact (brk_card R T).symm

-- pin: not_mem_Ioo_φs (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:208)
theorem not_mem_Ioo_φs (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) (k : Fin (refineExact R T hT).N) :
    ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
      t ∉ Set.Ioo ((refineExact R T hT).φs k.castSucc) ((refineExact R T hT).φs k.succ) := by
  intro t ht
  rw [← coe_brk R T] at ht
  exact emb_consec R T k t (Finset.mem_coe.mp ht)

-- pin: exists_arcIcc_subset (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:215)
theorem exists_arcIcc_subset (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi)
    (k' : Fin (refineExact R T hT).N) :
    ∃ k : Fin R.N, (refineExact R T hT).arcIcc k' ⊆ R.arcIcc k := by
  obtain ⟨k, h1, h2⟩ := harc R T hT k'
  exact ⟨k, Set.Icc_subset_Icc h1 h2⟩

end Refine

section Statement

open scoped Real
open Set

-- pin: exists_refine_exact (S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean:228)
theorem exists_refine_exact (R : RadialRegion) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * π) :
    ∃ R' : RadialRegion,
      R'.q = R.q ∧ R'.r = R.r ∧ R'.K = R.K ∧ R'.Kint = R.Kint ∧ R'.loop = R.loop ∧
      Set.range R'.φs = Set.range R.φs ∪ (T : Set ℝ) ∧
      R'.N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard ∧
      (∀ k' : Fin R'.N, ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
        t ∉ Ioo (R'.φs k'.castSucc) (R'.φs k'.succ)) ∧
      (∀ k' : Fin R'.N, ∃ k : Fin R.N, R'.arcIcc k' ⊆ R.arcIcc k) := by
  exact ⟨refineExact R T hT, refineExact_q R T hT, refineExact_r R T hT, refineExact_K R T hT,
    refineExact_Kint R T hT, refineExact_loop R T hT, range_φs R T hT, N_add_one_ncard R T hT,
    not_mem_Ioo_φs R T hT, exists_arcIcc_subset R T hT⟩

end Statement

end RadialRefine

end

end AlgebraicCurve.RadialRegion
