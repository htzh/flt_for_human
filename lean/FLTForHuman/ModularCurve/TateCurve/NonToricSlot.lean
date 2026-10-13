/-
  The non-toric slot extension of the `tateCurve` twins: `hasSum_expand_gen` and
  the single-index expansions `expand_X'` / `xfun_single` / `yfun_single`, the
  divisor reorganisations `sum_sum_divisors_{pos,neg,diag}`, the `Slot` block
  (`C_mul_X_pow`, `X_pow_pow_mul_single`, `single_inv`, the `xTerm`/`yTerm`
  slot lemmas, `s₁_X_pow'`), and the `SlotMain` block (`hasSum_xTerm_slot`,
  `hasSum_yTerm_slot`, `sum_split_zero`) ending in the two non-toric kernels
  `pointX_slot` / `pointY_slot`.

  FLT provenance, pinned `aa2d8b3`: the extension carried by the twin pair
  `S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_{fst,snd}.lean`;
  the representative transcription source is
  `P2M/Sol/S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean`
  (1,343 lines), pin lines 758-1335. See
  topics/modularCurve/WORKORDER-F2-tate-curve-twins.md.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean

  Transcribed whole (playbook §2.3); the pin's bare `import Mathlib` is replaced by
  the specific mathlib modules, the `p2m_*` commands, the outer
  `P2MW.S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst` frame and
  the final public `solution` are dropped, and the pin's two per-declaration
  heartbeat-bump markers are removed (the port iterates at
  the low cap). Names, namespaces and the pin's `open` lines are kept verbatim.
  `coeff_slotSubst_tateUnivX` / `_tateUnivY` come from the already-ported
  `ModularCurve.TateSlots.SlotCoeff` engine, qualified in the two `point*_slot`
  proofs (the pin reached them through their public `Theorems/` wrappers).

  The two extension kernels `pointX_slot` and `pointY_slot` are additionally
  promoted to public `ModularCurve.TateCurve.<kernel>` with the binders of their
  `Theorems/` wrappers (work order §3.2); the facade
  `ModularCurve.<headline>` is the manager's.
-/
import FLTForHuman.Algebra.LaurentSeriesXAdic
import FLTForHuman.TateCurve.QSeries
import FLTForHuman.TateCurve.PointSeries
import FLTForHuman.ModularForms.KatzLevelOne
import FLTForHuman.ModularCurve.Defs.KatzLevelP
import FLTForHuman.ModularCurve.Defs.KatzLevelPCusps
import FLTForHuman.ModularCurve.Defs.TateSlots
import FLTForHuman.ModularCurve.TateCurve.Bridge
import FLTForHuman.ModularCurve.TateSlots.SlotCoeff

set_option autoImplicit false

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
namespace BridgeX

variable {F : Type*} [Field F]

-- pin: hasSum_expand_gen (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:765)
theorem hasSum_expand_gen (N : ℕ → ℕ) (hN : ∀ m, m < N m) (g : ℕ → PowerSeries F)
    (hg : ∀ m, PowerSeries.coeff 0 (g m) = 0) :
    HasSum (fun m => expand F (N m) (Nat.zero_lt_of_lt (hN m)) (ofPowerSeries ℤ F (g m)))
      (ofPowerSeries ℤ F (PowerSeries.mk fun n =>
        ∑ m ∈ Finset.range (n + 1), if N m ∣ n then PowerSeries.coeff (n / N m) (g m) else 0)) := by
  have hcoeffE : ∀ m (i : ℤ), (expand F (N m) (Nat.zero_lt_of_lt (hN m)) (ofPowerSeries ℤ F (g m))).coeff i ≠ 0 →
      ((N m : ℕ) : ℤ) ∣ i ∧ 0 < i := by
    intro m i h
    rw [expand_ofPowerSeries_coeff] at h
    split_ifs at h with hc
    · refine ⟨hc.1, ?_⟩
      rcases hc.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply h
        subst heq
        rw [Int.zero_ediv, Int.toNat_zero]
        exact hg m
    · exact absurd rfl h
  apply hasSum_of_coeff
  · intro D
    refine (Set.finite_lt_nat D.toNat).subset ?_
    rintro m ⟨i, hi, hne⟩
    obtain ⟨hdvd, hipos⟩ := hcoeffE m i hne
    have hle : ((N m : ℕ) : ℤ) ≤ i := Int.le_of_dvd hipos hdvd
    have := hN m
    show m < D.toNat
    omega
  · intro i
    rw [PowerSeries.coeff_coe]
    split_ifs with hi
    · symm
      apply finsum_eq_zero_of_forall_eq_zero
      intro m
      by_contra hne
      have := (hcoeffE m i hne).2
      omega
    · push Not at hi
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      rw [Int.natAbs_natCast, PowerSeries.coeff_mk]
      symm
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [expand_ofPowerSeries_coeff]
        by_cases hdvd : N m ∣ n
        · rw [ite_eq_left ⟨Int.natCast_dvd_natCast.mpr hdvd, by positivity⟩, ite_eq_left hdvd]
          congr 2
          try rw [← Int.natCast_div, Int.toNat_natCast]
        · rw [ite_eq_right (fun h => hdvd (Int.natCast_dvd_natCast.mp h.1)), ite_eq_right hdvd]
      · intro m hm
        rw [Function.mem_support] at hm
        obtain ⟨hdvd, hipos⟩ := hcoeffE m _ hm
        have hle : ((N m : ℕ) : ℤ) ≤ n := Int.le_of_dvd hipos hdvd
        have := hN m
        simp only [Finset.coe_range, Set.mem_Iio]
        omega

-- pin: expand_X' (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:821)
theorem expand_X' (N : ℕ) (hN : 0 < N) :
    expand F N hN (single 1 1) = (single (N : ℤ) (1 : F) : LaurentSeries F) := by
  rw [expand_single, mul_one]

-- pin: xfun_single (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:825)
theorem xfun_single (N : ℕ) (hN : 0 < N) (a : F) :
    TateCurve.xfun (single (N : ℤ) a : LaurentSeries F)
      = expand F N hN (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * a ^ k)) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F N hN).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = single (N : ℤ) 1 := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X']
  have hC : φ (PowerSeries.C a) = HahnSeries.C a := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C]
  have hCX : HahnSeries.C a * single (N : ℤ) (1 : F) = single (N : ℤ) a := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  have h1 : (1 : LaurentSeries F) - single (N : ℤ) a ≠ 0 := one_sub_single_ne_zero hN a
  have key := congrArg φ (xSeries_identity a)
  simp only [map_mul, map_pow, map_sub, map_one, hX, hC, hCX] at key
  rw [TateCurve.xfun, eq_comm, eq_div_iff (pow_ne_zero 2 h1)]
  show φ _ * _ = _
  linear_combination key

-- pin: yfun_single (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:842)
theorem yfun_single (N : ℕ) (hN : 0 < N) (a : F) :
    TateCurve.yfun (single (N : ℤ) a : LaurentSeries F)
      = expand F N hN (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * a ^ k)) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F N hN).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = single (N : ℤ) 1 := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X']
  have hC : φ (PowerSeries.C a) = HahnSeries.C a := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C]
  have hCX : HahnSeries.C a * single (N : ℤ) (1 : F) = single (N : ℤ) a := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  have h1 : (1 : LaurentSeries F) - single (N : ℤ) a ≠ 0 := one_sub_single_ne_zero hN a
  have key := congrArg φ (ySeries_identity a)
  simp only [map_mul, map_pow, map_sub, map_one, hX, hC, hCX] at key
  rw [TateCurve.yfun, eq_comm, eq_div_iff (pow_ne_zero 3 h1)]
  show φ _ * _ = _
  linear_combination key

section Reindex

variable {A : Type*} [AddCommMonoid A] (p j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) (g : ℕ → A)
include hj hjp

-- pin: sum_sum_divisors_pos (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:864)
theorem sum_sum_divisors_pos :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n = p * M + j * e then g e else 0)
      = ∑ m ∈ Finset.range (n + 1), (if 0 < m ∧ (p * m + j) ∣ n then g (n / (p * m + j)) else 0) := by
  classical
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp
  have hL : ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n = p * M + j * e then g e else 0)
      = ∑ x ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun x => x.2 ∈ x.1.divisors ∧ n = p * x.1 + j * x.2), g x.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors] at hM ⊢
    constructor
    · rintro ⟨⟨hd, hM0⟩, he⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd
      exact ⟨by omega, ⟨hd, hM0⟩, he⟩
    · rintro ⟨-, hd, he⟩
      exact ⟨hd, he⟩
  have hR : ∑ m ∈ Finset.range (n + 1), (if 0 < m ∧ (p * m + j) ∣ n then g (n / (p * m + j)) else 0)
      = ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m ∧ (p * m + j) ∣ n), g (n / (p * m + j)) := by
    rw [Finset.sum_filter]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun x => x.1 / x.2) (fun m => (m * (n / (p * m + j)), n / (p * m + j)))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hMn, -⟩, ⟨⟨m, rfl⟩, hM0⟩, hn⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    have hmle : m ≤ e * m := Nat.le_mul_of_pos_left m he0
    rw [Nat.mul_div_cancel_left m he0]
    exact ⟨by omega, hm0, ⟨e, by rw [hn]; ring⟩⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hm ⊢
    obtain ⟨hmn, hm0, ⟨e, he⟩⟩ := hm
    have hN0 : 0 < p * m + j := by omega
    have he' : n / (p * m + j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    have hele : e ≤ n := by rw [he]; exact Nat.le_mul_of_pos_left e hN0
    have hpm : m ≤ p * m := Nat.le_mul_of_pos_left m hp
    have hmle : m * e ≤ n := by
      rw [he, mul_comm (p * m + j) e, mul_comm m e]
      exact Nat.mul_le_mul_left e (by omega)
    rw [he']
    exact ⟨⟨by omega, by omega⟩, ⟨Dvd.intro_left m rfl, Nat.mul_ne_zero hm0.ne' he0.ne'⟩, by rw [he]; ring⟩
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m, rfl⟩, hM0⟩, hn⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hN0 : 0 < p * m + j := by omega
    have hq : n / (p * m + j) = e := by
      rw [hn, show p * (e * m) + j * e = e * (p * m + j) by ring, Nat.mul_div_cancel e hN0]
    simp only [Nat.mul_div_cancel_left m he0, hq, mul_comm m e]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmn, hm0, ⟨e, he⟩⟩ := hm
    have hN0 : 0 < p * m + j := by omega
    have he' : n / (p * m + j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    simp only [he', Nat.mul_div_cancel m he0]
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m, rfl⟩, hM0⟩, hn⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hN0 : 0 < p * m + j := by omega
    simp only
    rw [Nat.mul_div_cancel_left m he0, hn, show p * (e * m) + j * e = e * (p * m + j) by ring,
      Nat.mul_div_cancel e hN0]

end Reindex

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
namespace BridgeX

variable {F : Type*} [Field F]

section Reindex2

variable {A : Type*} [AddCommMonoid A] (p j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) (g : ℕ → A)
include hj hjp

-- pin: sum_sum_divisors_neg (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:958)
theorem sum_sum_divisors_neg (hn : 0 < n) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n + j * e = p * M then g e else 0)
      = ∑ m ∈ Finset.range (n + 1), (if (p * (m + 1) - j) ∣ n then g (n / (p * (m + 1) - j)) else 0) := by
  classical
  have _ : 0 < j := hj
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp

  have hjle : ∀ m' : ℕ, 0 < m' → j ≤ p * m' := fun m' hm' =>
    (le_of_lt hjp).trans (Nat.le_mul_of_pos_right p hm')
  have hNpos : ∀ m' : ℕ, 0 < m' → 0 < p * m' - j := fun m' hm' => by
    have : j < p * m' := lt_of_lt_of_le hjp (Nat.le_mul_of_pos_right p hm')
    omega

  have hmN : ∀ m' : ℕ, 0 < m' → m' ≤ p * m' - j := fun m' hm' => by
    have h1 : j + 1 ≤ p := hjp
    have : (j + 1) * m' ≤ p * m' := Nat.mul_le_mul_right m' h1
    have : j * m' + m' ≤ p * m' := by rw [Nat.succ_mul] at this; omega
    have : j ≤ j * m' := Nat.le_mul_of_pos_right j hm'
    omega
  have hL : ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n + j * e = p * M then g e else 0)
      = ∑ x ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun x => x.2 ∈ x.1.divisors ∧ n + j * x.2 = p * x.1), g x.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors] at hM ⊢
    constructor
    · rintro ⟨⟨hd, hM0⟩, he⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd
      exact ⟨by omega, ⟨hd, hM0⟩, he⟩
    · rintro ⟨-, hd, he⟩
      exact ⟨hd, he⟩
  have hR : ∑ m ∈ Finset.range (n + 1), (if (p * (m + 1) - j) ∣ n then g (n / (p * (m + 1) - j)) else 0)
      = ∑ m ∈ (Finset.range (n + 1)).filter (fun m => (p * (m + 1) - j) ∣ n), g (n / (p * (m + 1) - j)) := by
    rw [Finset.sum_filter]
  rw [hL, hR]

  have hsolve : ∀ e m' : ℕ, 0 < m' → n + j * e = p * (e * m') → n = e * (p * m' - j) := by
    intro e m' hm' h
    have := hjle m' hm'
    zify [this] at h ⊢
    linear_combination h
  refine Finset.sum_nbij' (fun x => x.1 / x.2 - 1)
    (fun m => ((m + 1) * (n / (p * (m + 1) - j)), n / (p * (m + 1) - j))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hMn, -⟩, ⟨⟨m', rfl⟩, hM0⟩, hne⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    have hmle : m' ≤ e * m' := Nat.le_mul_of_pos_left m' he0
    rw [Nat.mul_div_cancel_left m' he0, Nat.sub_add_cancel hm']
    exact ⟨by omega, ⟨e, by rw [hsolve e m' hm' hne, mul_comm]⟩⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hm ⊢
    obtain ⟨hmn, ⟨e, he⟩⟩ := hm
    have hN0 := hNpos (m + 1) (Nat.succ_pos m)
    have he' : n / (p * (m + 1) - j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    have hele : e ≤ n := by rw [he]; exact Nat.le_mul_of_pos_left e hN0
    have hMle : (m + 1) * e ≤ n := by
      rw [he, mul_comm (p * (m + 1) - j) e, mul_comm (m + 1) e]
      exact Nat.mul_le_mul_left e (hmN (m + 1) (Nat.succ_pos m))
    rw [he']
    refine ⟨⟨by omega, by omega⟩, ⟨Dvd.intro_left (m + 1) rfl, Nat.mul_ne_zero (Nat.succ_ne_zero m) he0.ne'⟩, ?_⟩
    have := hjle (m + 1) (Nat.succ_pos m)
    zify [this] at he ⊢
    linear_combination he
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m', rfl⟩, hM0⟩, hne⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    have hq : n / (p * m' - j) = e := by
      rw [hsolve e m' hm' hne, Nat.mul_div_cancel e (hNpos m' hm')]
    simp only [Nat.mul_div_cancel_left m' he0, Nat.sub_add_cancel hm', hq, mul_comm m' e]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmn, ⟨e, he⟩⟩ := hm
    have hN0 := hNpos (m + 1) (Nat.succ_pos m)
    have he' : n / (p * (m + 1) - j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    simp only [he', Nat.mul_div_cancel (m + 1) he0, Nat.add_sub_cancel]
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m', rfl⟩, hM0⟩, hne⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    simp only
    rw [Nat.mul_div_cancel_left m' he0, Nat.sub_add_cancel hm', hsolve e m' hm' hne,
      Nat.mul_div_cancel e (hNpos m' hm')]

omit hj hjp in

-- pin: sum_sum_divisors_diag (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1052)
theorem sum_sum_divisors_diag (hp : 0 < p) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n = p * M then g e else 0)
      = if p ∣ n then ∑ e ∈ (n / p).divisors, g e else 0 := by
  classical
  have h1 : ∀ M, ∑ e ∈ M.divisors, (if n = p * M then g e else 0)
      = if n = p * M then ∑ e ∈ M.divisors, g e else 0 := by
    intro M; split_ifs <;> simp
  simp_rw [h1]
  by_cases hpn : p ∣ n
  · obtain ⟨M₀, rfl⟩ := hpn
    rw [ite_eq_left (Dvd.intro M₀ rfl), Nat.mul_div_cancel_left _ hp]
    have h2 : ∀ M, (p * M₀ = p * M) = (M₀ = M) := fun M => propext (Nat.mul_right_inj hp.ne')
    simp_rw [h2]
    rw [Finset.sum_ite_eq, ite_eq_left]
    simp only [Finset.mem_range]
    have := Nat.le_mul_of_pos_left M₀ hp
    omega
  · rw [ite_eq_right hpn]
    refine Finset.sum_eq_zero fun M _ => ?_
    rw [ite_eq_right]
    rintro rfl
    exact hpn (Dvd.intro M rfl)

end Reindex2

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
namespace BridgeX

variable {F : Type*} [Field F]

section Slot

variable (p j : ℕ) (hj : 0 < j) (hjp : j < p) (c : F) (hc : c ≠ 0)
include hj hjp

omit hj hjp in
-- pin: C_mul_X_pow (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1099)
theorem C_mul_X_pow : HahnSeries.C c * (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j = single (j : ℤ) c := by
  rw [X_pow_eq_single, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

omit hj hjp in
-- pin: X_pow_pow_mul_single (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1103)
theorem X_pow_pow_mul_single (m : ℕ) :
    ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ m * single (j : ℤ) c = single ((p * m + j : ℕ) : ℤ) c := by
  rw [← pow_mul, X_pow_eq_single, HahnSeries.single_mul_single, one_mul]
  push_cast
  ring_nf

include hc in
omit hj hjp in
-- pin: single_inv (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1111)
theorem single_inv : (single (j : ℤ) c : LaurentSeries F)⁻¹ = single (-(j : ℤ)) c⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [HahnSeries.single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc]
  rfl

include hc in
-- pin: X_pow_pow_mul_single_inv (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1117)
theorem X_pow_pow_mul_single_inv (m : ℕ) :
    ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹
      = single ((p * (m + 1) - j : ℕ) : ℤ) c⁻¹ := by
  have _ : 0 < j := hj
  have hle : j ≤ p * (m + 1) := (le_of_lt hjp).trans (Nat.le_mul_of_pos_right p (Nat.succ_pos m))
  rw [single_inv j c hc, ← pow_mul, X_pow_eq_single, HahnSeries.single_mul_single, one_mul]
  push_cast [hle]
  ring_nf

-- pin: lt_expPos (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1125)
theorem lt_expPos (m : ℕ) : m < p * m + j := by
  have : m ≤ p * m := Nat.le_mul_of_pos_left m (lt_of_le_of_lt (Nat.zero_le j) hjp)
  omega

-- pin: lt_expNeg (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1129)
theorem lt_expNeg (m : ℕ) : m < p * (m + 1) - j := by
  have _ : 0 < j := hj
  have h1 : (j + 1) * (m + 1) ≤ p * (m + 1) := Nat.mul_le_mul_right (m + 1) hjp
  have h2 : j ≤ j * (m + 1) := Nat.le_mul_of_pos_right j (Nat.succ_pos m)
  rw [Nat.succ_mul] at h1
  omega

include hc in
-- pin: xTerm_slot_natCast (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1136)
theorem xTerm_slot_natCast (m : ℕ) :
    TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ)
      = expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c ^ k)) := by
  have _ : c ≠ 0 := hc
  rw [xTerm_natCast, X_pow_pow_mul_single, xfun_single]

include hc in
-- pin: xTerm_slot_neg (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1143)
theorem xTerm_slot_neg (m : ℕ) :
    TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1))
      = expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c⁻¹ ^ k)) := by
  have hw : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 0 := by
    rw [X_pow_pow_mul_single_inv p j hj hjp c hc]; exact HahnSeries.single_ne_zero (inv_ne_zero hc)
  have hw1 : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 1 := by
    intro h
    apply one_sub_single_ne_zero (F := F) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹
    rw [← X_pow_pow_mul_single_inv p j hj hjp c hc, h, sub_self]
  have hz : (-((m : ℤ) + 1)) = -(((m + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [TateCurve.xTerm, hz, zpow_neg, zpow_natCast, ← inv_inv (single (j : ℤ) c), ← mul_inv,
    TateCurve.xfun_inv hw hw1, X_pow_pow_mul_single_inv p j hj hjp c hc,
    xfun_single _ (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))]

include hc in
-- pin: yTerm_slot_natCast (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1159)
theorem yTerm_slot_natCast (m : ℕ) :
    TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ)
      = expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * c ^ k)) := by
  have _ : c ≠ 0 := hc
  rw [yTerm_natCast, X_pow_pow_mul_single, yfun_single]

include hc in
-- pin: yTerm_slot_neg (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1166)
theorem yTerm_slot_neg (m : ℕ) :
    TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1))
      = expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => -((((k + 1).choose 2 : ℕ) : F) * c⁻¹ ^ k))) := by
  have hw : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 0 := by
    rw [X_pow_pow_mul_single_inv p j hj hjp c hc]; exact HahnSeries.single_ne_zero (inv_ne_zero hc)
  have hw1 : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 1 := by
    intro h
    apply one_sub_single_ne_zero (F := F) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹
    rw [← X_pow_pow_mul_single_inv p j hj hjp c hc, h, sub_self]
  have hz : (-((m : ℤ) + 1)) = -(((m + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [TateCurve.yTerm, hz, zpow_neg, zpow_natCast, ← inv_inv (single (j : ℤ) c), ← mul_inv,
    TateCurve.yfun_inv hw hw1, X_pow_pow_mul_single_inv p j hj hjp c hc,
    yfun_single _ (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹, xfun_single _ (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹,
    ← map_neg, ← map_sub, ← map_neg, ← map_sub]
  congr 2
  ext k
  simp only [map_neg, map_sub, PowerSeries.coeff_mk, Nat.choose_succ_succ', Nat.choose_one_right, Nat.cast_add]
  ring

-- pin: s₁_X_pow' (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1186)
theorem s₁_X_pow' (hp : 0 < p) :
    TateCurve.s₁ ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      = ofPowerSeries ℤ F (PowerSeries.mk fun n => if p ∣ n then ∑ e ∈ (n / p).divisors, (e : F) else 0) := by
  have _ : 0 < j := hj
  have _ : j < p := hjp
  rw [s₁_X_pow p hp]
  symm
  rw [ofPowerSeries_eq_expand p hp (PowerSeries.mk fun n => if p ∣ n then ∑ e ∈ (n / p).divisors, (e : F) else 0)
    (fun m hm => by rw [PowerSeries.coeff_mk, ite_eq_right hm])]
  congr 2
  ext M
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ite_eq_left (Dvd.intro M rfl),
    Nat.mul_div_cancel_left _ hp]

end Slot

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
namespace BridgeX

variable {F : Type*} [Field F]

section SlotMain

variable (p j : ℕ) (hj : 0 < j) (hjp : j < p) (c : F) (hc : c ≠ 0)
include hj hjp hc

-- pin: hasSum_xTerm_slot (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1221)
theorem hasSum_xTerm_slot :
    HasSum (fun n : ℤ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) n)
      (ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * m + j) ∣ n then ((n / (p * m + j) : ℕ) : F) * c ^ (n / (p * m + j)) else 0)
        + ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * (m + 1) - j) ∣ n then ((n / (p * (m + 1) - j) : ℕ) : F) * c⁻¹ ^ (n / (p * (m + 1) - j)) else 0)) := by
  have hpos := hasSum_expand_gen (F := F) (fun m => p * m + j) (lt_expPos p j hj hjp)
    (fun _ => PowerSeries.mk fun k => (k : F) * c ^ k) (fun _ => by simp)
  have hneg := hasSum_expand_gen (F := F) (fun m => p * (m + 1) - j) (lt_expNeg p j hj hjp)
    (fun _ => PowerSeries.mk fun k => (k : F) * c⁻¹ ^ k) (fun _ => by simp)
  simp only [PowerSeries.coeff_mk] at hpos hneg
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · have hfun : (fun m : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ))
        = fun m => expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c ^ k)) := by
      funext m; exact xTerm_slot_natCast p j hj hjp c hc m
    rw [hfun]; exact hpos
  · have hfun : (fun m : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1)))
        = fun m => expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c⁻¹ ^ k)) := by
      funext m; exact xTerm_slot_neg p j hj hjp c hc m
    rw [hfun]; exact hneg

-- pin: hasSum_yTerm_slot (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1244)
theorem hasSum_yTerm_slot :
    HasSum (fun n : ℤ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) n)
      (ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * m + j) ∣ n then (((n / (p * m + j)).choose 2 : ℕ) : F) * c ^ (n / (p * m + j)) else 0)
        + ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * (m + 1) - j) ∣ n then -(((((n / (p * (m + 1) - j)) + 1).choose 2 : ℕ) : F)
            * c⁻¹ ^ (n / (p * (m + 1) - j))) else 0)) := by
  have hpos := hasSum_expand_gen (F := F) (fun m => p * m + j) (lt_expPos p j hj hjp)
    (fun _ => PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * c ^ k) (fun _ => by simp)
  have hneg := hasSum_expand_gen (F := F) (fun m => p * (m + 1) - j) (lt_expNeg p j hj hjp)
    (fun _ => PowerSeries.mk fun k => -((((k + 1).choose 2 : ℕ) : F) * c⁻¹ ^ k)) (fun _ => by simp)
  simp only [PowerSeries.coeff_mk] at hpos hneg
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · have hfun : (fun m : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ))
        = fun m => expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * c ^ k)) := by
      funext m; exact yTerm_slot_natCast p j hj hjp c hc m
    rw [hfun]; exact hpos
  · have hfun : (fun m : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1)))
        = fun m => expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => -((((k + 1).choose 2 : ℕ) : F) * c⁻¹ ^ k))) := by
      funext m; exact yTerm_slot_neg p j hj hjp c hc m
    rw [hfun]; exact hneg

omit hc in

-- pin: sum_split_zero (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1270)
theorem sum_split_zero {A : Type*} [AddCommMonoid A] (n : ℕ) (v : ℕ → A) :
    ∑ m ∈ Finset.range (n + 1), (if (p * m + j) ∣ n then v (n / (p * m + j)) else 0)
      = (if j ∣ n then v (n / j) else 0)
        + ∑ m ∈ Finset.range (n + 1), (if 0 < m ∧ (p * m + j) ∣ n then v (n / (p * m + j)) else 0) := by
  have _ : 0 < j := hj
  have _ : j < p := hjp
  rw [Finset.sum_range_succ', Finset.sum_range_succ', mul_zero, zero_add]
  simp only [Nat.succ_pos, true_and, lt_self_iff_false, false_and, ite_false, add_zero]
  rw [add_comm]

end SlotMain


-- pin: pointX_slot (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1282)
theorem pointX_slot (p : ℕ) [NeZero p] (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (nonToricPoint F p c j).1 := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [C_mul_X_pow, TateCurve.pointX, (hasSum_xTerm_slot p j hj hjp (c : F) hc0).tsum_eq, s₁_X_pow' p j hj hjp hp,
    nonToricPoint_fst, two_mul, ← map_add, ← map_add, ← map_sub]
  congr 1
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mk, TateSlots.coeff_slotSubst_tateUnivX p c j hj hjp n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sum_split_zero p j hj hjp n (fun k => ((k : ℕ) : F) * (c : F) ^ k)]
    conv_rhs => simp only [mul_add, mul_sub, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_sum_divisors_pos p j hj hjp n (fun e => (e : F) * (c : F) ^ e),
      sum_sum_divisors_neg p j hj hjp n (fun e => (e : F) * ((c⁻¹ : Fˣ) : F) ^ e) hn,
      sum_sum_divisors_diag p n (fun e => (e : F) * 2) hp]
    simp only [Units.val_inv_eq_inv_val, ← Finset.sum_mul]
    split_ifs <;> ring


-- pin: pointY_slot (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1305)
theorem pointY_slot (p : ℕ) [NeZero p] (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointY ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (nonToricPoint F p c j).2 := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [C_mul_X_pow, TateCurve.pointY, (hasSum_yTerm_slot p j hj hjp (c : F) hc0).tsum_eq, s₁_X_pow' p j hj hjp hp,
    nonToricPoint_snd, ← map_add, ← map_add]
  congr 1
  ext n
  simp only [map_add, PowerSeries.coeff_mk, TateSlots.coeff_slotSubst_tateUnivY p c j hj hjp n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sum_split_zero p j hj hjp n (fun k => (((k : ℕ).choose 2 : ℕ) : F) * (c : F) ^ k)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_sum_divisors_pos p j hj hjp n (fun e => ((e.choose 2 : ℕ) : F) * (c : F) ^ e),
      sum_sum_divisors_neg p j hj hjp n (fun e => (((e + 1).choose 2 : ℕ) : F) * ((c⁻¹ : Fˣ) : F) ^ e) hn,
      sum_sum_divisors_diag p n (fun e => (e : F)) hp]
    have hneg : ∑ m ∈ Finset.range (n + 1),
        (if p * (m + 1) - j ∣ n then -((((n / (p * (m + 1) - j) + 1).choose 2 : ℕ) : F) * (c : F)⁻¹ ^ (n / (p * (m + 1) - j))) else 0)
        = -∑ m ∈ Finset.range (n + 1),
        (if p * (m + 1) - j ∣ n then (((n / (p * (m + 1) - j) + 1).choose 2 : ℕ) : F) * (c : F)⁻¹ ^ (n / (p * (m + 1) - j)) else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    simp only [Units.val_inv_eq_inv_val, hneg]
    split_ifs <;> ring

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve.TateCurve

-- pin: pointX_slot (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1282)
theorem pointX_slot (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).1 :=
  ModularCurve.BridgeX.pointX_slot p c j hj hjp

-- pin: pointY_slot (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:1305)
theorem pointY_slot (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointY ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).2 :=
  ModularCurve.BridgeX.pointY_slot p c j hj hjp

end ModularCurve.TateCurve
