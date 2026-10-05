/-
The odd-order summing-set combinatorics (cluster H) of the explicit-Vélu port.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` files

* `P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
  (the canonical statement copy), and
* `P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean`
  (the proof bodies);

only proof bodies are adapted to mathlib `v4.34.0`. This module is cluster H; it
imports cluster G (`Velu/Discharge.lean`). `liftSummingSet_oddOrderSummingSet`
and `coordsOrZero_ratPointMap` are already public in `Velu/Engine.lean` and are
imported, not redeclared.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Discharge

open Polynomial Finset
open scoped Polynomial.Bivariate
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace WeierstrassCurve

/-! ### Prerequisites

Shared-prelude declarations that H consumes but that are not yet available in
`Velu/Engine.lean`, `Place/Dictionary.lean` or `Velu/Formula.lean` (the pin's
`IsOddVeluSet` block). They are transcribed verbatim from the pinned FLT file;
`spec/check_flt_statements.py` validates their statements against the pin. They
are gathered in this one delimited section so the manager's refactor round can
relocate them mechanically. `exists_some_of_ne_zero` is public in the pin; SET-1
transcribed a `private` copy in `Velu/Formula.lean` and SET-3 added this public
duplicate, which the H5r refactor round folded back to the single public copy in
`Velu/Formula.lean`, imported here. -/

section Prerequisites

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

variable {Q : W.toAffine.Point} {p : ℕ}

lemma y_ne_negY_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    y ≠ W.toAffine.negY x y := fun hy =>
  h2 (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)

lemma veluGy_ne_zero_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    W.veluGy x y ≠ 0 := by
  intro h0
  refine y_ne_negY_of_two_nsmul_ne_zero h h2 ?_
  have hkey : W.toAffine.negY x y = y + W.veluGy x y := by
    simp only [Affine.negY, veluGy]; ring
  rw [hkey, h0, add_zero]

end Prerequisites

lemma kw_vdcoog_some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    (Affine.Point.some x₁ y₁ h₁ : V.Point) = Affine.Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem kw_not_dvd_of_le_half_odd {p k : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) : ¬ p ∣ k ∧ ¬ p ∣ 2 * k := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  exact ⟨Nat.not_dvd_of_pos_of_lt (by omega) (by omega),
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)⟩

theorem kw_not_dvd_add_of_le_half_odd {p k k' : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2) :
    ¬ p ∣ k + k' := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

section AbstractCofixed

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {p : ℕ}

theorem kw_exists_nsmul_of_mem_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) {P : F × F}
    (hP : P ∈ W.oddOrderSummingSet Q n) :
    ∃ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y), 1 ≤ k ∧ k ≤ n ∧
      k • Q = Point.some x y h ∧ P = (x, y) ∧ (2 * k) • Q ≠ 0 := by
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  obtain ⟨hndvd, hndvd2⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk1 (hkn.trans hn)
  have hne : k • Q ≠ 0 := nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd
  obtain ⟨x, y, h, heq, hcoords⟩ := exists_some_of_ne_zero hne
  exact ⟨k, x, y, h, hk1, hkn, heq, by rw [← hkP, hcoords],
    nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd2⟩

theorem kw_nsmul_eq_of_xOrZero_eq_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2)
    (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2)
    {x y : F} {h : W.toAffine.Nonsingular x y} (heq : k • Q = Point.some x y h)
    {x' y' : F} {h' : W.toAffine.Nonsingular x' y'} (heq' : k' • Q = Point.some x' y' h')
    (hx : x = x') : k • Q = k' • Q := by
  rcases (Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hx with hPP | hPP
  · rw [heq, heq', hPP]
  · exfalso
    have hsum : (k + k') • Q = 0 := by rw [add_nsmul, heq, heq', hPP, _root_.neg_add_cancel]
    exact kw_not_dvd_add_of_le_half_odd hp3 hpodd hk1 hkn hk'1 hk'n
      (hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsum)

theorem kw_nsmul_injOn_odd (hp3 : 3 ≤ p) (hord : addOrderOf Q = p) {k k' : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2)
    (heq : k • Q = k' • Q) : k = k' := by
  have hhalf : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  wlog hle : k ≤ k' generalizing k k'
  · exact (this hk'1 hk'n hk1 hkn heq.symm (by omega)).symm
  have hsub : (k' - k) • Q = 0 := by
    have : (k' - k) • Q + k • Q = k • Q := by
      rw [← add_nsmul, Nat.sub_add_cancel hle, heq]
    exact add_right_cancel (this.trans (zero_add _).symm)
  have hdvd : p ∣ k' - k := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsub
  rcases Nat.eq_zero_or_pos (k' - k) with h0 | h0
  · omega
  · exact absurd hdvd (Nat.not_dvd_of_pos_of_lt h0 (by omega))

theorem kw_isOddVeluSet_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    W.IsOddVeluSet (W.oddOrderSummingSet Q n) where
  equation P hP := by
    obtain ⟨_, _, _, h, _, _, _, hPxy, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP
    rw [hPxy]; exact h.left
  gy_ne_zero P hP := by
    obtain ⟨k, x, y, h, _, _, heq, hPxy, h2k⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP
    rw [hPxy]
    exact veluGy_ne_zero_of_two_nsmul_ne_zero h fun h2 => h2k (by
      rw [two_mul, add_nsmul, heq, ← two_nsmul, h2])
  x_injOn P hP P' hP' hx := by
    obtain ⟨k, x, y, h, hk1, hkn, heq, hPxy, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP
    obtain ⟨k', x', y', h', hk'1, hk'n, heq', hP'xy, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP'
    subst hPxy; subst hP'xy
    have hQQ' := kw_nsmul_eq_of_xOrZero_eq_odd hp3 hpodd hord hk1 (hkn.trans hn)
      hk'1 (hk'n.trans hn) heq heq' hx
    exact congrArg Point.coordsOrZero (heq ▸ heq' ▸ hQQ')

theorem kw_card_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    (W.oddOrderSummingSet Q n).card = n := by
  have hinj : Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 n : Finset ℕ) := by
    intro k hk k' hk' hcoords
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    obtain ⟨hndvd, _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk.1 (hk.2.trans hn)
    obtain ⟨hndvd', _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk'.1 (hk'.2.trans hn)
    obtain ⟨x, y, h, heq, hc⟩ :=
      exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd (k := k))
    obtain ⟨x', y', h', heq', hc'⟩ :=
      exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd' (k := k'))
    have hx : x = x' :=
      congrArg Prod.fst (show ((x, y) : F × F) = (x', y') from hc ▸ hc' ▸ hcoords)
    exact kw_nsmul_injOn_odd hp3 hord hk.1 (hk.2.trans hn) hk'.1 (hk'.2.trans hn)
      (kw_nsmul_eq_of_xOrZero_eq_odd hp3 hpodd hord hk.1 (hk.2.trans hn) hk'.1
        (hk'.2.trans hn) heq heq' hx)
  rw [oddOrderSummingSet, Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel]

end AbstractCofixed

section OrdNonneg

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {p : ℕ}

theorem kw_veluX_oddOrderSummingSet_eq_sum_Icc_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) x
      = x + ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((Point.some x y hP + k • Q : W.toAffine.Point).xOrZero
            + (Point.some x y hP + -(k • Q) : W.toAffine.Point).xOrZero
            - 2 * (k • Q).xOrZero) := by
  set d := (p - 1) / 2
  have hSset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hx : ∀ A ∈ W.oddOrderSummingSet Q d, x ≠ A.1 := by
    intro A hA
    obtain ⟨k, a, b, h, _, _, heq, hAeq, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord le_rfl hA
    subst hAeq
    exact xOrZero_ne_of_not_mem_zmultiples hPmem
      (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
      (heq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  rw [W.veluX_eq_orbitSum hP.1 hSset.equation hx]
  congr 1
  have hcard := kw_card_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hIcc : (Finset.Icc 1 d).card = d := by rw [Nat.card_Icc]; omega
  have hinj : Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 d) := by
    rw [← Finset.card_image_iff]; exact hcard.trans hIcc.symm
  show ∑ A ∈ W.oddOrderSummingSet Q d, _ = _
  rw [oddOrderSummingSet, Finset.sum_image (fun a ha b hb => hinj ha hb)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  obtain ⟨hndvd, _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk.1 hk.2
  obtain ⟨a, b, hab, hkQeq, hkQc⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd)
  rw [hkQc]; dsimp only
  have hxk : x ≠ a := xOrZero_ne_of_not_mem_zmultiples hPmem
    (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
    (hkQeq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  have hPkQ : (Point.some x y hP + k • Q : W.toAffine.Point).xOrZero
      = W.toAffine.addX x a (W.toAffine.slope x a y b) := by
    rw [hkQeq, Point.add_of_X_ne hxk, Point.xOrZero_some]
  have hnegkQ : -(k • Q) =
      Point.some a (W.toAffine.negY a b) ((Affine.nonsingular_neg ..).mpr hab) := by
    rw [hkQeq]; rfl
  have hPmkQ : (Point.some x y hP + -(k • Q) : W.toAffine.Point).xOrZero
      = W.toAffine.addX x a (W.toAffine.slope x a y (W.toAffine.negY a b)) := by
    rw [hnegkQ, Point.add_of_X_ne hxk, Point.xOrZero_some]
  rw [hPkQ, hPmkQ, show (k • Q).xOrZero = a from by rw [hkQeq, Point.xOrZero_some]]

theorem kw_veluX_oddOrderSummingSet_eq_sum_range_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) x
      = (∑ j ∈ Finset.range p, (Point.some x y hP + j • Q : W.toAffine.Point).xOrZero)
        - 2 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k • Q).xOrZero := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  rw [kw_veluX_oddOrderSummingSet_eq_sum_Icc_odd hp3 hpodd hord hP hPmem]
  obtain ⟨d, hpeq, hd_def⟩ : ∃ d, p = 2 * d + 1 ∧ d = (p - 1) / 2 := ⟨(p - 1) / 2, by omega, rfl⟩
  rw [← hd_def, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    show ∀ a b c : F, a + (b - c) = a + b - c from fun a b c => (add_sub_assoc a b c).symm]
  congr 1
  have hsplit : Finset.range p = {0} ∪ Finset.Icc 1 d ∪ Finset.Icc (d + 1) (p - 1) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj1 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 d) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_singleton] at ha; rw [Finset.mem_Icc] at hb; omega
  have hdisj2 : Disjoint (({0} : Finset ℕ) ∪ Finset.Icc 1 d) (Finset.Icc (d + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at ha
    rw [Finset.mem_Icc] at hb; omega
  rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton,
    zero_nsmul, add_zero, Point.xOrZero_some]
  clear hd_def
  have hrefl : ∑ j ∈ Finset.Icc (d + 1) (p - 1),
        (Point.some x y hP + j • Q : W.toAffine.Point).xOrZero
      = ∑ k ∈ Finset.Icc 1 d,
        (Point.some x y hP + -(k • Q) : W.toAffine.Point).xOrZero := by
    refine Finset.sum_nbij' (fun j => p - j) (fun k => p - k)
      (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
      (fun k hk => by simp only [Finset.mem_Icc] at hk ⊢; omega)
      (fun j hj => by rw [Finset.mem_Icc] at hj; omega)
      (fun k hk => by rw [Finset.mem_Icc] at hk; omega)
      (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    congr 2
    have hpQ : p • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
    rw [← sub_nsmul_eq_neg_of_nsmul_eq_zero hpQ (k := p - j) (Nat.sub_le _ _)]
    congr 1; omega
  rw [hrefl]; ring

theorem kw_veluX_xOrZero_add_gen_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) :
    W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) (P + Q).xOrZero
      = W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) P.xOrZero := by
  have hQmem : Q ∈ AddSubgroup.zmultiples Q := AddSubgroup.mem_zmultiples Q
  have hP0 : P ≠ 0 := fun h => hPmem (h ▸ AddSubgroup.zero_mem _)
  obtain ⟨x, y, hns, rfl, -⟩ := exists_some_of_ne_zero hP0
  have hPQmem := not_mem_zmultiples_add hPmem hQmem
  have hPQ0 : (Point.some x y hns + Q : W.toAffine.Point) ≠ 0 :=
    add_ne_zero_of_not_mem_zmultiples hPmem hQmem
  obtain ⟨x', y', hns', heqPQ, -⟩ := exists_some_of_ne_zero hPQ0
  rw [heqPQ, Point.xOrZero_some, Point.xOrZero_some,
    kw_veluX_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns' (heqPQ ▸ hPQmem),
    kw_veluX_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns hPmem]
  congr 1
  calc ∑ j ∈ Finset.range p, (Point.some x' y' hns' + j • Q : W.toAffine.Point).xOrZero
      = ∑ j ∈ Finset.range p,
          ((Point.some x y hns + Q : W.toAffine.Point) + j • Q).xOrZero :=
        Finset.sum_congr rfl fun j _ => by rw [← heqPQ]
    _ = ∑ j ∈ Finset.range p, (Point.some x y hns + j • Q : W.toAffine.Point).xOrZero :=
        sum_range_addOrderOf_shift_invariant hord _ _

theorem kw_veluY_oddOrderSummingSet_eq_sum_Icc_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) x y
      = y + ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((Point.some x y hP + k • Q : W.toAffine.Point).coordsOrZero.2
            + (Point.some x y hP + -(k • Q) : W.toAffine.Point).coordsOrZero.2
            - (k • Q).coordsOrZero.2
            - W.toAffine.negY (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) := by
  set d := (p - 1) / 2
  have hSset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hx : ∀ A ∈ W.oddOrderSummingSet Q d, x ≠ A.1 := by
    intro A hA
    obtain ⟨k, a, b, h, _, _, heq, hAeq, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord le_rfl hA
    subst hAeq
    exact xOrZero_ne_of_not_mem_zmultiples hPmem
      (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
      (heq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  rw [W.veluY_eq_orbitSum_fieldRed hP.1 hSset.equation hx]
  congr 1
  have hcard := kw_card_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hIcc : (Finset.Icc 1 d).card = d := by rw [Nat.card_Icc]; omega
  have hinj : Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 d) := by
    rw [← Finset.card_image_iff]; exact hcard.trans hIcc.symm
  show ∑ A ∈ W.oddOrderSummingSet Q d, _ = _
  rw [oddOrderSummingSet, Finset.sum_image (fun a ha b hb => hinj ha hb)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  obtain ⟨hndvd, _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk.1 hk.2
  obtain ⟨a, b, hab, hkQeq, hkQc⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd)
  rw [hkQc]; dsimp only
  have hxk : x ≠ a := xOrZero_ne_of_not_mem_zmultiples hPmem
    (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
    (hkQeq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  have hPkQ : (Point.some x y hP + k • Q : W.toAffine.Point).coordsOrZero.2
      = W.toAffine.addY x a y (W.toAffine.slope x a y b) := by
    rw [hkQeq, Point.add_of_X_ne hxk, Point.coordsOrZero_some]
  have hnegkQ : -(k • Q) = Point.some a (W.toAffine.negY a b)
      ((Affine.nonsingular_neg ..).mpr hab) := by
    rw [hkQeq]; rfl
  have hPmkQ : (Point.some x y hP + -(k • Q) : W.toAffine.Point).coordsOrZero.2
      = W.toAffine.addY x a y (W.toAffine.slope x a y (W.toAffine.negY a b)) := by
    rw [hnegkQ, Point.add_of_X_ne hxk, Point.coordsOrZero_some]
  rw [hPkQ, hPmkQ]

theorem kw_veluY_oddOrderSummingSet_eq_sum_range_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) x y
      = (∑ j ∈ Finset.range p,
          (Point.some x y hP + j • Q : W.toAffine.Point).coordsOrZero.2)
        - ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((k • Q).coordsOrZero.2
            + W.toAffine.negY (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  rw [kw_veluY_oddOrderSummingSet_eq_sum_Icc_odd hp3 hpodd hord hP hPmem]
  obtain ⟨d, hpeq, hd_def⟩ : ∃ d, p = 2 * d + 1 ∧ d = (p - 1) / 2 := ⟨(p - 1) / 2, by omega, rfl⟩
  rw [← hd_def]
  simp only [sub_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    show ∀ a b c : F, a + (b - c) = a + b - c from fun a b c => (add_sub_assoc a b c).symm]
  congr 1
  have hsplit : Finset.range p = {0} ∪ Finset.Icc 1 d ∪ Finset.Icc (d + 1) (p - 1) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj1 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 d) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_singleton] at ha; rw [Finset.mem_Icc] at hb; omega
  have hdisj2 : Disjoint (({0} : Finset ℕ) ∪ Finset.Icc 1 d) (Finset.Icc (d + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at ha
    rw [Finset.mem_Icc] at hb; omega
  rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton,
    zero_nsmul, add_zero, Point.coordsOrZero_some]
  clear hd_def
  have hrefl : ∑ j ∈ Finset.Icc (d + 1) (p - 1),
        (Point.some x y hP + j • Q : W.toAffine.Point).coordsOrZero.2
      = ∑ k ∈ Finset.Icc 1 d,
        (Point.some x y hP + -(k • Q) : W.toAffine.Point).coordsOrZero.2 := by
    refine Finset.sum_nbij' (fun j => p - j) (fun k => p - k)
      (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
      (fun k hk => by simp only [Finset.mem_Icc] at hk ⊢; omega)
      (fun j hj => by rw [Finset.mem_Icc] at hj; omega)
      (fun k hk => by rw [Finset.mem_Icc] at hk; omega)
      (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    congr 3
    have hpQ : p • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
    rw [← sub_nsmul_eq_neg_of_nsmul_eq_zero hpQ (k := p - j) (Nat.sub_le _ _)]
    congr 1; omega
  rw [hrefl]; ring

theorem kw_veluY_coordsOrZero_add_gen_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) :
    W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) (P + Q).coordsOrZero.1
        (P + Q).coordsOrZero.2
      = W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) P.coordsOrZero.1 P.coordsOrZero.2 := by
  have hQmem : Q ∈ AddSubgroup.zmultiples Q := AddSubgroup.mem_zmultiples Q
  have hP0 : P ≠ 0 := fun h => hPmem (h ▸ AddSubgroup.zero_mem _)
  obtain ⟨x, y, hns, rfl, -⟩ := exists_some_of_ne_zero hP0
  have hPQmem := not_mem_zmultiples_add hPmem hQmem
  have hPQ0 : (Point.some x y hns + Q : W.toAffine.Point) ≠ 0 :=
    add_ne_zero_of_not_mem_zmultiples hPmem hQmem
  obtain ⟨x', y', hns', heqPQ, -⟩ := exists_some_of_ne_zero hPQ0
  rw [heqPQ, Point.coordsOrZero_some, Point.coordsOrZero_some,
    kw_veluY_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns' (heqPQ ▸ hPQmem),
    kw_veluY_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns hPmem]
  congr 1
  calc ∑ j ∈ Finset.range p, (Point.some x' y' hns' + j • Q : W.toAffine.Point).coordsOrZero.2
      = ∑ j ∈ Finset.range p,
          ((Point.some x y hns + Q : W.toAffine.Point) + j • Q).coordsOrZero.2 :=
        Finset.sum_congr rfl fun j _ => by rw [← heqPQ]
    _ = ∑ j ∈ Finset.range p, (Point.some x y hns + j • Q : W.toAffine.Point).coordsOrZero.2 :=
        sum_range_addOrderOf_shift_invariant hord
          (fun P => Point.coordsOrZero P |>.2) (Point.some x y hns)

theorem kw_veluDeficit_add_gen_odd (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)
    {P : W.toAffine.Point} (hPmem : P ∉ AddSubgroup.zmultiples Q) :
    W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        (P + Q).coordsOrZero.1 (P + Q).coordsOrZero.2
      = W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P.coordsOrZero.1 P.coordsOrZero.2 := by
  refine W.veluDeficit_congr ?_ (kw_veluY_coordsOrZero_add_gen_odd hp3 hpodd hord hPmem)
  rw [Point.coordsOrZero_fst, Point.coordsOrZero_fst]
  exact kw_veluX_xOrZero_add_gen_odd hp3 hpodd hord hPmem

theorem kw_veluDeficit_add_nsmul_odd (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)
    {P : W.toAffine.Point} (hPmem : P ∉ AddSubgroup.zmultiples Q) (n : ℕ) :
    W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        (P + n • Q).coordsOrZero.1 (P + n • Q).coordsOrZero.2
      = W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P.coordsOrZero.1 P.coordsOrZero.2 := by
  induction n with
  | zero => rw [zero_nsmul, add_zero]
  | succ m ih =>
    have hPm : P + m • Q ∉ AddSubgroup.zmultiples Q :=
      not_mem_zmultiples_add hPmem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) m)
    rw [succ_nsmul, ← add_assoc, kw_veluDeficit_add_gen_odd hp3 hpodd hord hPm, ih]

theorem kw_veluDeficit_eq_of_sub_mem_zmultiples_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {P P' : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) (hdiff : P' - P ∈ AddSubgroup.zmultiples Q) :
    W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P'.coordsOrZero.1 P'.coordsOrZero.2
      = W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P.coordsOrZero.1 P.coordsOrZero.2 := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hdiff
  have hpQ : (p : ℤ) • Q = 0 := by exact_mod_cast hord ▸ addOrderOf_nsmul_eq_zero Q
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  set n : ℕ := (k % (p : ℤ)).toNat with hn_def
  have hmod_nn := Int.emod_nonneg k hp_ne
  have hkQ : k • Q = n • Q := by
    conv_lhs => rw [show k = k % p + k / p * p from by
        rw [mul_comm]; exact (Int.emod_add_mul_ediv k p).symm,
      add_zsmul, mul_zsmul, hpQ, smul_zero, add_zero]
    rw [hn_def, ← natCast_zsmul, Int.toNat_of_nonneg hmod_nn]
  have hP'eq : P' = P + n • Q := by
    have h1 : P' - P = n • Q := hk ▸ hkQ
    rw [← h1, add_sub_cancel]
  rw [hP'eq]
  exact kw_veluDeficit_add_nsmul_odd hp3 hpodd hord hPmem n

theorem kw_mem_zmultiples_of_abscissa_mem_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {a b : F} (hab : W.toAffine.Nonsingular a b)
    (hA : ∃ A ∈ W.oddOrderSummingSet Q ((p - 1) / 2), A.1 = a) :
    Affine.Point.some a b hab ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨A, hAmem, hAfst⟩ := hA
  obtain ⟨k, xk, yk, hk, hk1, _, hkQ, hAeq, _⟩ :=
    kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord le_rfl hAmem
  have hax : a = xk := hAfst ▸ congrArg Prod.fst hAeq
  rcases Affine.Y_eq_of_X_eq hab.1 hk.1 hax with hby | hby
  · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨(k : ℤ), by
      rw [natCast_zsmul, hkQ]; exact kw_vdcoog_some_congr hax.symm hby.symm _ _⟩
  · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-(k : ℤ), by
      rw [neg_zsmul, natCast_zsmul, hkQ, Affine.Point.neg_some]
      exact kw_vdcoog_some_congr hax.symm hby.symm _ _⟩

variable (F : Type*) [Field F] [DecidableEq F] in

theorem kw_veluDeficitFunKernelTranslationFixesAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunKernelTranslationFixesAt F p := by
  intro W hΔ x₀ y₀ h₀ hord a b hab hA
  classical
  set ι := algebraMap F W.toAffine.FunctionField
  set Q : W.toAffine.Point := Affine.Point.some x₀ y₀ h₀
  set Q' : (W.map ι).toAffine.Point := ratPointHom (W₀ := W.toAffine) ι Q
  rw [translationAlgEquivOf_veluDeficitFun_eq_iff hΔ hab,
    W.toAffine.liftSummingSet_oddOrderSummingSet Q ((p - 1) / 2)]
  have hord' : addOrderOf Q' = p :=
    (addOrderOf_injective (ratPointHom (W₀ := W.toAffine) ι) (ratPointMap_injective ι) Q).trans hord
  have hPmem : Affine.genericPoint hΔ ∉ AddSubgroup.zmultiples Q' :=
    genericPoint_notMem_zmultiples_ratPointHom hΔ Q
  have hab' : W.toAffine.Nonsingular a b :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hab
  have hAmem : Affine.Point.some a b hab' ∈ AddSubgroup.zmultiples Q :=
    kw_mem_zmultiples_of_abscissa_mem_oddOrderSummingSet_odd hp3 hpodd hord hab' hA
  have hdiff : Affine.genericPoint hΔ + Affine.mapPoint hΔ hab - Affine.genericPoint hΔ
      ∈ AddSubgroup.zmultiples Q' := by
    rw [add_sub_cancel_left]
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hAmem
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by
      show n • Q' = ratPointHom (W₀ := W.toAffine) ι (Affine.Point.some a b hab')
      rw [← hn, ← map_zsmul]⟩
  exact kw_veluDeficit_eq_of_sub_mem_zmultiples_odd hp3 hpodd hord' hPmem hdiff

variable (F : Type*) [Field F] [DecidableEq F] in

theorem kw_veluDeficitFunOrdNonnegAtInftyAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunOrdNonnegAtInftyAt F p := by
  intro W _hΔ x₀ y₀ h₀ hord v hv
  exact ord_veluDeficitFun_nonneg_of_not_isFinitePlace hv
    (kw_isOddVeluSet_oddOrderSummingSet_odd hp3 hpodd hord le_rfl).equation

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F] in

theorem kw_veluDeficitFunKernelTranslationYNotCentreAt_odd
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunKernelTranslationYNotCentreAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv ⟨A, hA, hXA⟩
  haveI := hDD W hΔ
  have hSset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord
    (le_refl ((p - 1) / 2))
  have hAeq : W.toAffine.Equation A.1 A.2 := hSset.equation A hA
  have hAgy : W.veluGy A.1 A.2 ≠ 0 := hSset.gy_ne_zero A hA
  have h2tor : W.toAffine.negY A.1 A.2 ≠ A.2 := negY_ne_self_of_veluGy_ne_zero hAgy
  obtain ⟨b, hab, hXcen, hYcen⟩ := Affine.exists_YClass_negY_notMem_centre hv hAeq h2tor hXA
  exact ⟨A.1, b, hab, ⟨A, hA, rfl⟩, hXcen, hYcen⟩

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F] in

theorem kw_veluDeficitFunOrdNonnegAt_odd
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunOrdNonnegAt F p :=
  veluDeficitFunOrdNonnegAt_of_kernelTranslation_of_atInfty_of_offKernel
    (veluDeficitFunKernelTranslationAt_of_fixes_of_toInfty F
      (kw_veluDeficitFunKernelTranslationFixesAt_odd F hp3 hpodd)
      (veluDeficitFunKernelTranslationToInftyAt_of_yNotCentre F
        (kw_veluDeficitFunKernelTranslationYNotCentreAt_odd F hDD hp3 hpodd)))
    (kw_veluDeficitFunOrdNonnegAtInftyAt_odd F hp3 hpodd)
    (veluDeficitFunOrdNonnegOffKernelAt F p)

end OrdNonneg

section ConstantIsZero

variable {F : Type*} [Field F] [DecidableEq F]

theorem kw_veluDeficitCrossQuadBetaSqDecompDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitCrossQuadBetaSqDecompDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  exact ⟨W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S,
    W.veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly S,
    hScard ▸ W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly_natDegree_lt hSne,
    fun r s hrs hav => W.veluDeficitCrossQuadBetaSq_mul_prodPow_sDecomp hrs hav⟩

theorem kw_veluDeficitCrossQuadAlphaBetaDecompDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p)
    (hpodd : Odd p) : VeluDeficitCrossQuadAlphaBetaDecompDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  exact ⟨W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S,
    W.veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly S,
    hScard ▸ W.veluDeficitCrossQuadAlphaBetaConstClearedPoly_natDegree_lt hSne,
    fun r s _hrs hav => W.veluDeficitCrossQuadAlphaBeta_mul_prodPow_sDecomp s hav⟩

theorem kw_veluDeficitCrossQuadCubeBetaDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hβ : VeluDeficitCrossQuadBetaOnlyDegLtAt F p) :
    VeluDeficitCrossQuadCubeBetaDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  obtain ⟨M, hMdeg, hM⟩ := hβ W hΔ x₀ y₀ h₀ hord
  refine ⟨M - W.veluDeficitCrossQuadAlphaCubeClearedPoly S, ?_, fun r s hrs hav => ?_⟩
  · exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hMdeg
      (hScard ▸ W.veluDeficitCrossQuadAlphaCubeClearedPoly_natDegree_lt hSne))
  · rw [W.veluDeficitCrossQuadCubeBeta_eq_betaOnly_sub_alphaCube, sub_mul,
      W.veluDeficitCrossQuadAlphaCube_mul_prodPow_eq hav, hM hrs hav, eval_sub]

theorem kw_veluDeficitCrossQuadProdDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hCB : VeluDeficitCrossQuadCubeBetaDegLtAt F p) :
    VeluDeficitCrossQuadProdDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  obtain ⟨M, hMdeg, hM⟩ := hCB W hΔ x₀ y₀ h₀ hord
  refine ⟨W.veluDeficitCrossQuadAlphaSqClearedPoly S + M, ?_, fun r s hrs hav => ?_⟩
  · exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt
      (hScard ▸ W.veluDeficitCrossQuadAlphaSqClearedPoly_natDegree_lt hSne) hMdeg)
  · rw [W.veluDeficitCrossQuad_eq_alphaSq_add_cubeBeta, add_mul,
      W.veluDeficitCrossQuadAlphaSq_mul_prodPow_eq hav, hM hrs hav, eval_add]

theorem kw_veluDeficitCrossQuadBetaOnlyDegLtAt_odd [Infinite F] [IsAlgClosed F] {p : ℕ}
    (hSD : VeluDeficitCrossQuadBetaSDecompDegLtAt F p) :
    VeluDeficitCrossQuadBetaOnlyDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  obtain ⟨M, N, hMdeg, hMN⟩ := hSD W hΔ x₀ y₀ h₀ hord
  have hNgy : ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ A ∈ S, r ≠ A.1) →
      N.eval r * W.veluGy r s = 0 := by
    intro r s hrs hav
    have hrs' : W.toAffine.Equation r (W.toAffine.negY r s) := (Affine.equation_neg r s).mpr hrs
    have hMN' := hMN hrs' hav
    rw [W.veluDeficitCrossQuadBetaOnly_negY_of_equation hrs, hMN hrs hav] at hMN'
    have hgy : s - W.toAffine.negY r s = -W.veluGy r s := by
      simp only [Affine.negY, veluGy]; ring
    linear_combination N.eval r * hgy - hMN'
  have hN2Ψ : N ^ 2 * W.Ψ₂Sq = 0 := by
    refine eq_zero_of_infinite_isRoot _ ?_
    have hbad_fin : {r : F | ∃ A ∈ S, r = A.1}.Finite :=
      (S.finite_toSet.image Prod.fst).subset (by rintro r ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩)
    refine hbad_fin.infinite_compl.mono ?_
    intro r hr
    have hav : ∀ A ∈ S, r ≠ A.1 := fun A hA heq => hr ⟨A, hA, heq⟩
    obtain ⟨s, hrs⟩ := Affine.exists_equation_of_isAlgClosed W r
    have hsq : (N.eval r) ^ 2 * W.Ψ₂Sq.eval r = 0 := by
      rw [← W.veluU_eq_Ψ₂Sq_eval hrs, veluU, ← mul_pow, hNgy hrs hav, zero_pow two_ne_zero]
    simpa [IsRoot, eval_mul, eval_pow] using hsq
  have hN0 : N = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp
      ((mul_eq_zero.mp hN2Ψ).resolve_right (W.Ψ₂Sq_ne_zero_of_Δ_ne_zero hΔ))
  exact ⟨M, hMdeg, fun r s hrs hav => by rw [hMN hrs hav, hN0, eval_zero, zero_mul, add_zero]⟩

theorem kw_veluDeficitConstantIsZeroAt_odd [Infinite F] [IsAlgClosed F]
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) (hCQ : VeluDeficitCrossQuadProdDegLtAt F p) :
    VeluDeficitConstantIsZeroAt F p := by
  intro W hΔ x₀ y₀ h₀ hord c hc
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  have hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2 :=
    (kw_isOddVeluSet_oddOrderSummingSet_odd hp3 hpodd hord le_rfl).equation
  obtain ⟨M, hMdeg, hM⟩ := hCQ W hΔ x₀ y₀ h₀ hord
  exact W.veluDeficit_isConstant_constant_eq_zero_of_crossQuadProdDegLt hSne hSeq
    (Affine.exists_equation_of_isAlgClosed W) hc (M := M) (hScard ▸ hMdeg)
    (fun r s hrs hav => hM hrs hav)

end ConstantIsZero

end WeierstrassCurve

end
