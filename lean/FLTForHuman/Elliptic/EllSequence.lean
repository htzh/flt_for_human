/-
The generic elliptic-sequence layer of the multiplication-formula bridge.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3`, sections `PortEllSequenceCore` (the `transf` and `Perm` parts). See
`logs/card-torsion-port.md`.

FLT's `addMulSub` / `rel₄` / `net` are *definitionally* mathlib's
`IsEllipticNet.atom` / `atomRel` / `rel`, so they are aliases here and FLT's
basic lemmas about them (`addMulSub_even`, `atom` symmetries, `net_eq_rel₄`, …)
are mathlib's. What mathlib lacks — and what this module supplies — is FLT's
"transfer" machinery: the reduction of a relator to sorted non-negative indices
via `HaveSameParity₄` / `StrictAnti₄` / `avg₄`.
-/
import FLTForHuman.Elliptic.EDS
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

open scoped Polynomial Polynomial.Bivariate
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R]

/-- FLT's `addMulSub`; definitionally mathlib's elliptic atom. -/
abbrev addMulSub (W : ℤ → R) (m n : ℤ) : R := IsEllipticNet.atom W m n

/-- FLT's `rel₄`; definitionally mathlib's `atomRel`. -/
abbrev rel₄ (W : ℤ → R) (a b c d : ℤ) : R := IsEllipticNet.atomRel W a b c d

/-- FLT's `net`; definitionally mathlib's `rel`. -/
abbrev net (W : ℤ → R) (p q r s : ℤ) : R := IsEllipticNet.rel W p q r s

/-- The elliptic-sequence relation, FLT's `Rel₃`. -/
def Rel₃ (W : ℤ → R) (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

variable (W : ℤ → R)

lemma net_zero_iff_rel₃ (m n r : ℤ) : net W m n r 0 = 0 ↔ Rel₃ W m n r := by
  simp only [net, IsEllipticNet.rel, Rel₃, add_zero, sq]
  constructor <;> intro h <;> linear_combination h

lemma isEllipticSequence_iff_rel₃ :
    IsEllipticSequence W ↔ ∀ m n r : ℤ, Rel₃ W m n r := by
  simp only [IsEllipticSequence]
  exact forall_congr' fun m => forall_congr' fun n => forall_congr' fun r =>
    net_zero_iff_rel₃ W m n r

section transf

variable (a b c d : ℤ)

/-- FLT's `StrictAnti₄`: four non-negative indices in strictly decreasing order. -/
def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

/-- FLT's `HaveSameParity₄`, phrased with `negOnePow`. -/
def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

def avg₄ : ℤ := (a + b + c + d) / 2

namespace HaveSameParity₄

open Int Equiv

variable {W a b c d} (same : HaveSameParity₄ a b c d)

include same in
lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  change IsEllipticNet.atomRel W a b c d
    = IsEllipticNet.rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d
  rw [IsEllipticNet.rel_eq]
  rw [Int.two_mul_ediv_two_of_even
        ((Int.negOnePow_eq_iff a d).mp (same.1.trans (same.2.1.trans same.2.2))),
    Int.two_mul_ediv_two_of_even ((Int.negOnePow_eq_iff b d).mp (same.2.1.trans same.2.2)),
    Int.two_mul_ediv_two_of_even ((Int.negOnePow_eq_iff c d).mp same.2.2)]
  simp_rw [sub_add_cancel]

include same in
lemma even_sum : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]

include same in
lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd

include same in
lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

include same in
protected lemma abs : HaveSameParity₄ |a| |b| |c| |d| := by
  simpa only [HaveSameParity₄, negOnePow_abs] using same

lemma perm (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)) := by
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction ?_ (fun _ ↦ id) (fun σ τ _ _ hσ hτ t same ↦ ?_) this
  on_goal 2 => simp_rw [Perm.mul_apply]; exact hτ (t ∘ σ) (hσ _ same)
  rintro _ ⟨i, rfl⟩ t ⟨h₀₁, h₁₂, h₂₃⟩; fin_cases i
  exacts [⟨h₀₁.symm, h₀₁ ▸ h₁₂, h₂₃⟩, ⟨h₀₁ ▸ h₁₂, h₁₂.symm, h₁₂ ▸ h₂₃⟩,
    ⟨h₀₁, h₁₂ ▸ h₂₃, h₂₃.symm⟩]

include same in
lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [← Int.add_two_le_iff_lt_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

variable (W) in

/-- FLT's `addMulSub₄`. -/
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)

omit same in
lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub, IsEllipticNet.atom]; ring

include same in
lemma addMulSub_transf :
    addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧
      addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - b) = addMulSub₄ W a c b d ∧
      addMulSub W (avg₄ a b c d - d) |avg₄ a b c d - a| = addMulSub₄ W b c a d ∧
      addMulSub W (avg₄ a b c d - c) (avg₄ a b c d - b) = addMulSub₄ W a d b c ∧
      addMulSub W (avg₄ a b c d - c) |avg₄ a b c d - a| = addMulSub₄ W b d a c ∧
      addMulSub W (avg₄ a b c d - b) |avg₄ a b c d - a| = addMulSub₄ W c d a b := by
  simp_rw [IsEllipticNet.atom_abs_right, addMulSub, IsEllipticNet.atom, addMulSub₄,
    sub_add_sub_comm, same.avg₄_add_avg₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf

include same in
theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp only [IsEllipticNet.atomRel, h₁, h₂, h₃, h₄, h₅, h₆,
    addMulSub₄_mul_addMulSub₄, mul_comm]

include same in
theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]

include same in
theorem strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]
  all_goals linarith only [hdc, hcb, hba]

end HaveSameParity₄

end transf

/-- FLT's `rel₆`. -/
def rel₆ (W : ℤ → R) (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

variable (W : ℤ → R)

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  change Rel₃ W m n r ↔ IsEllipticNet.atomRel W (2 * m) (2 * n) (2 * r) (2 * 0) = 0
  rw [IsEllipticNet.atomRel_two_mul, sub_zero, sub_zero, sub_zero, mul_zero]
  exact (net_zero_iff_rel₃ W m n r).symm

lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d := by
  simp only [rel₆, IsEllipticNet.atomRel, IsEllipticNet.atom]; ring

lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d := by
  simp only [rel₆, IsEllipticNet.atomRel, IsEllipticNet.atom]; ring

theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp only [rel₆, IsEllipticNet.atomRel, IsEllipticNet.atom]; ring

theorem addMulSub_sq_mul_rel₄_eq₉ (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s =
      addMulSub W m c * (rel₆ W n d r s c d - rel₆ W r d n s c d + rel₆ W s d n r c d)
      - addMulSub W m d * (rel₆ W n c r s c d - rel₆ W r c n s c d + rel₆ W s c n r c d)
      + addMulSub W c d * (rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d) := by
  simp only [rel₆, IsEllipticNet.atomRel, IsEllipticNet.atom]; ring

/-- The odd recursion satisfied by a normalised EDS, FLT's `OddRec`. -/
def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

/-- The even recursion satisfied by a normalised EDS, FLT's `EvenRec`. -/
def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  change _ ↔ IsEllipticNet.atomRel W (2 * m + 1) (2 * (m - 1) + 1) (2 * 1 + 1) (2 * 0 + 1) = 0
  simp_rw [IsEllipticNet.atomRel, IsEllipticNet.atom_odd]; ring_nf

/-- FLT's `dMin`. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1

/-- FLT's `cMin`. -/
def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even a h]
  · simp [Int.negOnePow_odd a (Int.not_even_iff_odd.mp h)]

lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

section Rel₄OfValid

open HaveSameParity₄

/-- FLT's `Rel₄OfValid`: the relator vanishes on same-parity, strictly decreasing
non-negative quadruples. -/
def Rel₄OfValid (W : ℤ → R) (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

lemma rel₄_fix₁_of_fix₂ {W : ℤ → R} {a c₀ d₀ : ℤ}
    (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)
    (b c : ℤ) : Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ (mem_nonZeroDivisors_iff.mp mem).2 _ ?_,
    fun _hc same anti ↦ (mem_nonZeroDivisors_iff.mp mem).2 _ ?_⟩ <;> rw [mul_comm, ← rel₆]
  on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp_rw [rel₆]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [_hc, anti.2.1, anti.2.2.1, anti.2.2.2]

lemma rel₄_of_fix₂ {W : ℤ → R} {a c₀ d₀ : ℤ}
    (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)
    (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) :
    Rel₄OfValid W a b c d := fun same ⟨_, hdc, hcb, hba⟩ ↦
      (mem_nonZeroDivisors_iff.mp mem).2 _ <| by
  rw [mul_comm, ← rel₆, rel₆_eq₁₀]; simp_rw [rel₆]
  have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1
  have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2
  rw [fix₁, fix₁, fix₁, fix₂ hc, fix₂ hc, fix₂ (hc.trans hdc), rel le_rfl, rel le_rfl,
    rel le_rfl, (rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1]
  · simp_rw [mul_zero, add_zero, sub_zero]
  iterate 10
    simp only [HaveSameParity₄, par, par', same.1, same.2.1, same.2.2, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hc, le, lt, hdc, hcb, hba]

theorem rel₄_of_min₂ {W : ℤ → R} {a : ℤ} (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) :
    Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc | hc := lt_or_ge (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors W one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
    (addMulSub_mem_nonZeroDivisors W one two a) b c
  obtain rfl | hc := (show d ≤ cMin a from hc).eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d :=
    (dMin_le (same.1.trans (same.2.1.trans same.2.2)) anti.1).antisymm <| by
    rwa [← Int.add_two_le_iff_lt_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← Int.negOnePow_eq_iff, negOnePow_cMin, same.1.trans (same.2.1.trans same.2.2)]
  obtain rfl | hc : cMin a = c ∨ _ := ((Int.add_two_le_iff_lt_of_even_sub <| by
    rw [← Int.negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mpr anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]

theorem rel₄_of_anti_oddRec_evenRec {W : ℤ → R} (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=
  Int.strongRec (m := 6)
    (fun a ha b c d same anti ↦
      absurd (ha.trans_le (six_le_of_strictAnti₄ same anti)) (lt_irrefl a))
    fun a h6 ih ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by
  obtain ha' | ha' := haa.lt_or_eq
  · exact ih _ ha' same anti
  obtain hba | rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (Int.add_two_le_iff_lt_of_even_sub <| (Int.negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · rw [← rel₄_transf same]
    refine ih _ ?_ (transf same) (strictAnti₄_transf same anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl | rfl⟩ := b.even_or_odd'
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, ite_eq_left ea]
    have hm : m ≥ 2 := by linarith only [h6, ha']
    convert (rel₃_iff₄ W (m + 1) m 1).mp ((rel₃_iff_oddRec W m).mpr <| oddRec _ hm) using 2
    all_goals ring
  · have nea : ¬ Even a := by
      rw [← ha', Int.not_even_iff_odd]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, ite_eq_right nea]
    have hm : m + 1 ≥ 3 := by linarith only [h6, ha']
    convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ hm) using 2
    all_goals ring

end Rel₄OfValid

section Perm

variable {W : ℤ → R}

lemma rel₄_abs (neg : W.Odd) {m n r s : ℤ} :
    rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp only [IsEllipticNet.atomRel, IsEllipticNet.atom_abs_left neg, IsEllipticNet.atom_abs_right]

lemma rel₄_swap₀₁ (neg : W.Odd) {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W n m r s := by
  simp only [IsEllipticNet.atomRel]
  rw [show IsEllipticNet.atom W n m = - IsEllipticNet.atom W m n from
    (IsEllipticNet.neg_atom neg m n).symm]
  ring

lemma rel₄_swap₁₂ (neg : W.Odd) {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m r n s := by
  simp only [IsEllipticNet.atomRel]
  rw [show IsEllipticNet.atom W r n = - IsEllipticNet.atom W n r from
    (IsEllipticNet.neg_atom neg n r).symm]
  ring

lemma rel₄_swap₂₃ (neg : W.Odd) {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp only [IsEllipticNet.atomRel]
  rw [show IsEllipticNet.atom W s r = - IsEllipticNet.atom W r s from
    (IsEllipticNet.neg_atom neg r s).symm]
  ring

open Equiv

/-- FLT's `relFin4`: the relator as a function of a `Fin 4`-tuple. -/
def relFin4 (W : ℤ → R) (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

theorem relFin4_perm (neg : W.Odd) (σ : Perm (Fin 4)) :
    ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t := by
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction ?_ (by simp) (fun σ τ _ _ hσ hτ t ↦ ?_) this
  · rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
      rw [Perm.sign_swap (Fin.castSucc_lt_succ).ne, Units.neg_smul, one_smul]
    exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]
  rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, map_mul, mul_comm, mul_smul]

lemma relFin4_perm' (neg : W.Odd) (σ : Perm (Fin 4)) (t : Fin 4 → ℤ) :
    Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]

lemma rel₄_same₀₁ (zero : W 0 = 0) (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp only [IsEllipticNet.atomRel, IsEllipticNet.atom_same, zero, mul_zero]
  ring

lemma rel₄_same₁₂ (zero : W 0 = 0) (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp only [IsEllipticNet.atomRel, IsEllipticNet.atom_same, zero, mul_zero]
  ring

lemma rel₄_same₂₃ (zero : W 0 = 0) (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp only [IsEllipticNet.atomRel, IsEllipticNet.atom_same, zero, mul_zero]
  ring

theorem rel₄_of_oddRec_evenRec (neg : W.Odd) (zero : W 0 = 0)
    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)
    {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0 := by
  let t := ![|a|, |b|, |c|, |d|]
  have nonneg i : 0 ≤ t i := by fin_cases i <;> exact abs_nonneg _
  let σ := Fin.revPerm.trans (Tuple.sort t)
  have anti : Antitone (t ∘ σ) := by
    simp_rw [σ, coe_trans, ← Function.comp_assoc]
    exact (Tuple.monotone_sort t).comp_antitone fun _ _ ↦ Fin.rev_le_rev.mpr
  clear_value σ
  rw [← rel₄_abs neg]; change relFin4 W t = 0
  rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]
  by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]
  by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]
  by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]
  rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec
      (HaveSameParity₄.perm σ t (HaveSameParity₄.abs same)), smul_zero]
  exact ⟨nonneg _, (anti <| by decide).lt_of_ne h₃₂,
    (anti <| by decide).lt_of_ne h₂₁, (anti <| by decide).lt_of_ne h₁₀⟩

/-- FLT's `IsEllSequence'.of_oddRec_evenRec`: the odd and even recursions force
the elliptic-sequence relation. -/
theorem isEllipticSequence_of_oddRec_evenRec (neg : W.Odd) (zero : W 0 = 0)
    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    IsEllipticSequence W := by
  rw [isEllipticSequence_iff_rel₃]
  intro m n r
  rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two oddRec evenRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Int.negOnePow_two_mul, Int.negOnePow_zero]

end Perm

section NormEDS

lemma normEDS_isEllipticSequence_of_mem_nonZeroDivisors {b c d : R} (hb : b ∈ R⁰) :
    IsEllipticSequence (normEDS b c d) :=
  isEllipticSequence_of_oddRec_evenRec (normEDS_neg b c d) (normEDS_zero b c d)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two])
    (fun m _ => by simp only [OddRec, normEDS_one, one_pow, mul_one]; exact normEDS_odd b c d m)
    (fun m _ => by
      simp only [EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
      rw [normEDS_even]; ring)

/-- The normalised EDS satisfies the elliptic-sequence relation. In FLT this is
`IsEllSequence'.normEDS`, proved by specialising to the universal EDS to get the
non-zero-divisor hypothesis on `b`. mathlib still lists this as a `TODO`. -/
theorem normEDS_isEllipticSequence (b c d : R) : IsEllipticSequence (normEDS b c d) := by
  rw [normEDS_eq_aeval]
  exact IsEllipticSequence.comp
    (normEDS_isEllipticSequence_of_mem_nonZeroDivisors
      (b := MvPolynomial.X (R := ℤ) Param.B) (c := MvPolynomial.X (R := ℤ) Param.C)
      (d := MvPolynomial.X (R := ℤ) Param.D)
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.B)))
    (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))

end NormEDS

section SequenceProps

variable {W : ℤ → R}

/-- `Rel₃` from mathlib's `rel`-based form of the elliptic-sequence property. -/
lemma rel₃_of_isEllipticSequence (ell : IsEllipticSequence W) (m n r : ℤ) : Rel₃ W m n r :=
  (net_zero_iff_rel₃ W m n r).mp (ell m n r)

lemma oddRec_of_isEllipticSequence (ell : IsEllipticSequence W) (m : ℤ) : OddRec W m :=
  (rel₃_iff_oddRec W m).mp (rel₃_of_isEllipticSequence ell (m + 1) m 1)

lemma evenRec_of_isEllipticSequence (ell : IsEllipticSequence W) (m : ℤ) : EvenRec W m :=
  (rel₃_iff_evenRec W m).mp (rel₃_of_isEllipticSequence ell (m + 1) (m - 1) 1)

/-- FLT's `IsEllSequence'.sub_add_neg_sub_mul_eq_zero`. -/
lemma sub_add_neg_sub_mul_eq_zero (ell : IsEllipticSequence W) (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have h₁ := rel₃_of_isEllipticSequence ell m n r
  have h₂ := rel₃_of_isEllipticSequence ell n m r
  simp only [Rel₃] at h₁ h₂
  rw [add_comm n m, show n - m = -(m - n) by ring] at h₂
  linear_combination h₁ + h₂

/-- FLT's `IsEllSequence'.zero`. -/
lemma zero_of_isEllipticSequence (ell : IsEllipticSequence W) (m : ℤ) (mem : W (2 * m) ∈ R⁰) :
    W 0 = 0 := by
  have h : W (2 * m) * W 0 * W (2 * m) ^ 2 = 0 := by
    have := rel₃_of_isEllipticSequence ell m m (2 * m)
    simp only [Rel₃, sub_self] at this
    rwa [show m + m = 2 * m by ring] at this
  rw [mul_comm (W (2 * m)) (W 0)] at h
  exact (mem_nonZeroDivisors_iff.mp mem).2 _
    ((mem_nonZeroDivisors_iff.mp (pow_mem mem 2)).2 _ h)

/-- FLT's `IsEllSequence'.neg`. -/
lemma neg_of_isEllipticSequence (ell : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl | rfl⟩ := m.even_or_odd'
  on_goal 1 => apply (mem_nonZeroDivisors_iff.mp two).2
  on_goal 2 => apply (mem_nonZeroDivisors_iff.mp one).2
  all_goals apply (mem_nonZeroDivisors_iff.mp (pow_mem one 2)).2
  · convert sub_add_neg_sub_mul_eq_zero ell (1 - m) (m + 1) 1 using 2; ring_nf
  · convert sub_add_neg_sub_mul_eq_zero ell (-m) (m + 1) 1 using 2; ring_nf

end SequenceProps

section Ext

variable {W U : ℤ → R}

/-- FLT's `IsEllSequence'.ext`: two elliptic sequences agreeing at `1,2,3,4` are
equal. -/
theorem isEllipticSequence_ext (ellW : IsEllipticSequence W) (ellU : IsEllipticSequence U)
    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U := by
  funext n
  induction n using Int.negInduction with
  | nat n =>
    refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_) (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
    · rw [Nat.cast_zero, zero_of_isEllipticSequence ellW 1 two,
        zero_of_isEllipticSequence ellU 1 (h2 ▸ two)]
    · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2), ← mul_assoc,
        ← mul_assoc, Nat.cast_mul, Nat.cast_add, evenRec_of_isEllipticSequence ellW, h1, h2,
        evenRec_of_isEllipticSequence ellU]
      convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> omega
    · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
      erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, oddRec_of_isEllipticSequence ellW, h1,
        oddRec_of_isEllipticSequence ellU]
      convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> omega
  | neg ih n => rw [neg_of_isEllipticSequence ellW one two,
      neg_of_isEllipticSequence ellU (h1 ▸ one) (h2 ▸ two), ih]

/-- `normEDS 2 3 2` is the identity EDS. -/
lemma normEDS_two_three_two : normEDS (2 : ℤ) 3 2 = id := by
  apply isEllipticSequence_ext (normEDS_isEllipticSequence 2 3 2) IsEllipticSequence.id <;>
    simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  exacts [mem_nonZeroDivisors_of_ne_zero one_ne_zero,
    mem_nonZeroDivisors_of_ne_zero two_ne_zero, rfl, rfl, rfl, rfl]

lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 := by
  intro h
  refine hn ?_
  apply_fun MvPolynomial.aeval (Param.rec (motive := fun _ => ℤ) 2 3 2) at h
  simpa [universalNormEDS, map_normEDS, normEDS_two_three_two] using h

lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :
    universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)

lemma complEDS_eq_aeval (b c d : R) :
    complEDS b c d = (MvPolynomial.aeval
      (Param.rec (motive := fun _ => R) b c d)
      <| complEDS (MvPolynomial.X (R := ℤ) Param.B) (MvPolynomial.X (R := ℤ) Param.C)
        (MvPolynomial.X (R := ℤ) Param.D) · ·) := by
  simp_rw [map_complEDS, MvPolynomial.aeval_X]

end Ext

section Net

variable {W : ℤ → R}

/-- The *full* net property, from the `s = 0` slice plus non-zero-divisors: apply
`rel₄_of_oddRec_evenRec` at the indices `(2p+s, 2q+s, 2r+s, s)`, which always
have the same parity. -/
lemma net_of_isEllipticSequence (ell : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (p q r s : ℤ) : net W p q r s = 0 := by
  change IsEllipticNet.rel W p q r s = 0
  rw [IsEllipticNet.rel_eq]
  refine rel₄_of_oddRec_evenRec (neg_of_isEllipticSequence ell one two)
    (zero_of_isEllipticSequence ell 1 two) one two
    (fun m _ => oddRec_of_isEllipticSequence ell m)
    (fun m _ => evenRec_of_isEllipticSequence ell m) ?_
  simp only [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]

/-- FLT's `invar_of_net`: the invariant ratio is independent of the index. -/
theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [IsEllipticNet.rel]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

/-- FLT's `net_add_sub_iff`. -/
lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  change IsEllipticNet.rel W (m + n) m (m - n) n = 0 ↔ _
  rw [IsEllipticNet.rel]
  conv_rhs => rw [← sub_eq_zero]
  ring_nf

end Net

end FLTForHuman.Elliptic
