/-  The polynomial calculus of a transcendental generator over a valuation subring.

  Let `A` be a valuation subring of an algebraically closed field `L`, let `F / L` be a field extension
  and `f ∈ F` transcendental over `L`. An element of `F` that lies in every valuation subring of `F`
  containing `L` and `f` (and whose `f`-denominator has a unit coefficient) can be *normalized*: it is a
  sum of terms whose scalar part has coefficients in `A` and whose remainder is a coefficient that is
  small at every such valuation. Dually, an element `x` such that `x * aeval f t` lies in every such
  valuation subring — and whose `f⁻¹`-side has the same property — is a constant of `L`.

  These are the two membership tests of the valuation spectrum that the regular prolongation's residue
  computation uses: they turn "lies in every valuation ring" into coefficient conditions in `A`.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean`
  (705 lines) and `…_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean` (310), with the
  statements from their wrappers `Theorems/Thm_ValuationSubring_*.lean`.

  spec-pin: Theorems/Thm_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean
  spec-pin: P2M/Sol/S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean
  spec-pin: Theorems/Thm_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean
  spec-pin: P2M/Sol/S_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean
-/
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

open Polynomial

namespace ZfSol

variable {L : Type*} [Field L] (A : ValuationSubring L)

def ACoeff (p : L[X]) : Prop := ∀ j, p.coeff j ∈ A


theorem ACoeff.zero : ACoeff A (0 : L[X]) := fun j => by simp [A.zero_mem]

theorem ACoeff.one : ACoeff A (1 : L[X]) := fun j => by
  rw [coeff_one]; split_ifs <;> simp [A.one_mem, A.zero_mem]

theorem ACoeff.C {a : L} (ha : a ∈ A) : ACoeff A (C a) := fun j => by
  rw [coeff_C]; split_ifs <;> simp [ha, A.zero_mem]

theorem ACoeff.X : ACoeff A (X : L[X]) := fun j => by
  rw [coeff_X]; split_ifs <;> simp [A.one_mem, A.zero_mem]

theorem ACoeff.add {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p + q) :=
  fun j => by rw [coeff_add]; exact AddMemClass.add_mem (hp j) (hq j)

theorem ACoeff.neg {p : L[X]} (hp : ACoeff A p) : ACoeff A (-p) :=
  fun j => by rw [coeff_neg]; exact NegMemClass.neg_mem (hp j)

theorem ACoeff.sub {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p - q) :=
  fun j => by rw [coeff_sub]; exact sub_mem (hp j) (hq j)

theorem ACoeff.mul {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p * q) := by
  intro j
  rw [coeff_mul]
  refine sum_mem fun x _ => ?_
  exact MulMemClass.mul_mem (hp _) (hq _)

theorem ACoeff.prod {ι : Type*} (s : Finset ι) (g : ι → L[X]) (hg : ∀ i ∈ s, ACoeff A (g i)) :
    ACoeff A (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ACoeff.one A
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ACoeff.mul A (hg a (Finset.mem_insert_self _ _))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem ACoeff.multiset_prod {ι : Type*} (s : Multiset ι) (g : ι → L[X])
    (hg : ∀ i ∈ s, ACoeff A (g i)) : ACoeff A (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using ACoeff.one A
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact ACoeff.mul A (hg a (Multiset.mem_cons_self _ _))
      (ih fun i hi => hg i (Multiset.mem_cons_of_mem hi))

theorem ACoeff.valuation_le {p : L[X]} (hp : ACoeff A p) (j : ℕ) :
    A.valuation (p.coeff j) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (hp j)

theorem acoeff_of_valuation_le {p : L[X]} (hp : ∀ j, A.valuation (p.coeff j) ≤ 1) :
    ACoeff A p := fun j => (A.valuation_le_one_iff _).mp (hp j)

def IsGood (t : L[X]) : Prop :=
  A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1


theorem IsGood.valuation_le {t : L[X]} (ht : IsGood A t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = 0
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGood.acoeff {t : L[X]} (ht : IsGood A t) : ACoeff A t :=
  acoeff_of_valuation_le A (ht.valuation_le A)

theorem IsGood.ne_zero {t : L[X]} (ht : IsGood A t) : t ≠ 0 := by
  intro h; have := ht.1; rw [h, coeff_zero, map_zero] at this; exact zero_ne_one this

theorem IsGood.one : IsGood A (1 : L[X]) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [coeff_one, ite_eq_right hj, map_zero]; exact zero_lt_one

theorem IsGood.one_sub {c : L} (hc : A.valuation c < 1) :
    IsGood A (1 - Polynomial.C c * Polynomial.X : L[X]) := by
  refine ⟨?_, fun j hj => ?_⟩
  · simp
  · rw [coeff_sub, coeff_one, ite_eq_right hj, coeff_C_mul]
    by_cases h1 : j = 1
    · subst h1; simp [Valuation.map_neg, hc]
    · rw [coeff_X_of_ne_one h1, mul_zero, sub_zero, map_zero]; exact zero_lt_one

theorem IsGood.mul {t s : L[X]} (ht : IsGood A t) (hs : IsGood A s) : IsGood A (t * s) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [mul_coeff_zero, map_mul, ht.1, hs.1, one_mul]
  · rw [coeff_mul]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    by_cases h1 : x.1 = 0
    · have h2 : x.2 ≠ 0 := by omega
      calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ 1 * A.valuation (s.coeff x.2) := by gcongr; exact ht.valuation_le A _
        _ < 1 := by rw [one_mul]; exact hs.2 _ h2
    · calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ A.valuation (t.coeff x.1) * 1 := by gcongr; exact hs.valuation_le A _
        _ < 1 := by rw [mul_one]; exact ht.2 _ h1

theorem IsGood.multiset_prod_one_sub (rs : Multiset L) (hrs : ∀ r ∈ rs, A.valuation r < 1) :
    IsGood A (rs.map fun r => (1 - Polynomial.C r * Polynomial.X : L[X])).prod := by
  induction rs using Multiset.induction_on with
  | empty => simpa using IsGood.one A
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact IsGood.mul A (IsGood.one_sub A (hrs a (Multiset.mem_cons_self _ _)))
      (ih fun r hr => hrs r (Multiset.mem_cons_of_mem hr))

theorem prod_X_sub_C_eq_C_mul_prod_one_sub (s : Multiset L) (hs : ∀ ρ ∈ s, ρ ≠ 0) :
    (s.map fun ρ => (X - C ρ : L[X])).prod =
      C (s.map fun ρ => -ρ).prod *
        ((s.map fun ρ => ρ⁻¹).map fun r => (1 - C r * X : L[X])).prod := by
  rw [map_multiset_prod C, Multiset.map_map, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congr_arg _ (Multiset.map_congr rfl fun ρ hρ => ?_)
  simp only [Function.comp_apply]
  have hρ0 : ρ ≠ 0 := hs ρ hρ
  have : C (-ρ) * (1 - C ρ⁻¹ * X) = X - C ρ := by
    have h1 : C ρ * C ρ⁻¹ = (1 : L[X]) := by rw [← C_mul, mul_inv_cancel₀ hρ0, C_1]
    rw [C_neg]
    linear_combination X * h1
  exact this.symm

def IsPrim (p : L[X]) : Prop :=
  (∀ j, A.valuation (p.coeff j) ≤ 1) ∧ ∃ d, A.valuation (p.coeff d) = 1


theorem IsPrim.ne_zero {p : L[X]} (hp : IsPrim A p) : p ≠ 0 := by
  rintro rfl
  obtain ⟨d, hd⟩ := hp.2
  rw [coeff_zero, map_zero] at hd
  exact zero_ne_one hd

theorem IsPrim.acoeff {p : L[X]} (hp : IsPrim A p) : ACoeff A p :=
  acoeff_of_valuation_le A hp.1

theorem IsGood.isPrim {t : L[X]} (ht : IsGood A t) : IsPrim A t :=
  ⟨ht.valuation_le A, 0, ht.1⟩

theorem IsPrim.mul {p q : L[X]} (hp : IsPrim A p) (hq : IsPrim A q) : IsPrim A (p * q) := by
  classical
  refine ⟨(ACoeff.mul A hp.acoeff hq.acoeff).valuation_le A, ?_⟩

  have hpS : (p.support.filter fun j => A.valuation (p.coeff j) = 1).Nonempty := by
    obtain ⟨d, hd⟩ := hp.2
    refine ⟨d, Finset.mem_filter.mpr ⟨mem_support_iff.mpr ?_, hd⟩⟩
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hqS : (q.support.filter fun j => A.valuation (q.coeff j) = 1).Nonempty := by
    obtain ⟨d, hd⟩ := hq.2
    refine ⟨d, Finset.mem_filter.mpr ⟨mem_support_iff.mpr ?_, hd⟩⟩
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  set i₀ := (p.support.filter fun j => A.valuation (p.coeff j) = 1).max' hpS with hi₀
  set j₀ := (q.support.filter fun j => A.valuation (q.coeff j) = 1).max' hqS with hj₀
  have hi₀mem := Finset.max'_mem _ hpS
  have hj₀mem := Finset.max'_mem _ hqS
  rw [← hi₀, Finset.mem_filter] at hi₀mem
  rw [← hj₀, Finset.mem_filter] at hj₀mem
  have hpi : ∀ i, i₀ < i → A.valuation (p.coeff i) < 1 := by
    intro i hi
    rcases (hp.1 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hmem : i ∈ p.support.filter fun j => A.valuation (p.coeff j) = 1 := by
        refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr ?_, h⟩
        intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
      have := Finset.le_max' _ i hmem
      rw [← hi₀] at this
      exact absurd hi (not_lt.mpr this)
  have hqj : ∀ j, j₀ < j → A.valuation (q.coeff j) < 1 := by
    intro j hj
    rcases (hq.1 j).lt_or_eq with h | h
    · exact h
    · exfalso
      have hmem : j ∈ q.support.filter fun j => A.valuation (q.coeff j) = 1 := by
        refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr ?_, h⟩
        intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
      have := Finset.le_max' _ j hmem
      rw [← hj₀] at this
      exact absurd hj (not_lt.mpr this)
  refine ⟨i₀ + j₀, ?_⟩
  rw [coeff_mul, ← Finset.add_sum_erase _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl : (i₀, j₀) ∈ _)]
  have hmain : A.valuation (p.coeff i₀ * q.coeff j₀) = 1 := by
    rw [map_mul, hi₀mem.2, hj₀mem.2, one_mul]
  have hrest : A.valuation (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      p.coeff x.1 * q.coeff x.2) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro x hx
    rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    rcases lt_or_ge i₀ x.1 with h1 | h1
    · calc A.valuation (p.coeff x.1) * A.valuation (q.coeff x.2)
          ≤ A.valuation (p.coeff x.1) * 1 := by gcongr; exact hq.1 _
        _ < 1 := by rw [mul_one]; exact hpi _ h1
    · have h2 : j₀ < x.2 := by
        rcases lt_or_ge j₀ x.2 with h2 | h2
        · exact h2
        · exfalso
          have h3 : x.1 = i₀ := by omega
          have h4 : x.2 = j₀ := by omega
          exact hx.1 (Prod.ext h3 h4)
      calc A.valuation (p.coeff x.1) * A.valuation (q.coeff x.2)
          ≤ 1 * A.valuation (q.coeff x.2) := by gcongr; exact hp.1 _
        _ < 1 := by rw [one_mul]; exact hqj _ h2
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]

theorem IsPrim.prod {ι : Type*} (s : Finset ι) (g : ι → L[X]) (hg : ∀ i ∈ s, IsPrim A (g i)) :
    IsPrim A (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsGood.one A).isPrim A
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact IsPrim.mul A (hg a (Finset.mem_insert_self _ _))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem isPrim_X_sub_C {α : L} (hα : A.valuation α ≤ 1) : IsPrim A (X - C α : L[X]) := by
  refine ⟨fun j => ?_, 1, ?_⟩
  · rw [coeff_sub, coeff_X, coeff_C]
    split_ifs with h1 h2 h2
    · omega
    · simp
    · simp [Valuation.map_neg, hα]
    · simp
  · simp

theorem acoeff_of_mul_isPrim {r q g : L[X]} (hq : IsPrim A q) (hg : ACoeff A g)
    (h : r * q = g) : ACoeff A r := by
  classical
  by_contra hcon

  have hr0 : r ≠ 0 := by
    rintro rfl; exact hcon (ACoeff.zero A)
  have hne : r.support.Nonempty := support_nonempty.mpr hr0
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image r.support (fun j => A.valuation (r.coeff j)) hne
  set c := r.coeff k with hc
  have hc0 : c ≠ 0 := mem_support_iff.mp hk
  have hcv : 1 < A.valuation c := by
    by_contra hle
    push Not at hle
    apply hcon
    intro j
    rw [← A.valuation_le_one_iff]
    by_cases hj : j ∈ r.support
    · exact (hkmax j hj).trans hle
    · rw [notMem_support_iff.mp hj, map_zero]; exact zero_le

  have hr₀ : IsPrim A (Polynomial.C c⁻¹ * r) := by
    refine ⟨fun j => ?_, k, ?_⟩
    · rw [coeff_C_mul, map_mul, map_inv₀]
      by_cases hj : j ∈ r.support
      · calc (A.valuation c)⁻¹ * A.valuation (r.coeff j)
            ≤ (A.valuation c)⁻¹ * A.valuation c := by gcongr; exact hkmax j hj
          _ = 1 := inv_mul_cancel₀ (by rw [ne_eq, map_eq_zero]; exact hc0)
      · rw [notMem_support_iff.mp hj, map_zero, mul_zero]; exact zero_le
    · rw [coeff_C_mul, ← hc, inv_mul_cancel₀ hc0, map_one]
  obtain ⟨d, hd⟩ := (IsPrim.mul A hr₀ hq).2
  have hd' : A.valuation (g.coeff d) = A.valuation c := by
    have : g = Polynomial.C c * (Polynomial.C c⁻¹ * r * q) := by
      rw [← h, ← mul_assoc, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
    rw [this, coeff_C_mul, map_mul, hd, mul_one]
  have := hg.valuation_le A d
  rw [hd'] at this
  exact absurd hcv (not_lt.mpr this)

theorem isPrim_one_sub_X_sub_C_mul {α : L} (hα : A.valuation α ≤ 1) {C₀ : L[X]}
    (hC : ACoeff A C₀) : IsPrim A (1 - (X - C α) * C₀) := by
  classical
  have hA : ACoeff A (1 - (X - C α) * C₀) :=
    ACoeff.sub A (ACoeff.one A) (ACoeff.mul A ((isPrim_X_sub_C A hα).acoeff A) hC)
  refine ⟨hA.valuation_le A, ?_⟩

  have hcoeff : ∀ n, ((X - C α) * C₀).coeff (n + 1) = C₀.coeff n - α * C₀.coeff (n + 1) := by
    intro n
    rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
  by_cases hall : ∀ j, A.valuation (C₀.coeff j) < 1
  ·
    refine ⟨0, ?_⟩
    rw [coeff_sub, coeff_one_zero, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub,
      neg_mul, sub_neg_eq_add]
    rw [Valuation.map_add_eq_of_lt_left]
    · simp
    · rw [map_one, map_mul]
      calc A.valuation α * A.valuation (C₀.coeff 0) ≤ 1 * A.valuation (C₀.coeff 0) := by gcongr
        _ < 1 := by rw [one_mul]; exact hall 0
  · push Not at hall
    have hS : (C₀.support.filter fun j => A.valuation (C₀.coeff j) = 1).Nonempty := by
      obtain ⟨j, hj⟩ := hall
      have hj1 : A.valuation (C₀.coeff j) = 1 := le_antisymm (hC.valuation_le A j) hj
      refine ⟨j, Finset.mem_filter.mpr ⟨mem_support_iff.mpr ?_, hj1⟩⟩
      intro h; rw [h, map_zero] at hj1; exact zero_ne_one hj1
    set d := (C₀.support.filter fun j => A.valuation (C₀.coeff j) = 1).max' hS with hd
    have hdmem := Finset.max'_mem _ hS
    rw [← hd, Finset.mem_filter] at hdmem
    have hlt : ∀ i, d < i → A.valuation (C₀.coeff i) < 1 := by
      intro i hi
      rcases (hC.valuation_le A i).lt_or_eq with h | h
      · exact h
      · exfalso
        have hmem : i ∈ C₀.support.filter fun j => A.valuation (C₀.coeff j) = 1 := by
          refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr ?_, h⟩
          intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
        have := Finset.le_max' _ i hmem
        rw [← hd] at this
        exact absurd hi (not_lt.mpr this)
    refine ⟨d + 1, ?_⟩
    rw [coeff_sub, coeff_one, ite_eq_right (Nat.succ_ne_zero d), zero_sub, Valuation.map_neg, hcoeff,
      sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
    · exact hdmem.2
    · rw [hdmem.2, Valuation.map_neg, map_mul]
      calc A.valuation α * A.valuation (C₀.coeff (d + 1)) ≤ 1 * A.valuation (C₀.coeff (d + 1)) := by
            gcongr
        _ < 1 := by rw [one_mul]; exact hlt _ (Nat.lt_succ_self d)

theorem valuation_coeff_X_sub_C_mul_lt {α : L} (hα : A.valuation α ≤ 1) {p' : L[X]}
    (hp' : ∀ j, A.valuation (p'.coeff j) < 1) (j : ℕ) :
    A.valuation (((X - C α) * p').coeff j) < 1 := by
  rw [sub_mul, coeff_sub, coeff_C_mul, sub_eq_add_neg]
  refine Valuation.map_add_lt _ ?_ ?_
  · cases j with
    | zero => rw [coeff_X_mul_zero, map_zero]; exact zero_lt_one
    | succ n => rw [coeff_X_mul]; exact hp' n
  · rw [Valuation.map_neg, map_mul]
    calc A.valuation α * A.valuation (p'.coeff j) ≤ 1 * A.valuation (p'.coeff j) := by gcongr
      _ < 1 := by rw [one_mul]; exact hp' j

section Field

variable {F : Type*} [Field F] [Algebra L F]

omit A in
theorem aeval_ne_zero_of_ne_zero {g : F} (hg : Transcendental L g) {t : L[X]} (ht : t ≠ 0) :
    aeval g t ≠ 0 := fun h => ht (transcendental_iff_injective.mp hg (by rw [h, map_zero]))

omit A in
theorem aeval_injective {g : F} (hg : Transcendental L g) : Function.Injective (aeval g : L[X] → F) :=
  transcendental_iff_injective.mp hg

def IsW (f x : F) : Prop :=
  ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
    ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
    x * aeval f q = aeval f p


def IsMW (f x : F) : Prop :=
  ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
    ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
    x * aeval f q = aeval f p


def IsLam (f x : F) : Prop :=
  ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
    (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
    x = aeval f p / aeval f t


variable (L) in
omit A in

def InT (f y : F) : Prop :=
  ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V


omit A in
theorem InT.add {f x y : F} (hx : InT L f x) (hy : InT L f y) : InT L f (x + y) :=
  fun V hV hf => AddMemClass.add_mem (hx V hV hf) (hy V hV hf)

omit A in
theorem InT.sub {f x y : F} (hx : InT L f x) (hy : InT L f y) : InT L f (x - y) :=
  fun V hV hf => sub_mem (hx V hV hf) (hy V hV hf)

omit A in
theorem InT.mul {f x y : F} (hx : InT L f x) (hy : InT L f y) : InT L f (x * y) :=
  fun V hV hf => MulMemClass.mul_mem (hx V hV hf) (hy V hV hf)

omit A in
theorem InT.algebraMap (f : F) (c : L) : InT L f (algebraMap L F c) := fun _ hV _ => hV c

omit A in
theorem InT.self (f : F) : InT L f f := fun _ _ hf => hf

omit A in
theorem InT.aeval (f : F) (p : L[X]) : InT L f (aeval f p) := by
  intro V hV hf
  rw [aeval_eq_sum_range]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  exact MulMemClass.mul_mem (hV _) (pow_mem hf j)

omit A in
theorem InT.sum {f : F} {ι : Type*} (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, InT L f (x i)) :
    InT L f (∑ i ∈ s, x i) := fun V hV hf => sum_mem fun i hi => hx i hi V hV hf

omit A in
theorem algebraMap_mem_adjoin (f : F) (c : L) :
    algebraMap L F c ∈ IntermediateField.adjoin L ({f} : Set F) :=
  IntermediateField.algebraMap_mem _ c

omit A in
theorem self_mem_adjoin (f : F) : f ∈ IntermediateField.adjoin L ({f} : Set F) :=
  IntermediateField.mem_adjoin_simple_self L f

omit A in
theorem aeval_mem_adjoin (f : F) (p : L[X]) :
    aeval f p ∈ IntermediateField.adjoin L ({f} : Set F) := by
  have h1 : aeval f p ∈ Algebra.adjoin L ({f} : Set F) := Polynomial.aeval_mem_adjoin_singleton L f
  exact IntermediateField.algebra_adjoin_le_adjoin L _ h1

omit A in
theorem mem_adjoin_of_mul_aeval_eq {f : F} (hf : Transcendental L f) {x : F} {p q : L[X]}
    (hq : q ≠ 0) (h : x * aeval f q = aeval f p) :
    x ∈ IntermediateField.adjoin L ({f} : Set F) := by
  have hq' : aeval f q ≠ 0 := aeval_ne_zero_of_ne_zero hf hq
  have hx : x = aeval f p / aeval f q := (eq_div_iff hq').mpr h
  rw [hx]
  exact div_mem (aeval_mem_adjoin f p) (aeval_mem_adjoin f q)

end Field

end ZfSol

open ZfSol

theorem ZfSol.caseB
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {x : F} (hx : IsW A f x) {D P : L[X]} (hD0 : D ≠ 0)
    (hroots : ∀ ρ ∈ D.roots, 1 < A.valuation ρ) (hP : x * aeval f D = aeval f P) :
    IsLam A f x := by
  classical
  have hsplit : C D.leadingCoeff * (D.roots.map fun a => X - C a).prod = D :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hroots0 : ∀ ρ ∈ D.roots, ρ ≠ 0 := by
    intro ρ hρ h; have := hroots ρ hρ; rw [h, map_zero] at this
    exact absurd this (not_lt.mpr zero_le)
  set cs : Multiset L := D.roots.map fun ρ => ρ⁻¹ with hcs
  have hcs1 : ∀ c ∈ cs, A.valuation c < 1 := by
    intro c hc
    rw [hcs, Multiset.mem_map] at hc
    obtain ⟨ρ, hρ, rfl⟩ := hc
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hroots ρ hρ)
  set t : L[X] := (cs.map fun c => (1 - C c * X : L[X])).prod with ht
  have htgood : IsGood A t := IsGood.multiset_prod_one_sub A cs hcs1
  set u : L := D.leadingCoeff * (D.roots.map fun ρ => -ρ).prod with hu
  have hfac : D = C u * t := by
    conv_lhs => rw [← hsplit, prod_X_sub_C_eq_C_mul_prod_one_sub D.roots hroots0]
    rw [hu, ht, hcs, C_mul, mul_assoc]
  have hu0 : u ≠ 0 := by
    intro h; apply hD0; rw [hfac, h, C_0, zero_mul]

  obtain ⟨r, hr⟩ : ∃ r : L[X], r = C u⁻¹ * P := ⟨_, rfl⟩
  have hxt : x * aeval f t = aeval f r := by
    have h1 : aeval f D = algebraMap L F u * aeval f t := by
      conv_lhs => rw [hfac]
      rw [map_mul, aeval_C]
    have hU : algebraMap L F u⁻¹ * algebraMap L F u = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
    rw [hr, map_mul, aeval_C, ← hP, h1]
    linear_combination (-(x * aeval f t)) * hU

  obtain ⟨p, q, hp, hq, hpq⟩ := hx
  have hrq : r * q = p * t := by
    apply aeval_injective hf
    rw [map_mul, map_mul, ← hxt, ← hpq]
    ring
  have hrA : ACoeff A r := acoeff_of_mul_isPrim A hq (ACoeff.mul A hp (htgood.acoeff A)) hrq
  exact ⟨r, t, hrA, htgood, (eq_div_iff (aeval_ne_zero_of_ne_zero hf (htgood.ne_zero A))).mpr hxt⟩

open ZfSol

theorem ZfSol.caseA
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {ι : Type*} [Fintype ι] (z : ι → F)
    (hzT : ∀ i, InT L f (z i))
    (hzind : ∀ g : ι → F, (∀ i, g i ∈ IntermediateField.adjoin L ({f} : Set F)) →
      ∑ i, g i * z i = 0 → ∀ i, g i = 0)
    (hres : ∀ (y : F) (w : ι → F), InT L f y → (∀ i, IsW A f (w i)) → y = ∑ i, w i * z i →
      ∃ (C₁ : ι → L[X]) (μ : ι → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧ (∀ i, IsMW A f (μ i)) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i)
    (s : F) (w : ι → F) (hsT : InT L f s) (hs : s = ∑ i, w i * z i)
    (D : L[X]) (P : ι → L[X]) (hD0 : D ≠ 0) (hP : ∀ i, w i * aeval f D = aeval f (P i))
    {α : L} (hα : A.valuation α ≤ 1) (hroot : D.IsRoot α) :
    ∃ (D₁ : L[X]) (P₁ : ι → L[X]), D₁ ≠ 0 ∧ D₁.natDegree < D.natDegree ∧
      ∀ i, w i * aeval f D₁ = aeval f (P₁ i) := by
  classical
  obtain ⟨D₁, hD⟩ := dvd_iff_isRoot.mpr hroot
  have hD₁0 : D₁ ≠ 0 := by
    rintro rfl; exact hD0 (by rw [hD, mul_zero])
  have hdeg : D₁.natDegree < D.natDegree := by
    rw [hD, natDegree_mul (X_sub_C_ne_zero α) hD₁0, natDegree_X_sub_C]
    omega

  have hQex : ∀ i, ∃ Q : L[X], P i - C ((P i).eval α) = (X - C α) * Q := fun i =>
    X_sub_C_dvd_sub_C_eval
  choose Q hQ using hQex
  set e : ι → L := fun i => (P i).eval α with he
  have hfa : f - algebraMap L F α ≠ 0 := by
    have := aeval_ne_zero_of_ne_zero hf (X_sub_C_ne_zero α)
    simpa using this

  set y : F := aeval f D₁ * s - ∑ i, aeval f (Q i) * z i with hy
  have hyT : InT L f y :=
    InT.sub (InT.mul (InT.aeval f D₁) hsT)
      (InT.sum _ _ fun i _ => InT.mul (InT.aeval f (Q i)) (hzT i))
  have hkey : ∑ i, algebraMap L F (e i) * z i = (f - algebraMap L F α) * y := by
    have h1 : ∀ i, aeval f (P i) = algebraMap L F (e i) + (f - algebraMap L F α) * aeval f (Q i) := by
      intro i
      have := congrArg (aeval f) (hQ i)
      simp only [map_sub, map_mul, aeval_C, aeval_X] at this
      linear_combination this
    have h2 : aeval f D = (f - algebraMap L F α) * aeval f D₁ := by
      rw [hD, map_mul, map_sub, aeval_X, aeval_C]
    have h3 : aeval f D * s = ∑ i, aeval f (P i) * z i := by
      rw [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, mul_comm (aeval f D) (w i), hP i]
    rw [hy, mul_sub, ← mul_assoc, ← h2, h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]
    ring

  have hall : ∀ i, e i = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨i₁, hi₁⟩ := hne
    obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => A.valuation (e i))
      ⟨i₁, Finset.mem_univ _⟩
    set c : L := e i₀ with hc
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 := hmax i₁ (Finset.mem_univ _)
      rw [h0, map_zero] at h1
      exact hi₁ ((map_eq_zero A.valuation).mp (le_antisymm h1 zero_le))
    set μ : ι → L := fun i => e i / c with hμ
    have hμle : ∀ i, A.valuation (μ i) ≤ 1 := by
      intro i
      rw [hμ]
      simp only [map_div₀]
      exact div_le_one_of_le₀ (hmax i (Finset.mem_univ _)) zero_le
    have hμ0 : μ i₀ = 1 := by rw [hμ]; exact div_self hc0

    set y' : F := algebraMap L F c⁻¹ * y with hy'
    have hy'T : InT L f y' := InT.mul (InT.algebraMap f _) hyT
    have hkey' : ∑ i, algebraMap L F (μ i) * z i = (f - algebraMap L F α) * y' := by
      have : ∑ i, algebraMap L F (μ i) * z i = algebraMap L F c⁻¹ * ∑ i, algebraMap L F (e i) * z i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμ]
        simp only [map_div₀]
        rw [div_eq_mul_inv, map_inv₀]
        ring
      rw [this, hkey, hy']
      ring

    set w' : ι → F := fun i => algebraMap L F (μ i) / (f - algebraMap L F α) with hw'
    have hw'W : ∀ i, IsW A f (w' i) := by
      intro i
      refine ⟨C (μ i), X - C α, fun j => ?_, isPrim_X_sub_C A hα, ?_⟩
      · rw [coeff_C]
        split_ifs
        · exact (A.valuation_le_one_iff _).mp (hμle i)
        · exact A.zero_mem
      · rw [hw', map_sub, aeval_X, aeval_C, aeval_C, div_mul_cancel₀ _ hfa]
    have hy'sum : y' = ∑ i, w' i * z i := by
      have : ∑ i, w' i * z i = (f - algebraMap L F α)⁻¹ * ∑ i, algebraMap L F (μ i) * z i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw']
        field_simp
      rw [this, hkey', ← mul_assoc, inv_mul_cancel₀ hfa, one_mul]
    obtain ⟨C₁, m, hC₁, hm, hy'eq⟩ := hres y' w' hy'T hw'W hy'sum

    have hcoef : ∀ i, w' i - aeval f (C₁ i) - m i = 0 := by
      apply hzind
      · intro i
        refine sub_mem (sub_mem ?_ (aeval_mem_adjoin f _)) ?_
        · exact div_mem (algebraMap_mem_adjoin f _)
            (sub_mem (self_mem_adjoin f) (algebraMap_mem_adjoin f α))
        · obtain ⟨p', q', -, hq', hpq'⟩ := hm i
          exact mem_adjoin_of_mul_aeval_eq hf (IsPrim.ne_zero A hq') hpq'
      · have : ∑ i, (w' i - aeval f (C₁ i) - m i) * z i =
            ∑ i, w' i * z i - ∑ i, (aeval f (C₁ i) + m i) * z i := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [this, ← hy'sum, ← hy'eq, sub_self]

    have h0 := hcoef i₀
    obtain ⟨p', q', hp', hq', hpq'⟩ := hm i₀
    set G : L[X] := 1 - (X - C α) * C₁ i₀ with hG
    have hGprim : IsPrim A G := isPrim_one_sub_X_sub_C_mul A hα (hC₁ i₀)
    have hGq : G * q' = (X - C α) * p' := by
      apply aeval_injective hf
      have h1 : w' i₀ * (f - algebraMap L F α) = 1 := by
        rw [hw']
        simp only [hμ0, map_one]
        exact div_mul_cancel₀ _ hfa
      have h2 : m i₀ = w' i₀ - aeval f (C₁ i₀) := by linear_combination (-1 : F) * h0
      rw [map_mul, map_mul, ← hpq', h2, hG]
      simp only [map_sub, map_one, map_mul, aeval_X, aeval_C]
      linear_combination (-(aeval f q')) * h1
    obtain ⟨d, hd⟩ := (IsPrim.mul A hGprim hq').2
    rw [hGq] at hd
    exact absurd hd (ne_of_lt (valuation_coeff_X_sub_C_mul_lt A hα hp' d))

  refine ⟨D₁, Q, hD₁0, hdeg, fun i => ?_⟩
  have h1 : P i = (X - C α) * Q i := by
    have := hQ i
    rw [show (P i).eval α = e i from rfl, hall i, C_0, sub_zero] at this
    exact this
  have h2 := hP i
  rw [hD, h1, map_mul, map_mul, map_sub, aeval_X, aeval_C] at h2
  have h3 : (f - algebraMap L F α) * (w i * aeval f D₁) = (f - algebraMap L F α) * aeval f (Q i) := by
    linear_combination h2
  exact mul_left_cancel₀ hfa h3

open ZfSol

theorem ZfSol.main
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {ι : Type*} [Fintype ι] (z : ι → F)
    (hzT : ∀ i, InT L f (z i))
    (hzind : ∀ g : ι → F, (∀ i, g i ∈ IntermediateField.adjoin L ({f} : Set F)) →
      ∑ i, g i * z i = 0 → ∀ i, g i = 0)
    (hres : ∀ (y : F) (w : ι → F), InT L f y → (∀ i, IsW A f (w i)) → y = ∑ i, w i * z i →
      ∃ (C₁ : ι → L[X]) (μ : ι → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧ (∀ i, IsMW A f (μ i)) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i)
    (s : F) (w : ι → F) (hsT : InT L f s) (hw : ∀ i, IsW A f (w i)) (hs : s = ∑ i, w i * z i) :
    ∀ (N : ℕ) (D : L[X]) (P : ι → L[X]), D ≠ 0 → D.natDegree ≤ N →
      (∀ i, w i * aeval f D = aeval f (P i)) → ∀ i, IsLam A f (w i) := by
  classical
  intro N
  induction N with
  | zero =>
    intro D P hD0 hdeg hP i
    by_cases hsmall : ∃ ρ ∈ D.roots, A.valuation ρ ≤ 1
    · obtain ⟨ρ, hρ, hρ1⟩ := hsmall
      obtain ⟨D₁, P₁, -, hlt, -⟩ := caseA A hf z hzT hzind hres s w hsT hs D P hD0 hP hρ1
        ((mem_roots hD0).mp hρ)
      omega
    · push Not at hsmall
      exact caseB A hf (hw i) hD0 hsmall (hP i)
  | succ N ih =>
    intro D P hD0 hdeg hP i
    by_cases hsmall : ∃ ρ ∈ D.roots, A.valuation ρ ≤ 1
    · obtain ⟨ρ, hρ, hρ1⟩ := hsmall
      obtain ⟨D₁, P₁, hD₁0, hlt, hP₁⟩ := caseA A hf z hzT hzind hres s w hsT hs D P hD0 hP
        hρ1 ((mem_roots hD0).mp hρ)
      exact ih D₁ P₁ hD₁0 (by omega) hP₁ i
    · push Not at hsmall
      exact caseB A hf (hw i) hD0 hsmall (hP i)

open ZfSol
theorem exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {ι : Type*} [Fintype ι] (z : ι → F)
    (hzT : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z i ∈ V)
    (hzind : LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z)
    (hres : ∀ (y : F) (w : ι → F),
      (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
      (∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
        ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
        w i * aeval f q = aeval f p) →
      y = ∑ i, w i * z i →
      ∃ (C₁ : ι → L[X]) (μ : ι → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧
        (∀ i, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          μ i * aeval f q = aeval f p) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i)
    (s : F) (w : ι → F)
    (hsT : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V)
    (hw : ∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
      ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
      w i * aeval f q = aeval f p)
    (hs : s = ∑ i, w i * z i) (i : ι) :
    ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
      w i = aeval f p / aeval f t := by
  classical

  have hzind' : ∀ g : ι → F, (∀ i, g i ∈ IntermediateField.adjoin L ({f} : Set F)) →
      ∑ i, g i * z i = 0 → ∀ i, g i = 0 := by
    intro g hg hsum i
    have := Fintype.linearIndependent_iff.mp hzind (fun i => ⟨g i, hg i⟩)
      (by simpa [IntermediateField.smul_def] using hsum) i
    exact congrArg Subtype.val this

  choose p q hp hq hpq using hw
  set D : L[X] := ∏ j, q j with hD
  have hq0 : ∀ j, q j ≠ 0 := fun j => IsPrim.ne_zero A (hq j)
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hq0 j
  set P : ι → L[X] := fun i => p i * ∏ j ∈ Finset.univ.erase i, q j with hP
  have hPw : ∀ i, w i * aeval f D = aeval f (P i) := by
    intro i
    rw [hD, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, ← mul_assoc, hpq i, hP]
    simp only [map_mul]
  exact ZfSol.main A hf z hzT hzind' hres s w hsT (fun i => ⟨p i, q i, hp i, hq i, hpq i⟩) hs
    D.natDegree D P hD0 le_rfl hPw i

open Polynomial

namespace E1Sol

variable {L : Type*} [Field L] (A : ValuationSubring L)

def IsGood (t : L[X]) : Prop :=
  A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1


theorem IsGood.valuation_le {t : L[X]} (ht : IsGood A t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = 0
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGood.coeff_mem {t : L[X]} (ht : IsGood A t) (j : ℕ) : t.coeff j ∈ A :=
  (A.valuation_le_one_iff _).mp (ht.valuation_le A j)

theorem IsGood.coeff_zero_ne {t : L[X]} (ht : IsGood A t) : t.coeff 0 ≠ 0 := by
  intro h; have := ht.1; rw [h, map_zero] at this; exact zero_ne_one this

theorem IsGood.ne_zero {t : L[X]} (ht : IsGood A t) : t ≠ 0 := fun h =>
  ht.coeff_zero_ne A (by rw [h, coeff_zero])

theorem IsGood.valuation_eval_eq_one {t : L[X]} (ht : IsGood A t) {c : L}
    (hc : A.valuation c < 1) : A.valuation (t.eval c) = 1 := by
  rw [eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [Valuation.map_add_eq_of_lt_right]
  · exact ht.1
  · rw [ht.1]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, map_pow]
    calc A.valuation (t.coeff (j + 1)) * A.valuation c ^ (j + 1)
        ≤ 1 * A.valuation c ^ (j + 1) := by gcongr; exact ht.valuation_le A _
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le hc (Nat.succ_ne_zero j)

theorem IsGood.one_lt_valuation_of_isRoot {t : L[X]} (ht : IsGood A t) {ρ : L}
    (hρ : t.IsRoot ρ) : 1 < A.valuation ρ := by
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have h1 := ht.valuation_eval_eq_one A hlt
    rw [show t.eval ρ = 0 from hρ, map_zero] at h1
    exact zero_ne_one h1
  · have hev : t.eval ρ = 0 := hρ
    rw [eval_eq_sum_range, Finset.sum_range_succ'] at hev
    simp only [pow_zero, mul_one] at hev
    have h0 : t.coeff 0 = -∑ j ∈ Finset.range t.natDegree, t.coeff (j + 1) * ρ ^ (j + 1) := by
      linear_combination hev
    have hlt : A.valuation (∑ j ∈ Finset.range t.natDegree, t.coeff (j + 1) * ρ ^ (j + 1)) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro j _
      rw [map_mul, map_pow, heq, one_pow, mul_one]
      exact ht.2 (j + 1) (Nat.succ_ne_zero j)
    have h1 := ht.1
    rw [h0, Valuation.map_neg] at h1
    exact absurd h1 (ne_of_lt hlt)

theorem prod_X_sub_C_eq_C_mul_prod_one_sub (s : Multiset L) (hs : ∀ ρ ∈ s, ρ ≠ 0) :
    (s.map fun ρ => (X - C ρ : L[X])).prod =
      C (s.map fun ρ => -ρ).prod *
        ((s.map fun ρ => ρ⁻¹).map fun r => (1 - C r * X : L[X])).prod := by
  rw [map_multiset_prod C, Multiset.map_map, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congr_arg _ (Multiset.map_congr rfl fun ρ hρ => ?_)
  simp only [Function.comp_apply]
  have hρ0 : ρ ≠ 0 := hs ρ hρ
  have : C (-ρ) * (1 - C ρ⁻¹ * X) = X - C ρ := by
    have h1 : C ρ * C ρ⁻¹ = (1 : L[X]) := by rw [← C_mul, mul_inv_cancel₀ hρ0, C_1]
    rw [C_neg]
    linear_combination X * h1
  exact this.symm

theorem IsGood.exists_eq_C_mul_prod [IsAlgClosed L] {t : L[X]} (ht : IsGood A t) :
    ∃ (u : L) (cs : Multiset L), u ≠ 0 ∧ (∀ c ∈ cs, A.valuation c < 1) ∧
      t = C u * (cs.map fun c => (1 - C c * X : L[X])).prod := by
  classical
  have ht0 := ht.ne_zero A
  have hsplit : C t.leadingCoeff * (t.roots.map fun a => X - C a).prod = t :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hroots : ∀ ρ ∈ t.roots, 1 < A.valuation ρ := fun ρ hρ =>
    ht.one_lt_valuation_of_isRoot A ((mem_roots ht0).mp hρ)
  have hroots0 : ∀ ρ ∈ t.roots, ρ ≠ 0 := by
    intro ρ hρ h; have := hroots ρ hρ; rw [h, map_zero] at this
    exact absurd this (not_lt.mpr zero_le)
  refine ⟨t.leadingCoeff * (t.roots.map fun ρ => -ρ).prod, t.roots.map fun ρ => ρ⁻¹, ?_, ?_, ?_⟩
  · refine mul_ne_zero (leadingCoeff_ne_zero.mpr ht0) ?_
    rw [ne_eq, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨ρ, hρ, h⟩
    exact hroots0 ρ hρ (neg_eq_zero.mp h)
  · intro r hr
    rw [Multiset.mem_map] at hr
    obtain ⟨ρ, hρ, rfl⟩ := hr
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hroots ρ hρ)
  · conv_lhs => rw [← hsplit, prod_X_sub_C_eq_C_mul_prod_one_sub t.roots hroots0]
    rw [C_mul, mul_assoc]

section Field

variable {F : Type*} [Field F] [Algebra L F]

omit A in

theorem valuation_algebraMap_eq_one (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V)
    {c : L} (hc : c ≠ 0) : V.valuation (algebraMap L F c) = 1 := by
  have h1 : V.valuation (algebraMap L F c) ≤ 1 := (V.valuation_le_one_iff _).mpr (hV c)
  have h2 : V.valuation (algebraMap L F c⁻¹) ≤ 1 := (V.valuation_le_one_iff _).mpr (hV c⁻¹)
  have h3 : V.valuation (algebraMap L F c) * V.valuation (algebraMap L F c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : V.valuation (algebraMap L F c) * V.valuation (algebraMap L F c⁻¹) < 1 :=
    calc V.valuation (algebraMap L F c) * V.valuation (algebraMap L F c⁻¹)
        ≤ V.valuation (algebraMap L F c) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  rw [h3] at this
  exact lt_irrefl _ this

omit A in
theorem valuation_algebraMap_le_one (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V)
    (c : L) : V.valuation (algebraMap L F c) ≤ 1 :=
  (V.valuation_le_one_iff _).mpr (hV c)

theorem valuation_aeval_eq_one_of_lt (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V)
    {g : F} (hg : V.valuation g < 1) {t : L[X]} (ht : IsGood A t) :
    V.valuation (aeval g t) = 1 := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, Algebra.smul_def, mul_one]
  have h0 : V.valuation (algebraMap L F (t.coeff 0)) = 1 :=
    valuation_algebraMap_eq_one V hV (ht.coeff_zero_ne A)
  rw [Valuation.map_add_eq_of_lt_right]
  · exact h0
  · rw [h0]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, map_pow]
    calc V.valuation (algebraMap L F (t.coeff (j + 1))) * V.valuation g ^ (j + 1)
        ≤ 1 * V.valuation g ^ (j + 1) := by gcongr; exact valuation_algebraMap_le_one V hV _
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le hg (Nat.succ_ne_zero j)

theorem valuation_aeval_eq_one_of_sub_lt (V : ValuationSubring F)
    (hV : ∀ c : L, algebraMap L F c ∈ V) {g : F} {c : L} (hc : A.valuation c < 1)
    (hgc : V.valuation (g - algebraMap L F c) < 1) {t : L[X]} (ht : IsGood A t) :
    V.valuation (aeval g t) = 1 := by
  have hg1 : V.valuation g ≤ 1 := by
    have : g = (g - algebraMap L F c) + algebraMap L F c := by ring
    rw [this]
    exact (V.valuation.map_add _ _).trans (max_le hgc.le (valuation_algebraMap_le_one V hV c))

  have hev : V.valuation (algebraMap L F (t.eval c)) = 1 := by
    apply valuation_algebraMap_eq_one V hV
    intro h0
    have := ht.valuation_eval_eq_one A hc
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hdiff : aeval g t - algebraMap L F (t.eval c) =
      ∑ j ∈ Finset.range (t.natDegree + 1),
        algebraMap L F (t.coeff j) * (g ^ j - algebraMap L F c ^ j) := by
    rw [aeval_eq_sum_range, eval_eq_sum_range, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, map_pow, mul_sub]
  have hlt : V.valuation (aeval g t - algebraMap L F (t.eval c)) < 1 := by
    rw [hdiff]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul]
    have hpow : V.valuation (g ^ j - algebraMap L F c ^ j) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : V.valuation (∑ i ∈ Finset.range j, g ^ i * algebraMap L F c ^ (j - 1 - i)) ≤ 1 := by
        apply Valuation.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        calc V.valuation g ^ i * V.valuation (algebraMap L F c) ^ (j - 1 - i) ≤ 1 * 1 := by
              gcongr
              · exact pow_le_one₀ zero_le hg1
              · exact pow_le_one₀ zero_le (valuation_algebraMap_le_one V hV c)
          _ = 1 := one_mul 1
      calc V.valuation (∑ i ∈ Finset.range j, g ^ i * algebraMap L F c ^ (j - 1 - i)) *
            V.valuation (g - algebraMap L F c) ≤ 1 * V.valuation (g - algebraMap L F c) := by
            gcongr
        _ < 1 := by rw [one_mul]; exact hgc
    calc V.valuation (algebraMap L F (t.coeff j)) * V.valuation (g ^ j - algebraMap L F c ^ j)
        ≤ 1 * V.valuation (g ^ j - algebraMap L F c ^ j) := by
          gcongr; exact valuation_algebraMap_le_one V hV _
      _ < 1 := by rw [one_mul]; exact hpow
  have : aeval g t = algebraMap L F (t.eval c) + (aeval g t - algebraMap L F (t.eval c)) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hev]; exact hlt), hev]

theorem mem_of_forall [IsAlgClosed L] {f : F} (hf : Transcendental L f) {t t' : L[X]}
    (ht : IsGood A t) (ht' : IsGood A t') {x : F}
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      x * aeval f⁻¹ t' ∈ V)
    (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V) : x ∈ V := by
  classical
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)

  have key : ∀ d : F, V.valuation d = 1 → x * d ∈ V → x ∈ V := by
    intro d hd hxd
    rw [← V.valuation_le_one_iff] at hxd ⊢
    rw [map_mul, hd, mul_one] at hxd
    exact hxd
  rcases lt_trichotomy (V.valuation f) 1 with hlt | heq | hgt
  ·
    exact key _ (valuation_aeval_eq_one_of_lt A V hV hlt ht)
      (hx V hV ((V.valuation_le_one_iff _).mp hlt.le))
  ·
    have hfV : f ∈ V := (V.valuation_le_one_iff _).mp heq.le
    have hfiV : f⁻¹ ∈ V := (V.valuation_le_one_iff _).mp (by rw [map_inv₀, heq, inv_one])
    obtain ⟨u, cs, hu0, hcs, htfac⟩ := ht.exists_eq_C_mul_prod A
    by_cases hunit : ∀ c ∈ cs, V.valuation (1 - algebraMap L F c * f) = 1
    ·
      apply key _ ?_ (hx V hV hfV)
      rw [htfac, map_mul, aeval_C, map_mul, valuation_algebraMap_eq_one V hV hu0, one_mul,
        map_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro v hv
      rw [Multiset.mem_map] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      simp only [Function.comp_apply, map_sub, map_one, map_mul, aeval_C, aeval_X]
      exact hunit c hc
    ·
      push Not at hunit
      obtain ⟨c, hc, hne⟩ := hunit
      have hle : V.valuation (1 - algebraMap L F c * f) ≤ 1 :=
        (V.valuation_le_one_iff _).mpr (sub_mem V.one_mem (MulMemClass.mul_mem (hV c) hfV))
      have hlt : V.valuation (1 - algebraMap L F c * f) < 1 := lt_of_le_of_ne hle hne
      have hcA := hcs c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero, zero_mul, sub_zero, map_one] at hlt
        exact lt_irrefl _ hlt

      have hsub : V.valuation (f⁻¹ - algebraMap L F c) < 1 := by
        have : f⁻¹ - algebraMap L F c = f⁻¹ * (1 - algebraMap L F c * f) := by
          field_simp
        rw [this, map_mul, map_inv₀, heq, inv_one, one_mul]
        exact hlt
      exact key _ (valuation_aeval_eq_one_of_sub_lt A V hV hcA hsub ht') (hx' V hV hfiV)
  ·
    have hlt : V.valuation f⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt
    exact key _ (valuation_aeval_eq_one_of_lt A V hV hlt ht')
      (hx' V hV ((V.valuation_le_one_iff _).mp hlt.le))

omit A in

theorem exists_eq_algebraMap_of_forall_mem [IsAlgClosed L] {x : F}
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → x ∈ V) :
    ∃ c : L, x = algebraMap L F c := by
  have hmem : x ∈ (⨅ V : {V : ValuationSubring F //
      Set.range (algebraMap L F) ⊆ V.toSubring}, V.1.toSubring) := by
    refine Subring.mem_iInf.2 fun V => ?_
    exact hx V.1 fun a => V.2 ⟨a, rfl⟩
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure (Set.range (algebraMap L F))) x := hmem

  set φ := algebraMap L F with hφ
  have hcl : Subring.closure (Set.range φ) = φ.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  have hbij : Function.Bijective φ.rangeRestrict :=
    ⟨fun a b hab => φ.injective (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
  let e : L ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict hbij
  let φ₀ : Subring.closure (Set.range φ) →+* L :=
    e.symm.toRingHom.comp (RingEquiv.subringCongr hcl).toRingHom
  have hcomp : (algebraMap L F).comp φ₀ =
      (RingHom.id F).comp (algebraMap (Subring.closure (Set.range φ)) F) := by
    ext y
    have h1 : φ.rangeRestrict (e.symm (RingEquiv.subringCongr hcl y)) =
        RingEquiv.subringCongr hcl y := by
      rw [← RingEquiv.ofBijective_apply φ.rangeRestrict hbij]
      exact e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    exact h2
  have hintL : IsIntegral L x := by
    have := hint.map_of_comp_eq φ₀ (RingHom.id F) hcomp
    simpa using this

  have h1 : (minpoly L x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hintL)
  have h0 := minpoly.aeval L x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h1,
    show (minpoly L x).leadingCoeff = 1 from minpoly.monic hintL, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h0
  exact ⟨-(minpoly L x).coeff 0, by rw [map_neg]; exact h0⟩

end Field

end E1Sol

open E1Sol
theorem exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (t t' : L[X])
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      x * aeval f⁻¹ t' ∈ V) :
    ∃ c : L, x = algebraMap L F c :=
  exists_eq_algebraMap_of_forall_mem (mem_of_forall A hf ht ht' hx hx')

end ValuationSubring
