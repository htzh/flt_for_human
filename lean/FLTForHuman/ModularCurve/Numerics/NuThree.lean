/-
  `ν₃(N)`, the number of solutions of x² + x + 1 = 0 in `ZMod N`: the prime case, multiplicativity,
  and the small values.

  This is the public home of a block the port had been carrying `private` inside
  `FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean` (`section
  File_FLT_ModularCurve_Numerics_NuThree`, twenty-two declarations). Two of them are pin `Theorems/`
  headlines — `ModularCurve.nuThree_prime` and `ModularCurve.nuThree_mul_of_coprime` — so burying them
  made the frontier count two demand nodes as ported when nothing importable stated them (the pin's
  own `S_ModularCurve_nuThree_prime.lean` is a different, 67-line proof of the same theorem; the text
  here is the composite silo's more developed version).

  Transcribed verbatim from the pin, pinned `aa2d8b3`:

      `P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean` (`File_FLT_ModularCurve_Numerics_NuThree`)
      `Theorems/Thm_ModularCurve_nuThree_prime.lean`
      `Theorems/Thm_ModularCurve_nuThree_mul_of_coprime.lean`

  Every declaration keeps its pin name; the two headlines are the pin's headline names, so no
  statement is restated. Nothing here depends on the rest of the host (checked by name).

  spec-pin: Theorems/Thm_ModularCurve_nuThree_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_nuThree_mul_of_coprime.lean
  spec-pin: P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace ModularCurve

noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

theorem not_sq_add_self_add_one_eq_zero_zmod_nine (y : ZMod 9) : y ^ 2 + y + 1 ≠ 0 := by
  revert y
  decide

theorem nuThree_eq_zero_of_nine_dvd {N : ℕ} (h : 9 ∣ N) : nuThree N = 0 := by
  have hempty : IsEmpty {x : ZMod N // x ^ 2 + x + 1 = 0} := by
    refine ⟨fun z => ?_⟩
    obtain ⟨x, hx⟩ := z
    refine not_sq_add_self_add_one_eq_zero_zmod_nine (ZMod.castHom h (ZMod 9) x) ?_
    have hx9 := congrArg (ZMod.castHom h (ZMod 9)) hx
    simpa only [map_add, map_pow, map_one, map_zero] using hx9
  exact @Nat.card_of_isEmpty _ hempty

section Prime

variable {p : ℕ}

theorem sq_add_self_add_one_eq_zero_iff_orderOf_eq_three (hp : p.Prime) (hp3 : p ≠ 3)
    (x : ZMod p) : x ^ 2 + x + 1 = 0 ↔ orderOf x = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  constructor
  · intro hx
    refine orderOf_eq_prime ?_ ?_
    ·
      linear_combination (x - 1) * hx
    ·
      rintro rfl
      have h3 : (3 : ZMod p) = 0 := by linear_combination hx
      have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)
  · intro hx
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      omega
    have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h : x = 1) hx1
    · exact h

theorem sq_add_self_add_one_eq_zero_iff_of_prime (hp : p.Prime) {ζ x : ZMod p}
    (hζ : ζ ^ 2 + ζ + 1 = 0) : x ^ 2 + x + 1 = 0 ↔ x = ζ ∨ x = -1 - ζ := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hx
    have hfac : (x - ζ) * (x + ζ + 1) = 0 := by linear_combination hx - hζ
    rcases mul_eq_zero.mp hfac with hd | hd
    · exact Or.inl (by linear_combination hd)
    · exact Or.inr (by linear_combination hd)
  · rintro (rfl | rfl)
    · exact hζ
    · linear_combination hζ

theorem ne_neg_one_sub_of_sq_add_self_add_one_eq_zero (hp : p.Prime) (hp3 : p ≠ 3)
    {ζ : ZMod p} (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ -1 - ζ := by
  have : Fact p.Prime := ⟨hp⟩
  intro hcontra
  have h3 : (3 : ZMod p) = 0 := by linear_combination 4 * hζ - (2 * ζ + 1) * hcontra
  have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)

theorem exists_orderOf_eq_three (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ x : ZMod p, orderOf x = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    have := hp.two_le
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  exact ⟨(u : ZMod p), by rw [orderOf_units]; exact hu⟩

theorem nuThree_prime (hp : p.Prime) (hp3 : p ≠ 3) :
    nuThree p = if p % 3 = 1 then 2 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h1 : p % 3 = 1
  ·

    rw [ite_eq_left h1]
    obtain ⟨ζ, hζord⟩ := exists_orderOf_eq_three hp h1
    have hζ : ζ ^ 2 + ζ + 1 = 0 :=
      (sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 ζ).mpr hζord
    have hζ' : (-1 - ζ) ^ 2 + (-1 - ζ) + 1 = 0 := by linear_combination hζ
    have hne : ζ ≠ -1 - ζ := ne_neg_one_sub_of_sq_add_self_add_one_eq_zero hp hp3 hζ
    show Nat.card {x : ZMod p // x ^ 2 + x + 1 = 0} = 2
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨ζ, hζ⟩, ⟨-1 - ζ, hζ'⟩, ?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq]
      exact hne
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      exact (sq_add_self_add_one_eq_zero_iff_of_prime hp hζ).mp hx
  ·

    rw [ite_eq_right h1]
    have hempty : IsEmpty {x : ZMod p // x ^ 2 + x + 1 = 0} := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, hx⟩ := z
      have hord : orderOf x = 3 :=
        (sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 x).mp hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact one_ne_zero (α := ZMod p) (by linear_combination hx)
      have hdvd : (3 : ℕ) ∣ p - 1 := by
        rw [← hord]
        exact ZMod.orderOf_dvd_card_sub_one hx0
      have := hp.two_le
      omega
    exact @Nat.card_of_isEmpty _ hempty

theorem nuThree_eq_zero_of_mod_three_eq_two (hp : p.Prime) (h2 : p % 3 = 2) :
    nuThree p = 0 := by
  have hp3 : p ≠ 3 := by rintro rfl; omega
  have hne1 : ¬p % 3 = 1 := by omega
  rw [nuThree_prime hp hp3, ite_eq_right hne1]

theorem nuThree_eq_two_of_mod_three_eq_one (hp : p.Prime) (h1 : p % 3 = 1) :
    nuThree p = 2 := by
  have hp3 : p ≠ 3 := by rintro rfl; omega
  rw [nuThree_prime hp hp3, ite_eq_left h1]

end Prime

theorem nuThree_three : nuThree 3 = 1 := by
  have hcard : nuThree 3 = Fintype.card {x : ZMod 3 // x ^ 2 + x + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard]
  decide

section Multiplicative

variable {A B : Type*} [Ring A] [Ring B]

theorem fst_sq_add_self_add_one (y : A × B) : (y ^ 2 + y + 1).1 = y.1 ^ 2 + y.1 + 1 := by
  rw [pow_two, pow_two, Prod.fst_add, Prod.fst_add, Prod.fst_mul, Prod.fst_one]

theorem snd_sq_add_self_add_one (y : A × B) : (y ^ 2 + y + 1).2 = y.2 ^ 2 + y.2 + 1 := by
  rw [pow_two, pow_two, Prod.snd_add, Prod.snd_add, Prod.snd_mul, Prod.snd_one]

theorem sq_add_self_add_one_eq_zero_prod_iff (y : A × B) :
    y ^ 2 + y + 1 = 0 ↔ y.1 ^ 2 + y.1 + 1 = 0 ∧ y.2 ^ 2 + y.2 + 1 = 0 := by
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · rw [← fst_sq_add_self_add_one, hy, Prod.fst_zero]
    · rw [← snd_sq_add_self_add_one, hy, Prod.snd_zero]
  · rintro ⟨h1, h2⟩
    calc y ^ 2 + y + 1 = ((y ^ 2 + y + 1).1, (y ^ 2 + y + 1).2) := rfl
      _ = ((0 : A), (0 : B)) := by
          rw [fst_sq_add_self_add_one, snd_sq_add_self_add_one, h1, h2]
      _ = (0 : A × B) := rfl

theorem sq_add_self_add_one_eq_zero_iff_map {R S : Type*} [Ring R] [Ring S] (f : R ≃+* S)
    (x : R) : x ^ 2 + x + 1 = 0 ↔ f x ^ 2 + f x + 1 = 0 := by
  constructor
  · intro hx
    have hmap := congrArg f hx
    simpa only [map_add, map_pow, map_one, map_zero] using hmap
  · intro hx
    have hmap := congrArg f.symm hx
    simpa only [map_add, map_pow, map_one, map_zero, RingEquiv.symm_apply_apply] using hmap

end Multiplicative

theorem nuThree_mul_of_coprime {M N : ℕ} (h : Nat.Coprime M N) :
    nuThree (M * N) = nuThree M * nuThree N := by
  have key : ∀ x : ZMod (M * N),
      x ^ 2 + x + 1 = 0 ↔
        ((ZMod.chineseRemainder h) x).1 ^ 2 + ((ZMod.chineseRemainder h) x).1 + 1 = 0 ∧
          ((ZMod.chineseRemainder h) x).2 ^ 2 + ((ZMod.chineseRemainder h) x).2 + 1 = 0 := by
    intro x
    rw [sq_add_self_add_one_eq_zero_iff_map (ZMod.chineseRemainder h) x,
      sq_add_self_add_one_eq_zero_prod_iff]
  have e₁ : {x : ZMod (M * N) // x ^ 2 + x + 1 = 0} ≃
      {c : ZMod M × ZMod N // c.1 ^ 2 + c.1 + 1 = 0 ∧ c.2 ^ 2 + c.2 + 1 = 0} :=
    Equiv.subtypeEquiv (ZMod.chineseRemainder h).toEquiv key
  have e₂ : {c : ZMod M × ZMod N // c.1 ^ 2 + c.1 + 1 = 0 ∧ c.2 ^ 2 + c.2 + 1 = 0} ≃
      {a : ZMod M // a ^ 2 + a + 1 = 0} × {b : ZMod N // b ^ 2 + b + 1 = 0} :=
    Equiv.subtypeProdEquivProd
      (p := fun a : ZMod M => a ^ 2 + a + 1 = 0)
      (q := fun b : ZMod N => b ^ 2 + b + 1 = 0)
  show Nat.card {x : ZMod (M * N) // x ^ 2 + x + 1 = 0} =
    Nat.card {a : ZMod M // a ^ 2 + a + 1 = 0} * Nat.card {b : ZMod N // b ^ 2 + b + 1 = 0}
  rw [Nat.card_congr (e₁.trans e₂), Nat.card_prod]

theorem nuThree_one : nuThree 1 = 1 := by
  have hcard : nuThree 1 = Fintype.card {x : ZMod 1 // x ^ 2 + x + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard]
  decide

theorem nuThree_seven : nuThree 7 = 2 :=
  nuThree_eq_two_of_mod_three_eq_one (by norm_num) (by norm_num)

theorem nuThree_eleven : nuThree 11 = 0 :=
  nuThree_eq_zero_of_mod_three_eq_two (by norm_num) (by norm_num)

theorem nuThree_thirteen : nuThree 13 = 2 :=
  nuThree_eq_two_of_mod_three_eq_one (by norm_num) (by norm_num)

theorem nuThree_nineteen : nuThree 19 = 2 :=
  nuThree_eq_two_of_mod_three_eq_one (by norm_num) (by norm_num)

end ModularCurve
