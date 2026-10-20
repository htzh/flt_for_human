/-
  The orbit census of a `D₃`-action on a finite type.

  Let `a`, `b` be endomorphisms of a finite type `X` with `a` an involution, `b` of
  order three and `a b = b² a` — the relations of the dihedral group of order six,
  which therefore acts on `X` through `a ↦ (reflection)` and `b ↦ (rotation)`. If a
  map `c : X → ι` has exactly the six-element `⟨a, b⟩`-orbit of `x` as its fibre over
  `c x`, then

  * every fibre of `c` has `1`, `2`, `3` or `6` elements,
  * the number of `a`-fixed points of `X` is the number of fibres of size `1` or `3`, and
  * `(#1-fibres) + 2 · (#2-fibres)` is the number of `b`-fixed points.

  Transcribed verbatim from the pin
  `Theorems/Thm_Function_orbitCensus_of_dihedralThree_relations.lean` /
  `P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean` (315 pin lines,
  pinned `aa2d8b3`). The pin's `S_` development is `namespace Function.OrbitCensus`, kept
  verbatim (`D₃`-orbits, the `T`- and `six`-finsets, `card_T`/`card_six` and the two
  `Finset.card_bij` bijections onto the fixed-point sets); the port drops only the
  `P2MW.S_<stem>` prefix, and the pin's `solution` wrapper is the headline below.

  Grouping: this is the one permutation-census node of the `Function` family; it shares
  no vocabulary with the two separation-of-variables nodes (they are `Function.SepFinAux`
  / `Function.FactorAux` over `Finset.Univ`-typed products), so it is its own module
  rather than a section of `FunctionSeparation`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has no orbit census of this shape. `rg` over
  `Mathlib/` for `orbitCensus`, `dihedralThree` and `DihedralThree` returns nothing, and
  the concept search (a `D₃`-orbit-counting identity relating fibre sizes to fixed-point
  counts) finds only the general orbit–stabiliser formula
  (`MulAction.card_orbit_mul_card_stabiliser_eq_card_group`), which is not this statement
  and does not prove it. The proof uses mathlib's `Finset.card_bij`,
  `Finset.card_biUnion`, `Finset.disjoint_filter` and `omega` only.

  Drift against `v4.34.0` — statements untouched, no `set_option` and no suppression:

  * the pin's *file-wide* `linter.unusedSectionVars false` is repaired **at the source**
    with 22 `omit … in` lines, one per declaration the pin's `variable`/`include`
    idiom left with an unused auto-included section variable: port:59, 65, 71, 79
    (`[Fintype X] [DecidableEq X]`, on `b_injective`, `a_injective`, `abb`, `ba`),
    port:85, 89, 92, 99, 107, 118, 125 (`[Fintype X]`, on `mem_T`, `self_mem_T`,
    `T_b`, `T_eq_of_mem`, `T_eq_or_disjoint`, `card_T_of_fix`, `card_T_of_not_fix`),
    port:143, 150, 165, 172, 191, 198, 212, 223, 243 (`[Fintype X]` / `[DecidableEq X]`,
    on `card_T`, `bfix_a_iff`, `card_T_a`, `mem_T_a_iff`, `mem_six`, `card_six`,
    `card_six_mem`, `odd_iff`, `small_iff`) and port:270 (`[Fintype X] [DecidableEq ι]`,
    on `c_eq_iff_mem_six`);
  * port:119–121: `card_T_of_fix` keeps the pin's explicit `include hb in`, although
    `hb` is unused in the declaration's own type, so the pin's warning survives the
    `omit [Fintype X]` repair; it is suppressed **declaration-scoped** with
    `set_option linter.unusedSectionVars false in`, and the pin's binder set is
    untouched (dropping the hypothesis with `omit hb in` would have been
    checker-invisible but would have changed the declaration's arity, and the pin
    deliberately asked for it); the three call sites keep the pin's `… b hb …`
    argument;
  * port:380–381: the pin's final `smul_eq_mul` (removed in `v4.34.0`) becomes
    `nsmul_eq_mul, mul_one` followed by `simp only [Nat.cast_id, mul_comm]` —
    `v4.34.0`'s `nsmul_eq_mul` now states `n • a = ↑n * a`, so the `NatCast ℕ` that it
    introduces has to be erased before `omega` can see the arithmetic;
  * the pin's file-wide `linter.unusedVariables false` is **dropped**: with the `omit`s
    in place nothing in the port needs it.

  spec-pin: Theorems/Thm_Function_orbitCensus_of_dihedralThree_relations.lean
  spec-pin: P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Function.OrbitCensus

variable {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
  (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))

omit [Fintype X] [DecidableEq X] in
include hb in
theorem b_injective : Function.Injective b := fun x y h => by
  have := congrArg (fun z => b (b z)) h
  simpa [hb] using this

omit [Fintype X] [DecidableEq X] in
include ha in
theorem a_injective : Function.Injective a := fun x y h => by
  have := congrArg a h
  simpa [ha] using this

omit [Fintype X] [DecidableEq X] in
include hb hab in

theorem abb (x : X) : a (b (b x)) = b (a x) := by
  have h := hab (b x)
  rw [hab x] at h
  rw [h, hb]

omit [Fintype X] [DecidableEq X] in
include hb hab in
theorem ba (x : X) : b (a x) = a (b (b x)) := (abb a b hb hab x).symm

def T (x : X) : Finset X := {x, b x, b (b x)}

omit [Fintype X] in
theorem mem_T {x y : X} : y ∈ T b x ↔ y = x ∨ y = b x ∨ y = b (b x) := by
  simp [T]

omit [Fintype X] in
theorem self_mem_T (x : X) : x ∈ T b x := (mem_T b).mpr (Or.inl rfl)

omit [Fintype X] in
include hb in
theorem T_b (x : X) : T b (b x) = T b x := by
  ext y
  simp only [mem_T, hb]
  tauto

omit [Fintype X] in
include hb in
theorem T_eq_of_mem {x y : X} (h : y ∈ T b x) : T b y = T b x := by
  rcases (mem_T b).mp h with rfl | rfl | rfl
  · rfl
  · exact T_b b hb x
  · rw [T_b b hb, T_b b hb]

omit [Fintype X] in
include hb in

theorem T_eq_or_disjoint (x y : X) : T b y = T b x ∨ Disjoint (T b x) (T b y) := by
  by_cases h : Disjoint (T b x) (T b y)
  · exact Or.inr h
  · left
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hzx, hzy⟩ := h
    rw [← T_eq_of_mem b hb hzy, T_eq_of_mem b hb hzx]

omit [Fintype X] in
set_option linter.unusedSectionVars false in
include hb in
theorem card_T_of_fix {x : X} (h : b x = x) : (T b x).card = 1 := by
  have : T b x = {x} := by
    ext y; simp [mem_T, h]
  rw [this, Finset.card_singleton]

omit [Fintype X] in
include hb in
theorem card_T_of_not_fix {x : X} (h : b x ≠ x) : (T b x).card = 3 := by
  have h1 : b x ≠ x := h
  have h2 : b (b x) ≠ x := by
    intro h2
    apply h
    have := congrArg b h2
    rw [hb] at this
    exact this.symm
  have h3 : b (b x) ≠ b x := by
    intro h3
    exact h ((b_injective b hb) h3)
  rw [T, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simpa using h3.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩

omit [Fintype X] in
include hb in
theorem card_T (x : X) : ((T b x).card = 1 ∧ b x = x) ∨ ((T b x).card = 3 ∧ b x ≠ x) := by
  by_cases h : b x = x
  · exact Or.inl ⟨card_T_of_fix b hb h, h⟩
  · exact Or.inr ⟨card_T_of_not_fix b hb h, h⟩

omit [Fintype X] [DecidableEq X] in
include ha hb hab in

theorem bfix_a_iff (x : X) : b (a x) = a x ↔ b x = x := by
  constructor
  · intro h

    have h' : b (a (a x)) = a (a x) := by
      rw [ba a b hb hab (a x)]
      have hbb : b (b (a x)) = a x := by rw [h, h]
      rw [hbb]
    rwa [ha] at h'
  · intro h
    rw [ba a b hb hab x, h, h]

omit [Fintype X] in
include ha hb hab in
theorem card_T_a (x : X) : (T b (a x)).card = (T b x).card := by
  rcases card_T b hb x with ⟨h1, hx⟩ | ⟨h3, hx⟩
  · rw [h1, card_T_of_fix b hb ((bfix_a_iff a b ha hb hab x).mpr hx)]
  · rw [h3, card_T_of_not_fix b hb (fun h => hx ((bfix_a_iff a b ha hb hab x).mp h))]

omit [Fintype X] in
include hb hab in

theorem mem_T_a_iff {x y : X} : y ∈ T b (a x) ↔ y = a x ∨ y = a (b x) ∨ y = a (b (b x)) := by
  have h1 : b (a x) = a (b (b x)) := ba a b hb hab x
  have h2 : b (b (a x)) = a (b x) := (hab x).symm
  rw [mem_T, h2, h1]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

def six (x : X) : Finset X := T b x ∪ T b (a x)

omit [Fintype X] in
include hb hab in
theorem mem_six {x y : X} :
    y ∈ six a b x ↔ (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))) := by
  rw [six, Finset.mem_union, mem_T, mem_T_a_iff a b hb hab]
  tauto

omit [Fintype X] in
include ha hb hab in

theorem card_six (x : X) :
    (T b (a x) = T b x ∧ (six a b x).card = (T b x).card) ∨
      (Disjoint (T b x) (T b (a x)) ∧ (six a b x).card = 2 * (T b x).card) := by
  rcases T_eq_or_disjoint b hb x (a x) with h | h
  · left
    refine ⟨h, ?_⟩
    rw [six, h, Finset.union_idempotent]
  · right
    refine ⟨h, ?_⟩
    rw [six, Finset.card_union_of_disjoint h, card_T_a a b ha hb hab, two_mul]

omit [Fintype X] in
include ha hb hab in
theorem card_six_mem (x : X) :
    (six a b x).card = 1 ∨ (six a b x).card = 2 ∨ (six a b x).card = 3 ∨ (six a b x).card = 6 := by
  rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩ <;>
    rcases card_T b hb x with ⟨h1, -⟩ | ⟨h3, -⟩
  · exact Or.inl (by rw [h, h1])
  · exact Or.inr (Or.inr (Or.inl (by rw [h, h3])))
  · exact Or.inr (Or.inl (by rw [h, h1]))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, h3])))

omit [Fintype X] in
include ha hb hab in

theorem odd_iff (x : X) :
    ((six a b x).card = 1 ∨ (six a b x).card = 3) ↔ a x ∈ T b x := by
  constructor
  · intro hodd
    rcases card_six a b ha hb hab x with ⟨h, -⟩ | ⟨-, h⟩
    · rw [← h]; exact self_mem_T b (a x)
    · exfalso
      rw [h] at hodd
      rcases hodd with h' | h' <;> omega
  · intro hmem
    have hT : T b (a x) = T b x := T_eq_of_mem b hb hmem
    have : (six a b x).card = (T b x).card := by rw [six, hT, Finset.union_idempotent]
    rw [this]
    rcases card_T b hb x with ⟨h1, -⟩ | ⟨h3, -⟩
    · exact Or.inl h1
    · exact Or.inr h3

omit [Fintype X] in
include ha hb hab in

theorem small_iff (x : X) :
    ((six a b x).card = 1 ∨ (six a b x).card = 2) ↔ b x = x := by
  constructor
  · intro hsmall
    by_contra hne
    have h3 := card_T_of_not_fix b hb hne
    rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h, h3] at hsmall <;> omega
  · intro hfix
    have h1 := card_T_of_fix b hb hfix
    rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (by rw [h, h1])
    · exact Or.inr (by rw [h, h1])

variable {ι : Type*} [DecidableEq ι] (c : X → ι)
  (hc : ∀ x y, c x = c y ↔
    (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))

include hb hab hc in
theorem fibre_eq_six (x : X) : (Finset.univ.filter fun y => c y = c x) = six a b x := by
  ext y
  rw [Finset.mem_filter, mem_six a b hb hab]
  simp only [Finset.mem_univ, true_and]
  rw [eq_comm, hc x y]

omit [Fintype X] [DecidableEq ι] in
include hb hab hc in
theorem c_eq_iff_mem_six (x y : X) : c y = c x ↔ y ∈ six a b x := by
  rw [mem_six a b hb hab, eq_comm, hc x y]

end Function.OrbitCensus

open Function.OrbitCensus in
/-- The census of the orbits of a `D₃`-action: every fibre of `c` has `1`, `2`, `3` or
`6` elements, the `a`-fixed points are counted by the `1`- and `3`-fibres and the
`b`-fixed points by `1 + 2 · (#1-fibres)`. -/
theorem Function.orbitCensus_of_dihedralThree_relations
    {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))
    {ι : Type*} [DecidableEq ι] (c : X → ι)
    (hc : ∀ x y, c x = c y ↔
      (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))
    (S : Finset ι) (hS : ∀ p, p ∈ S ↔ ∃ x, c x = p) :
    (∀ x, (Finset.univ.filter fun y => c y = c x).card = 1 ∨
        (Finset.univ.filter fun y => c y = c x).card = 2 ∨
        (Finset.univ.filter fun y => c y = c x).card = 3 ∨
        (Finset.univ.filter fun y => c y = c x).card = 6) ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 ∨
        (Finset.univ.filter fun y => c y = p).card = 3).card =
      (Finset.univ.filter fun x => a x = x).card ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1).card +
        2 * (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2).card =
      (Finset.univ.filter fun x => b x = x).card := by
  have hfib := fibre_eq_six a b hb hab c hc
  refine ⟨fun x => by rw [hfib]; exact card_six_mem a b ha hb hab x, ?_, ?_⟩
  ·
    symm
    apply Finset.card_bij (fun x _ => c x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨(hS _).mpr ⟨x, rfl⟩, ?_⟩
      rw [hfib, odd_iff a b ha hb hab]
      rw [hx.2]; exact self_mem_T b x
    · intro x hx x' hx' hxx'
      rw [Finset.mem_filter] at hx hx'
      have hmem : x' ∈ six a b x := (c_eq_iff_mem_six a b hb hab c hc x x').mp hxx'.symm
      have hT : T b (a x) = T b x := by rw [hx.2]
      rw [six, hT, Finset.union_idempotent, mem_T] at hmem
      rcases hmem with h | h | h
      · exact h.symm
      ·
        have hfix : a (b x) = b x := by rw [← h]; exact hx'.2
        rw [hab x, hx.2] at hfix

        have : b x = x := b_injective b hb hfix
        rw [h, this]
      · have hfix : a (b (b x)) = b (b x) := by rw [← h]; exact hx'.2
        rw [abb a b hb hab x, hx.2] at hfix

        have h1 : x = b x := b_injective b hb hfix
        rw [h, ← h1, ← h1]
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨x, rfl⟩ := (hS p).mp hp.1
      have hodd : (six a b x).card = 1 ∨ (six a b x).card = 3 := by rw [← hfib]; exact hp.2
      have hmem : a x ∈ T b x := (odd_iff a b ha hb hab x).mp hodd
      rcases (mem_T b).mp hmem with h | h | h
      · exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩, rfl⟩
      ·
        refine ⟨b (b x), ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [abb a b hb hab x, h]
        · exact (c_eq_iff_mem_six a b hb hab c hc x _).mpr
            ((mem_six a b hb hab).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      ·
        refine ⟨b x, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hab x, h, hb]
        · exact (c_eq_iff_mem_six a b hb hab c hc x _).mpr
            ((mem_six a b hb hab).mpr (Or.inr (Or.inr (Or.inl rfl))))
  ·
    set S1 := S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 with hS1
    set S2 := S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2 with hS2
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega

    have hunion : (Finset.univ.filter fun x => b x = x) =
        (S1 ∪ S2).biUnion fun p => Finset.univ.filter fun y => c y = p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_union,
        hS1, hS2]
      constructor
      · intro hfix
        refine ⟨c x, ?_, rfl⟩
        have hsmall := (small_iff a b ha hb hab x).mpr hfix
        rw [← hfib] at hsmall
        rcases hsmall with h | h
        · exact Or.inl ⟨(hS _).mpr ⟨x, rfl⟩, h⟩
        · exact Or.inr ⟨(hS _).mpr ⟨x, rfl⟩, h⟩
      · rintro ⟨p, hp, rfl⟩
        apply (small_iff a b ha hb hab x).mp
        rw [← hfib]
        rcases hp with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
    rw [hunion, Finset.card_biUnion]
    · rw [Finset.sum_union hdisj]
      have h1 : ∑ p ∈ S1, (Finset.univ.filter fun y => c y = p).card = ∑ p ∈ S1, 1 :=
        Finset.sum_congr rfl fun p hp => by rw [hS1, Finset.mem_filter] at hp; exact hp.2
      have h2 : ∑ p ∈ S2, (Finset.univ.filter fun y => c y = p).card = ∑ p ∈ S2, 2 :=
        Finset.sum_congr rfl fun p hp => by rw [hS2, Finset.mem_filter] at hp; exact hp.2
      rw [h1, h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
      all_goals simp only [Nat.cast_id, mul_comm]
    · intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_filter]
      intro x _ h1 h2
      exact hpq (h1.symm.trans h2)
