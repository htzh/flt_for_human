/-
  SET-AF47B consumer: the coarsening `locAt` and the `e = 1` headline, read at their two smallest
  non-degenerate instances.

  **The zone.** Two rows, both read off
  `FLTForHuman/FieldTheory/ValuationSubringIndependent.lean`.

  Row 1 (`ValuationSubring.locAt` + `mem_locAt_iff` + `le_locAt` + `inv_not_mem_locAt`) is read at a
  *concrete* rank-one valuation subring of `ℚ` — the `2`-adic one,
  `(Rat.padicValuation 2).valuationSubring` — with `D = {2}`.  Nothing in the statement is assumed:
  the two membership facts about `2` are decided by `Rat.padicValuation_le_one_iff` (`den` is `1` for
  `2`, `2` for `2⁻¹`), `2 ∈ locAt … {2}` then follows from `le_locAt` (the coarsening is *coarser*
  than `A`), and the `memLocAt_iff` membership is **read at the point `2`** with the depth index
  `n = 2`, producing the concrete inequality `A.valuation (2 * 2 ^ 2) < 1`.  The accompanying
  non-membership `2⁻¹ ∉ locAt A {2}` is `inv_not_mem_locAt` at the same point: the inverse of the
  coarsening element stays *out*, which is exactly the engine of `exists_le_and_one_le`.

  Row 2 (`exists_valuation_mul_eq_one_of_forall_sup_eq_top`) is the headline, read at the smallest
  possible family: the degree-one extension `F' = F` (`Module.finrank F F = 1`), `S = {Q}` a
  singleton of valuation subrings, `σ = Unit` with `cls` the identity on that singleton
  (`cls = fun _ => Q`, i.e. the unique map `Unit → ↥S` followed by `Subtype.val`), `ω` the constant
  `1 : F`, and `P₀ = Q`.  Two of the four hypotheses are discharged, not assumed:

  * `hS : ∀ P ∈ {Q}, P.comap (algebraMap F F) = Q` is triviality — `algebraMap F F` is the identity
    on `F`, and `comap` of the identity is the subring itself (`ValuationSubring.mem_comap`);
  * `hind` — the independence hypothesis — collapses: every `s : Unit` has `cls s = Q`, so the
    support condition `∀ s, cls s ≠ P → a s = 0` is vacuous, and for the unique index the conclusion
    `P.valuation (∑ s, a s * ω s) = 1` is the hypothesis `Q.valuation (a s) = 1` itself;
  * `hcard : finrank F F ≤ Fintype.card Unit` is `1 ≤ 1`, and `hindep` is vacuous because `S` has one
    member (`P ≠ P₀` is impossible).

  What comes back is the headline's conclusion with no `F'` left: for every `g ≠ 0` in `F` there is
  `h : F` with `Q.valuation (h * g) = 1`.  That is the `e = 1` statement for the trivial prolongation
  — the base field's value group is all of the value group, so every element can be normalized.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.FieldTheory.ValuationSubringIndependent
import Mathlib.NumberTheory.Padics.PadicNumbers

set_option autoImplicit false

noncomputable section

open ValuationSubring

namespace ValuationSubring.SetAF47BConsumer

/-- The `2`-adic valuation subring of `ℚ`: a concrete rank-one valuation subring, i.e. the local ring
of rationals integral at `2`.  Kept `private`: it is the instance of the zone, not an export. -/
private def padicTwo : ValuationSubring ℚ := (Rat.padicValuation 2).valuationSubring

/-- Membership in `padicTwo` is decided by the denominator: `2` is a prime, and `Rat.padicValuation`
has value `≤ 1` exactly on rationals whose denominator is not divisible by `2`. -/
private theorem mem_padicTwo_iff (x : ℚ) : x ∈ padicTwo ↔ ¬ (2 : ℕ) ∣ x.den := by
  show x ∈ (Rat.padicValuation 2).valuationSubring ↔ ¬ (2 : ℕ) ∣ x.den
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff]

/-- `2` itself is integral at `2`. -/
private theorem two_mem_padicTwo : (2 : ℚ) ∈ padicTwo := by
  rw [mem_padicTwo_iff, show ((2 : ℚ)).den = 1 from by norm_num]
  norm_num

/-- `2⁻¹` is not integral at `2`: the denominator is `2`. -/
private theorem inv_two_not_mem_padicTwo : (2 : ℚ)⁻¹ ∉ padicTwo := by
  rw [mem_padicTwo_iff, show ((2 : ℚ)⁻¹).den = 2 from by norm_num]
  norm_num

/-- `2` has value `< 1` at `padicTwo` — it is a nonunit, because its inverse is not integral. -/
private theorem valuation_two_lt_one : padicTwo.valuation (2 : ℚ) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
  exact Or.inr inv_two_not_mem_padicTwo

/-- **Zone A.** The coarsening `locAt padicTwo {2}` at the rank-one `2`-adic valuation subring of
`ℚ`, with `D = {2}`:

* `2 ∈ locAt … {2}` because the coarsening is coarser than `A` (`le_locAt`), and reading that
  membership through `mem_locAt_iff` **at the point `2`** with depth `n = 2` gives the concrete
  inequality `A.valuation (2 * 2 ^ 2) < 1`;
* `2⁻¹ ∉ locAt … {2}` by `inv_not_mem_locAt` at the same point: the coarsening element's inverse
  stays outside. -/
theorem consumer_zoneA_locAt_padic_two :
    (padicTwo.valuation ((2 : ℚ) * (2 : ℚ) ^ 2) < 1) ∧ (2 : ℚ)⁻¹ ∉ locAt padicTwo {2} := by
  refine ⟨?_, inv_not_mem_locAt padicTwo (Set.mem_singleton 2) valuation_two_lt_one
    (by norm_num)⟩
  have hmem : (2 : ℚ) ∈ locAt padicTwo {2} := le_locAt padicTwo {2} two_mem_padicTwo
  exact (mem_locAt_iff padicTwo {2} (2 : ℚ)).mp hmem 2 (Set.mem_singleton 2) valuation_two_lt_one 2

/-- **Zone B.** The headline at the smallest possible family: `F' = F` (degree one), `S = {Q}`,
`σ = Unit`, `cls` the identity on the singleton, `ω` the constant `1`, `P₀ = Q`.  The degree
hypothesis is `1 ≤ 1`, `hS` is `comap` of the identity, `hindep` is vacuous, and the independence
hypothesis `hind` is discharged — with the unique index, its sum is one term and its conclusion is its
own hypothesis.  The conclusion has no `F'` left: every `g ≠ 0` of `F` has a `Q`-unit multiple by an
element of `F`. -/
theorem consumer_zoneB_headline_singleton
    {F : Type*} [Field F] (Q : ValuationSubring F) (g : F) (hg : g ≠ 0) :
    ∃ h : F, Q.valuation (h * g) = 1 := by
  have hmain : ∃ h : F, Q.valuation (algebraMap F F h * g) = 1 :=
    exists_valuation_mul_eq_one_of_forall_sup_eq_top (F' := F) (σ := Unit) Q {Q}
      (by
        intro P hP
        rw [Finset.mem_singleton] at hP
        subst hP
        ext x
        rw [ValuationSubring.mem_comap, Algebra.algebraMap_self_apply])
      (fun _ => Q) (fun _ => Finset.mem_singleton_self Q) (fun _ => (1 : F))
      (fun _ => ValuationSubring.one_mem Q)
      (by
        intro P hP a _ _ hunit
        rw [Finset.mem_singleton] at hP
        subst hP
        obtain ⟨s, hs⟩ := hunit
        have e : (∑ s : Unit, algebraMap F F (a s) * (fun _ => (1 : F)) s) = a s := by
          rw [Fintype.sum_unique, Subsingleton.elim (default : Unit) s]
          simp
        rw [e]
        exact hs)
      (by simp) Q (Finset.mem_singleton_self Q)
      (by intro P hP hne; rw [Finset.mem_singleton] at hP; exact absurd hP hne) g hg
  simpa using hmain

end ValuationSubring.SetAF47BConsumer
