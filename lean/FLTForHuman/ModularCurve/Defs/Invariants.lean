/-
  Layer 0c \u2014 the strong induction's invariants: the port's own consequences.

  Two port-own packagings, stated once because more than one module needs each:

  * `mff_congr`, `full_congr` \u2014 transport of `modularFunctionField`/`modularFunctionFieldFull`
    along an equality of levels, `subst`-based so that the `NeZero` instances travel with the
    level. Both were `private` copies in two modules (the degree data and the capstone); the
    non-membership argument needed a third. They are one line each, but three copies of `subst h;
    rfl` in three modules is the same defect as three copies of any other lemma.
  * `gen_prime` \u2014 `Gen p` is definitional at a prime. This is T19's substitution for
    the pin's `functionFieldGeneration_of_squarefree p` call, so the prime
    non-membership does not depend on the squarefree generation/degree block.

  Both are the port's own statements: the pin's counterparts are `private` and carry a
  different hypothesis (`ModularPolynomialData`), which is why they are here (tier 3,
  no `spec-pin:`) rather than beside the pinned vocabulary. What pins them is use: the
  slot product, the non-membership and the degree data cite them at specific arguments,
  so any drift breaks those builds.

  Assumes `Defs/Fields`'s `modularFunctionField`/`modularFunctionFieldFull`/`Tight`/`Gen`,
  `Defs/Jq`'s `jqN`, and `NumberTheory/DedekindPsi`'s `dedekindPsi`.
-/
import FLTForHuman.ModularCurve.Defs.Fields

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

/-- Transport of the two-generator field along an equality of levels. -/
theorem mff_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionField n = modularFunctionField m := by
  subst h; rfl

/-- Transport of the full divisor field along an equality of levels. -/
theorem full_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionFieldFull n = modularFunctionFieldFull m := by
  subst h; rfl

/-- **`Gen` at a prime is definitional**: `modularFunctionField p =
modularFunctionFieldFull p = ℚ(j, j(q ^ p))`. This is T19's substitution: it
replaces the pin's `functionFieldGeneration_of_squarefree p` call at
`S_ModularCurve_jqN_prime_not_mem_full.lean:1638`
(`TOPIC-t17-t19-route-audit.md` §1), so T19 does not depend on the squarefree
generation/degree block. -/
theorem gen_prime (p : ℕ) [NeZero p] [hp : Fact (Nat.Prime p)] : Gen p := by
  unfold Gen
  refine le_antisymm (modularFunctionField_le_full p) ?_
  rw [modularFunctionField, modularFunctionFieldFull, divisorExpansions,
    IntermediateField.adjoin_le_iff]
  rintro x ⟨d, -, hdvd, rfl⟩
  rcases hp.out.eq_one_or_self_of_dvd d hdvd with h1 | h2
  · subst h1; rw [qExpand_one_apply]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  · subst h2
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

end ModularCurve

end
