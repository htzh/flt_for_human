/-
  Layer 0c \u2014 the strong induction's invariants: the port's own consequences.

  Two port-own packagings, stated once because two modules need each:

  * `isIntegral_adjoin_jqN`, `natDegree_minpoly_jqN` \u2014 from `Tight M` (the adjoin of
    `jqN M` has finite positive dimension) to the integrality of `jqN M` and the degree
    of its minimal polynomial. The slot argument and the non-membership argument each
    used to write these out; the pin has them inline in its slot files and under
    `ModularPolynomialData` hypotheses, never from `Tight`, so there is no pin
    declaration to diff against.
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

/-- **Integrality of `jqN M` over the base field**: `hall` gives the adjoin of `jqN M` the
positive finite dimension `ψ(M)`, so `jqN M` is integral over `ℚ⟮jq⟯`. -/
theorem isIntegral_adjoin_jqN {M : ℕ} [NeZero M]
    (htM : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) = dedekindPsi M) :
    IsIntegral ℚ⟮jq⟯ (jqN M) := by
  have hfd : FiniteDimensional ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ (NeZero.ne M))
  exact IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite ℚ⟮jq⟯
    (⟨jqN M, IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl⟩ :
      IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))))

/-- **The degree of the minimal polynomial**: `minpoly ℚ⟮jq⟯ (jqN M)` has degree `ψ(M)`,
the dimension of the adjoin. -/
theorem natDegree_minpoly_jqN {M : ℕ} [NeZero M]
    (htM : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) = dedekindPsi M) :
    (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M := by
  have hfd : FiniteDimensional ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ (NeZero.ne M))
  rw [← IntermediateField.adjoin.finrank (isIntegral_adjoin_jqN htM)]
  exact htM



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
