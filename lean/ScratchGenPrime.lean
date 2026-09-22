import FLTForHuman.ModularCurve.FunctionFieldGeneration.Spine
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness

open IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- `Gen p` for prime `p` is near-definitional: both sides are `ℚ(jq, jqN p)`. -/
theorem gen_prime_test (p : ℕ) [hp : Fact (Nat.Prime p)] : Gen p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold Gen
  refine le_antisymm (modularFunctionField_le_full p) ?_
  rw [modularFunctionField, modularFunctionFieldFull, divisorExpansions,
    IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hdne, hdvd, rfl⟩
  rcases hp.out.eq_one_or_self_of_dvd d hdvd with h1 | h2
  · subst h1
    rw [qExpand_one_apply]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  · subst h2
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

/-- The pin's `hallp` at `d = p` (lines 1634-1639), with the sole use of
`functionFieldGeneration_of_squarefree` replaced by `gen_prime_test`. -/
example (p : ℕ) [hp : Fact (Nat.Prime p)] : Tight p ∧ Gen p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨?_, gen_prime_test p⟩
  unfold Tight
  rw [dedekindPsi_prime hp.out]
  exact finrank_adjoin_jqN_eq_of_prime p

end ModularCurve
