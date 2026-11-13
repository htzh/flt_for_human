/-
  The datum's characterization: `data.toAdjoin` is the minimal polynomial of `j(q ^ N)`.

  For any `data : ModularPolynomialData N`, `toAdjoin` is monic, annihilates `j(q ^ N)`,
  and has the field degree `ψ(N)` (the capstone), so it is `minpoly ℚ⟮jq⟯ (jqN N)`.
  This is the engine `ModularPolynomialLeadingCoeff` reads.

  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean   -- homes `toAdjoin_eq_minpoly_all`
-/
import FLTForHuman.ModularCurve.ModularEquation.Split
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.Degree.PhiData
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve

/-- The `Y`-degree of the transported datum is `ψ(N)`. Re-derived `private`
(the port's copy in `ModularPolynomialUniqueness.lean` is `private`); the pin's
binder spelling `{N : ℕ} [NeZero N] (data : …)`. -/
private theorem natDegree_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

/-- Every datum at level `N` has `toAdjoin` equal to the minimal polynomial of
`j(q ^ N)`: it is monic, it annihilates `j(q ^ N)`, and its degree is the
minimal one, `ψ(N)`. This is the pin's `toAdjoin_eq_minpoly_all`, the datum's
uniqueness fact, and the statement is the pin's `toAdjoin_eq_minpoly_all`. -/
theorem toAdjoin_eq_minpoly_all (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN N) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_dedekindPsi N
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (aeval_jqN_toAdjoin data)) ?_
  rw [hdeg, natDegree_toAdjoin]

end ModularCurve

end

