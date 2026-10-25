/-
The uniqueness, irreducibility and symmetry of the modular polynomial `Φ_N`.

Four facts about the datum `data : ModularPolynomialData N`, which is a monic `Φ ∈
ℤ[X][Y]` of `Y`-degree `ψ(N)` vanishing at `(j(q), j(q ^ N))`:

* `ModularPolynomialData.eq_all` — any two data at the same level are equal. Each
  `toAdjoin` is the minimal polynomial of `j(q ^ N)` (`toAdjoin_eq_minpoly_all`: it is
  monic, it annihilates `j(q ^ N)` because `Φ` does, and its degree is that of the field
  extension), and the coefficient map is injective;
* `phiIrreducible_all` — the datum is irreducible, since `toAdjoin` is a minimal
  polynomial;
* `phiIrreducible_of_prime`, `ModularPolynomialData.evalSymm_of_prime` — at a prime `p`,
  irreducible and symmetric: `exists_phiIrreducible_evalSymm` (resp.
  `exists_modularPolynomialData_evalSymm`) produces such a datum, and the prime-level
  uniqueness `eq_of_prime` identifies the caller's with it.

`toAdjoin_eq_minpoly_all` is the engine and is public: it is what the uniqueness, the
irreducibility and `ModularPolynomialLeadingCoeff`'s leading-coefficient computation all
read. It needs `aeval_jqN_toAdjoin` and `finrank_adjoin_jqN_eq_dedekindPsi`, both imported.

After FLT's `S_ModularCurve_ModularPolynomialData_eq_all.lean`,
`S_ModularCurve_phiIrreducible_of_prime.lean`,
`S_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean` and
`S_ModularCurve_phiIrreducible_all.lean`, pinned at `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_phiIrreducible_all.lean>.

spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean
spec-pin: Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean
spec-pin: Theorems/Thm_ModularCurve_phiIrreducible_all.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean   -- comparable copy: homes `toAdjoin_eq_minpoly_all`
spec-pin: P2M/Sol/S_ModularCurve_phiIrreducible_all.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.Degree.PhiData
import Mathlib.FieldTheory.Minpoly.Field

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

namespace ModularPolynomialData

/-- Any two modular-polynomial data at the same level `N` are equal: the
transpose `toAdjoin` is always the minimal polynomial of `j(q ^ N)`. Verbatim
from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean`. -/
theorem eq_all (N : ℕ) [NeZero N] (d d' : ModularPolynomialData N) : d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly_all N d, toAdjoin_eq_minpoly_all N d']
  cases d
  cases d'
  cases h
  rfl

/-- At a prime `p` the datum is symmetric. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean`. -/
theorem evalSymm_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) :
    EvalSymm data.Φ := by
  obtain ⟨d, hd⟩ := exists_modularPolynomialData_evalSymm p
  rw [ModularPolynomialData.eq_of_prime p data d]
  exact hd

end ModularPolynomialData

/-- At a prime `p` the datum is irreducible. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean`. -/
theorem phiIrreducible_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) : PhiIrreducible data := by
  obtain ⟨d₀, h, -⟩ := exists_phiIrreducible_evalSymm p
  rwa [ModularPolynomialData.eq_of_prime p data d₀]

/-- At every level `N` the datum is irreducible: `toAdjoin` is the minimal polynomial
of `j(q ^ N)`, and a minimal polynomial is irreducible. Verbatim from
`Theorems/Thm_ModularCurve_phiIrreducible_all.lean`. -/
theorem phiIrreducible_all (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    PhiIrreducible data := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  show Irreducible data.toAdjoin
  rw [toAdjoin_eq_minpoly_all N data]
  exact minpoly.irreducible hint

end ModularCurve

end

#print axioms ModularCurve.ModularPolynomialData.eq_all
#print axioms ModularCurve.phiIrreducible_of_prime
#print axioms ModularCurve.phiIrreducible_all
#print axioms ModularCurve.ModularPolynomialData.evalSymm_of_prime
