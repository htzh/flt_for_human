/-
  The uniqueness, irreducibility and symmetry of the modular polynomial `Φ_N`.

  Three classical facts about the already-ported `Φ` machinery, stated on the
  `ModularPolynomialData` structure and proved from the ported `Φ_p` cone:

  * `ModularPolynomialData.eq_all` — any two data at the same level `N` are
    equal, because each `toAdjoin` is the minimal polynomial of `j(q ^ N)`
    (the `N`-arbitrary form of T13's `eq_of_prime`);
  * `phiIrreducible_of_prime` — the datum is irreducible at a prime `p`;
  * `ModularPolynomialData.evalSymm_of_prime` — the datum is symmetric at a
    prime `p`.

  The last two are one-line transports: the ported `exists_phiIrreducible_evalSymm`
  (resp. `exists_modularPolynomialData_evalSymm`) produces *some* datum with the
  property, and `eq_of_prime` identifies the caller's datum with it.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean` (75 lines),
  `P2M/Sol/S_ModularCurve_phiIrreducible_of_prime.lean` (73 lines) and
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean` (14 lines).
  The three public statements are the `Theorems/` wrappers verbatim.

  ## Reuse

  `evalAtJGen_injective`, `aeval_jqN_toAdjoin`, `finrank_adjoin_jqN_eq_dedekindPsi`
  and `ModularPolynomialData.eq_of_prime` are public in the port and imported.
  The pin's `toAdjoin_eq_minpoly_all` drags a `natDegree_toAdjoin`; the port holds
  both only `private` (`ModularPolynomialUniqueness.lean`), so this module
  re-derives them `private` — no promotion, and the pin's dead
  `evalAtJGen_injective` copy (no consumer in the pin file) is dropped (`--`
  free header, so the statement checker's namespace tracker stays aligned).

  ## Assumptions

  `Defs/PhiGen`'s `ModularPolynomialData`/`PhiIrreducible`/`EvalSymm`;
  `Defs/Fields`'s `toAdjoin`/`evalAtJGen`/`algebraMap_comp_evalAtJGen`;
  `ModularPolynomialIrreducible`'s `evalAtJGen_injective`/`aeval_jqN_toAdjoin`;
  `ModularPolynomialUniqueness`'s `eq_of_prime`/`finrank_adjoin_jqN_eq_of_prime`;
  `ModularPolynomialProperties`'s `exists_phiIrreducible_evalSymm`;
  `Degree/PhiData`'s `exists_modularPolynomialData_evalSymm`.
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
minimal one, `ψ(N)`. This is the pin's `toAdjoin_eq_minpoly_all`, re-derived
`private` (the prime-indexed sibling in `ModularPolynomialUniqueness.lean` is
`private` too). -/
private theorem toAdjoin_eq_minpoly_all (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
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

end ModularCurve

end

#print axioms ModularCurve.ModularPolynomialData.eq_all
#print axioms ModularCurve.phiIrreducible_of_prime
#print axioms ModularCurve.ModularPolynomialData.evalSymm_of_prime
