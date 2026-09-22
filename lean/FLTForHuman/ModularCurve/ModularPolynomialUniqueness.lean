/-
  T13 — the consequence, part 1: uniqueness and the degree.

  Two facts about the level-`p` datum that the splitting reads off:

  * `finrank_adjoin_jqN_eq_of_prime` — `[ℚ(j)(j(q^p)) : ℚ(j)] = p + 1`, the degree
    of the minimal polynomial, obtained from T12's
    `exists_phiIrreducible_evalSymm` and `dedekindPsi_prime`;
  * `ModularPolynomialData.eq_of_prime` — any two data at a prime are equal,
    because each `toAdjoin` is the minimal polynomial of `j(q^p)`.

  Together they are the "uniqueness" that lets `splits_of_prime` identify the
  caller's datum with the one assembled from the descended family.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean` (52 lines) and
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_of_prime.lean` (73 lines). The
  two public statements are the `Theorems/` wrappers verbatim; the pin's
  `minpoly_jqN_eq_toAdjoin` is T12's `ModularPolynomialData.minpoly_jqN_eq`, and
  its `evalAtJGen_injective`/`aeval_jqN_toAdjoin` are T12's public ones.

  ## Assumptions

  `Defs/Fields`'s `toAdjoin`/`toAdjoin_monic`/`evalAtJGen`; `Defs/Jq`'s
  `jq`/`jqN`/`dedekindPsi`/`dedekindPsi_prime`; `Defs/PhiGen`'s `PhiIrreducible`;
  T12's `ModularPolynomialProperties.exists_phiIrreducible_evalSymm` and
  `ModularPolynomialIrreducible`'s `evalAtJGen_injective`, `aeval_jqN_toAdjoin`,
  `minpoly_jqN_eq`.
-/
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import Mathlib.FieldTheory.Minpoly.Field

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve

/-! ## The relative degree of `j(q ^ N)` -/

section Finrank

variable {N : ℕ} [NeZero N]

/-- `data.toAdjoin` annihilates `j(q ^ N)`; T12's public declaration, restated
here for the local proof. -/
private theorem aeval_jqN_toAdjoin' (data : ModularPolynomialData N) :
    Polynomial.aeval (jqN N) data.toAdjoin = 0 :=
  aeval_jqN_toAdjoin data

/-- For an irreducible datum the relative degree is `ψ(N)`: `data.toAdjoin` is the
minimal polynomial of `j(q ^ N)`, and `IntermediateField.adjoin.finrank` turns the
degree of that minimal polynomial into the degree of the simple extension. -/
private theorem finrank_adjoin_jqN_eq (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ = dedekindPsi N := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      rw [← Polynomial.aeval_def]
      exact aeval_jqN_toAdjoin' data⟩
  rw [IntermediateField.adjoin.finrank hint, ModularPolynomialData.minpoly_jqN_eq data hirr,
    ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

end Finrank

/-- The relative degree at a prime is `p + 1`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean`. -/
theorem finrank_adjoin_jqN_eq_of_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN ℓ} : Set (LaurentSeries ℚ))) = ℓ + 1 := by
  obtain ⟨data, hirr, -⟩ := exists_phiIrreducible_evalSymm ℓ
  rw [show Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          ({jqN ℓ} : Set (LaurentSeries ℚ))) = dedekindPsi ℓ from
      finrank_adjoin_jqN_eq data hirr,
    dedekindPsi_prime hℓ.out]

/-! ## Uniqueness of the datum -/

section Uniqueness

variable {N : ℕ} [NeZero N]

/-- The `Y`-degree of the transported datum is `ψ(N)`. -/
private theorem natDegree_toAdjoin (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

/-- Every datum at a prime has `toAdjoin` equal to the minimal polynomial of
`j(q ^ p)`: it is monic, it annihilates `j(q ^ p)`, and its degree is the
minimal one, `p + 1`. -/
private theorem toAdjoin_eq_minpoly (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN p) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN p) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin' data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN p)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_of_prime p
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (aeval_jqN_toAdjoin' data)) ?_
  rw [hdeg, natDegree_toAdjoin, dedekindPsi_prime hp.out]

end Uniqueness

namespace ModularPolynomialData

/-- Any two modular-polynomial data at a prime are equal. Verbatim from the pin
wrapper `Theorems/Thm_ModularCurve_ModularPolynomialData_eq_of_prime.lean`. -/
theorem eq_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (d d' : ModularPolynomialData p) :
    d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly p d, toAdjoin_eq_minpoly p d']
  cases d
  cases d'
  cases h
  rfl

end ModularPolynomialData

end ModularCurve

end

#print axioms ModularCurve.finrank_adjoin_jqN_eq_of_prime
#print axioms ModularCurve.ModularPolynomialData.eq_of_prime
