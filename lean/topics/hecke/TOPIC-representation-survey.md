# Topic: the representation survey of the Hecke-representative block

**Status: applied (2026-11-18).** The survey asked how the block's facts should be *represented* rather than
merely cleaned up locally. Two things were measured: the index type (`OnePoint (ZMod p)` vs the
`Option ℕ` lift the representatives are stated for) and the place where the four label transitions
are proved. The refactor that came out of it is internal — every public statement is unchanged — and
the four label transitions now live in one lemma, so `heckeRep_mul` has no case split at all.

## What the module said, and at what price

| block | lines before | after |
|---|---|---|
| representations | two index types (`OnePoint` + the `Option ℕ` lift), 28 `labelOf` call sites | **one** index type (`OnePoint (ZMod p)`), no lift |
| four label transitions as a case-condition API (`smul_*_iff`) | 48 | 40 |
| the transitions' `ZMod p` arithmetic, inside `heckeRep_mul` | ~30 | — (with the conditions, in `dvd_conjugate`: 55) |
| `heckeRep_mul` | 113, four nested cases | 61, no cases |
| `heckeMatrix_mul_of_eq` premise | `(j j' : ℕ) (e : ℤ)` | `(j j' : ZMod p)`, no quotient |
| consumers | `e`-obtaining and `.val` casting at both call sites | labels passed directly, −3 / −1 lines |
| module | 811 | 810 |

The four transitions were encoded twice: as `conjugate_*` (entries of the shear conjugate, for the
cocycle) and as `smul_*_iff` (labels, for the case conditions). `heckeRep_mul` was the only place
they met, which is why it needed a two-way translation and four per-case entry analyses.

## Findings and what was done

1. **One index type.** The block is stated over `OnePoint (ZMod p)` throughout: `repMatrix`,
   `conjugate`, `weylPart`/`shear`/`unshear`, the engine `repMatrix_mul`, `dvd_conjugate`, the entry
   facts, the `smul_*_iff` facts and `heckeRep_mul`. There is no `Option ℕ` lift and no `labelOf`
   left; `repMatrix` reads the canonical lift `j.val` in its own body, which is the only place the
   lift appears.

   The pin's `heckeMatrix_mul_of_eq` had to follow, and that turned out to be a *simplification*
   rather than a cost: it was stated over `ℕ` labels with a quotient `e` for the hypothesis
   `… = j' * (…) + p * e`, but in `ZMod p` the term `p * e` is `0`, so the label form needs no
   quotient at all — and its consumers already held labels (`x : ZMod ℓ`, `y := affinePerm g _ x`)
   and converted with `.val` only to reach the pin's signature. They now pass the labels directly
   and lose their `dvd_numerator`/cast plumbing.

2. **The level and the weight are unit cancellations.** Three entry facts carry them:
   `repMatrix x 1 0 = 0` (both representatives are upper triangular), the weight is the `0 0`
   entry (`((repMatrix p (labelOf x) 0 0 : ℤ) : ZMod N) = wt N p x`), and the representative
   carries `p` on its diagonal exactly once
   (`((repMatrix p (labelOf x) 1 1 : ℤ) : ZMod N) * wt N p x = p`). Then the identity's `1 0`
   entry gives `N ∣ g' 1 0` after cancelling the unit `wt N p y` (`isUnit_wt`), and its `1 1`
   entry gives the weight equation after cancelling the unit `p`
   (`ZMod.isUnit_prime_of_not_dvd`). The proof is a six-step `calc`; the four per-case entry
   analyses and their `p`-division bookkeeping are gone.

3. **The transitions moved into the engine.** `dvd_conjugate` proves
   `p ∣ conjugate g (labelOf x) (labelOf (redMatrix p g • x)) 0 1` from the label equation, by
   splitting the label pair once. `repMatrix_mul` now takes that divisibility instead of the
   quotient equation `conjugate g x y 0 1 = p * c`, and returns its witness together with the
   quotient, so no caller constructs the equation. `heckeRep_mul` writes
   `dvd_conjugate g (y := redMatrix p g • x) rfl`.

4. **Kept as they were.** The `smul_*_iff` facts (where the coset action sends a label: they are
   about labels only, with no `N`, no `Γ₀` and no conclusion); the `weylPart`/`clearedWitness`
   factorisation of `repMatrix_mul`'s proof, which is what keeps the engine case-free; the explicit
   witness conjunct (its entries can be read off the matrix as well as off the identity);
   `mapGL_mul_of_matrix` as the single `ℤ → ℝ` bridge.

5. **Rejected.** Re-indexing the coset layer to `OnePoint (ZMod p)` — it breaks the pin-shaped
   `ℕ` entry formulas of `heckeMatrix_mul_of_eq` (finding 1). Adding the `1 1`-entry conjunct to
   `heckeMatrix_mul_of_dvd` — the consumer that would use it (`Gamma1CuspStructure`) reads the same
   entry from `heckeMatrix_mul_of_eq`, which already carries it.

## Consumer adaptation

Zero. `heckeRep_mul`, `HeckeGamma1.heckeRep_mul`, `heckeMatrix_mul_of_eq` and
`heckeMatrix_mul_of_dvd` keep byte-identical statements, and everything new is `private`; the six
outside consumers (`PhiGenDescends`, `NebentypusEigenbasis`, `Gamma1HeckeOperators`, `HeckeULevel`,
`Gamma1CuspStructure`, `HeckeFricke`) build unchanged.

## Verification

`lake env lean` on the module is silent; module build 6 s; `#print axioms` on the two `heckeRep_mul`s
and both facades is `[propext, Classical.choice, Quot.sound]`; the direct importers rebuild green.
