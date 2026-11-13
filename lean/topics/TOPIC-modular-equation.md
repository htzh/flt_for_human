# The modular-equation theory: one subject, two theories, and the seam between them

The mathematics of the modular equation is [base/006](../../base/006-the-modular-equation.md); the level
tower is [math/010](../../math/010-function-field-generation.md) and
[math/010a](../../math/010a-any-field-supplement.md). This file is about the shape of the code.

Two theories:

* **A — the modular equation at a prime** (`FLTForHuman/ModularCurve/ModularEquation/`). It constructs
  `Φ_p` (monic, degree `ψ(p) = p + 1`, vanishing at `(j(q), j(q^p))`), proves it irreducible and
  symmetric, and splits it at a prime and at a slot.
* **B — the level tower** (`FLTForHuman/ModularCurve/FunctionFieldGeneration/` and its composite-level
  tail). It proves `[ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N)` by the strong induction, and builds the slot product,
  the non-membership, and the canonical datum `dataMinpoly N = minpoly (Polynomial ℤ) (jqN N)`.

They share only the `Defs/*` floor.

## 1. The seam

B reaches A through two theorem families:

* the prime datum — `exists_phiIrreducible_evalSymm`: `Φ_p` monic of degree `p + 1`, irreducible and
  symmetric;
* the split and root family — `splits_of_prime` and `splits_prime_at_slot`.

Everything else in A — the conjugate product, the descent, the integrality of the coefficients, the
assembly, the transpose, the dictionary, the level-two computation — is invisible to B. The
composite-level facts are B's: `dataMinpoly` is built from B's degree count
`finrank_adjoin_jqN_eq_dedekindPsi`, and the characterization `toAdjoin_eq_minpoly_all` reads
`ModularEquation.Split` and `FunctionFieldGeneration.Capstone`.

A middle `PhiGen` theory would be a two-cycle: the split at a prime is obtained by identifying the
caller's datum with the assembled one, so the splitting module imports the modular polynomial's
uniqueness. Folding B into A would stack the level tower on A's main results. Two theories, then.

## 2. Theory A

`FLTForHuman/ModularCurve/ModularEquation/` is five subject modules over four support modules.

| module | lines | role |
|---|---|---|
| `Support/LevelEmbedding` | 77 | the level-`l` nome embedding `Q((q)) -> K((q))`, its injectivity, `evalAtJK`, and `conj 1 = j(q)` |
| `Support/Descent` | 140 | the range tests behind the descent: a twist-fixed series is a level-`l` expand (`mem_range_qExpand_of_qTwist_eq`), a Galois-fixed series is rational (`mem_range_coeffEmb_of_forall_coeffMap_eq`), and their intersection is the image of `coeffEmb ∘ qExpand` (`mem_range_coeffEmb_qExpand_of_mem_inter`); the private contraction `qContract` |
| `Support/PoleBounds` | 250 | the product's pole bounds at the cusp: the leading `1` at `q ^ -(l*l + l)` and the vanishing at and below it |
| `Support/Permutation` | 267 | *products under a permutation* (`map_prod_of_perm`); *the twist's permutation* (`twistPerm`, its label formula and only fixed point, `qTwist_conj`); *the Galois permutation* (`galExp`, `galLabelPerm`, `galPerm`, `coeffMap_conj`); also `Fin.succEquivOfEquiv` |
| `Transpose` | 240 | the transpose engine (`swapBivar` against mathlib's `Bivariate.swap`), the monic/degree bookkeeping, the pole-bound-to-degree dictionary, and the transposed evaluation |
| `Construction` | 438 | descent to `Q((q))`, the integrality of the descended family, and the assembly; one public constructor `exists_modularPolynomialData_splits` |
| `Existence` | 779 | the conjugates, `j(q ^ l)` not a polynomial in `j(q)`, the minimal polynomial, irreducibility, the two descent read-offs (private), and `exists_phiIrreducible_evalSymm` |
| `Split` | 701 | prime-level uniqueness and degree, the split over `Q` and over any field, the slot root API, the coefficient-degree bound, and the symmetry corollary |
| `LevelTwo` | 440 | `Φ = Φ₂` |

The layer discipline: `Transpose` imports only the support modules and `Defs/*`; `Construction`
additionally imports `Support/LevelEmbedding`, `Support/Descent`, `Support/Permutation` and
`ModularForms/PhiGenDescends`; neither imports the other, so the subject layer stays flat. `Existence`
and `Split` consume one constructor, `exists_modularPolynomialData_splits`, and `evalAtJ_injective`;
they do not see the descended family, the assembly, or the coefficient equality. `LevelTwo`'s helpers
are `private`; its only public declaration is `phi_eq_phiTwo`.

## 3. Theory B

B is written at three layers over the same mathematics:

* `Generic/` is the theory: `LevelPackage` (`baseField`, `levelSeries`, `levelField`, `PkgAt`,
  `isIntegral_levelSeries`, `natDegree_minpoly_levelSeries`), `SlotValue` (`slotValue` and its
  separation), `SlotProduct` (`slotProductInduction`, `pushedMinpoly_eq_slotPolynomial`), `PrimeStep`
  (`levelSeries_mem_levelField_mul_prime`) and `PrimeNonmembership` (`prime_notMem_levelField`).
* `Rat/` is the `ℚ` instance: `LevelPackage` converts `Tight`/`Gen`/`Hall` to `PkgAt` and names the
  level fields; `SlotProduct` is the `ℚ` slot-product instance.
* `CharP/` is the `C` layer: `LevelPackage` converts the pin's `Pkg` to `PkgAt`; `SlotProduct`,
  `PrimeStep` and `Nonmembership` are its instances; `PrimePowerStep` is its prime-power degree step.

The `ℚ` spine sits above the shared floor: `Target` (the `FunctionFieldGeneration` definition),
`Collapse` (`functionFieldGeneration_iff_full_eq`), `Capstone` (the strong induction and its
corollaries), `DegreeStep` (the prime-power degree), `Generation` (one new generator per prime power),
`Descent` (the one-prime descent, the `ℚ` prime-step instance), `Nonmembership` (the two
non-membership facts), `SlotProduct` (the pinned slot product and prime non-membership spelling),
`SlotValues` (the slot count), `TwoPrimeSeparation`, and `ModularPolynomialExistence`.

The composite-level tail lives outside the directory:

| module | lines | role |
|---|---|---|
| `Defs/Invariants` | 64 | `mff_congr`, `full_congr`, `gen_prime` |
| `Degree/PhiData` | 206 | the `jqNModC` evaluation/integrality tail and the prime generation facts |
| `ModularPolynomialUniquenessIrreducible` | 50 | `toAdjoin_eq_minpoly_all`, the datum's characterization |

`ModularPolynomialExistence` is the canonical datum block: `exists_monic_evalAtJ_jqN_eq_zero` proves
integrality over `ℤ[X]` by the modular equation, the private `isFractionRing_polynomial_jq` makes
`ℚ⟮jq⟯` the fraction ring of `ℤ[X]`, and `dataMinpoly N` is `minpoly (Polynomial ℤ) (jqN N)` with its
degree from the capstone. `nonempty_modularPolynomialData N` is `⟨dataMinpoly N⟩`.

## 4. The composite-level closure and the Reserve shelf

The live composite-level API is the canonical datum and its characterization: `dataMinpoly`,
`nonempty_modularPolynomialData`, `toAdjoin_eq_minpoly_all`, and the leading-coefficient consumer
`ModularPolynomialLeadingCoeff`.

The alternate constructions and the retired statements are on the Reserve shelf; nothing in
`FLTForHuman` imports it.

| shelved module | lines | content |
|---|---|---|
| `Reserve/ModularCurve/ModularPolynomialResultant` | 116 | `ModularPolynomialData.dvd_resultant_of_mul` |
| `Reserve/ModularCurve/ModularPolynomialSquarefree` | 425 | the squarefree/biresultant existence |
| `Reserve/ModularCurve/ModularPolynomialComposite` | 21 | header-only: the pins of the retired composite statements (`eq_all`, `phiIrreducible_all`, `phiIrreducible_of_prime`, `exists_phiIrreducible`, and the live-elsewhere `natDegree_coeff_le`/`evalSymm_of_prime`) |

The composite-level irreducibility and uniqueness statements (`eq_all`, `phiIrreducible_all`,
`phiIrreducible_of_prime`, `exists_phiIrreducible`) have no live consumer; the prime-level
irreducibility and symmetry remain in A.

## 5. Numbers

| | modules | lines |
|---|---|---|
| A | 9 | 3332 |
| B, `FunctionFieldGeneration/` | 23 | 7018 |
| B, composite-level tail | 3 | 320 |
| Reserve shelf | 3 | 562 |

The largest modules are `CharP/PrimePowerStep` (1479), `Generic/SlotProduct` (1005), `Existence` (779),
`Split` (701), `Nonmembership` (686), `DegreeStep` (551), `LevelTwo` (440), and `Support/PoleBounds`
(250).
