# SET-AF108 — the shelf SET-AF107 emptied: the nineteen rows it made ready

**Status: PLANNED (2026-11-27).** The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. SET-AF107 consumed the whole clean ready block; what it left behind is **its own
payoff**: nineteen rows, **4,387 silo**, every one a consumer of a row that set landed (or of the module
that holds it). Eight orders, ten new modules and seven insertions.

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | the divisor's order under a constant field extension | 2 | 773 | `AlgebraicCurve/Genus/ConstantFieldExtensionDivisor.lean` (new), `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (insert) |
| B | the regular prolongation's residue and ord completion | 2 | 443 | `AlgebraicCurve/RegularProlongationResidueOrd.lean` (new) |
| C | the fibre polynomial is the Vélu product | 1 | 544 | `ModularCurve/ModularPolynomialFibreVelu.lean` (new) |
| D | differentials ⊗ cusp forms, and the `ψ`-finrank | 2 | 567 | `ModularCurve/X1/RegularDifferentialsCuspForm.lean` (new), `ModularCurve/Degree/FinrankDedekindPsi.lean` (new) |
| E | the Tate curve's normal forms | 2 | 397 | `TateCurve/SeriesIdentities.lean` (insert) |
| F | the Eisenstein piece's Weyl integrability | 1 | 547 | `EisensteinGeneral/PieceWeylIntegrability.lean` (new) |
| G | the archimedean height's compact cover | 1 | 410 | `AutomorphicForm/Adelic/Siegel/ArchHeightCover.lean` (new) |
| H | the adelic compactness and Fourier leaves | 8 | 706 | `NumberTheory/NumberField/{InfinitePlaceWeightedSum,AdelicCompactness,StandardAddCharTrace}.lean` (new), `NumberTheory/AdelicFourier.lean` (insert ×2), `NumberTheory/NumberField/MixedEmbedding.lean`, `Analysis/Measure/LpFinrank.lean`, `FieldTheory/ValuationSubringValuedField.lean` (insert) |
| **total** | | **19** | **4,387** | 10 new, 7 insertions |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport20.txt)) > build/shelf_af108_read.json
```

The correction list is the `--selfcheck` output of the current tree: **20 names**, byte-identical to
SET-AF107's `unport20_landed.txt` (this set's rows are new declarations, so the set did not change it).

| figure | value |
|---|---:|
| `needed [F terminal]` | **266 / 154,725** |
| ready rows | 22 / 4,460 |
| leaves | 5 / 13,761 |
| withheld (FR-0044 guard) | 5 / 1,648 |

**The cut is nineteen of the twenty-two ready rows** — every row that became ready because SET-AF107
landed, minus the three that are not ready at all (§5): the two definition-gated rows
(`rep_tateModule_jOne_comm`, `defectCoeff_zero`) and one false ready (`exists_sum_smul_eq_of_isIntegralQExp_gamma1`,
whose premise SET-AF107 cut). The leaves block is entirely definition-gated (§5) and is not touched.

Two checks were run on all nineteen rows before writing a line, and both are new instruments of this
column:

* **`premcheck.py`** — is each premise *really* ported, or only last-name-shadowed (the trap that cut a row
  from SET-AF107)? It parses each premise's own `Theorems/` wrapper and looks its declarations up in the
  port **by statement**, not by name. Result: **one** non-`ported` premise out of 47, and it is a
  **generalisation**, not a shadow: the port's
  `AlgebraicCurve.Place.min_ord_le_ord_add` (`Defs/PlaceCalculus.lean`) takes only `f + g ≠ 0` where the
  pin also passes `f ≠ 0` and `g ≠ 0` — a stronger statement the row's proof can use directly. Every other
  premise is statement-identical, and the modules they live in are §1's table.
* **the def-layer read** — every row's `S_` file `import Definitions/…` lines, checked declaration by
  declaration against the port index. The absences are all **structure fields** (`RegularProlongation.integers`,
  `FactorizationDatum.cS`, `AdelicTraceData.traceFin`, …) which the checker does not index, so no row has a
  definition gate.

## 1. The stories

### A — the divisor's order under a constant field extension

Two rows, **773** silo:

* `Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension` (**729**, 10 premises) — the biggest row
  of the shelf: for `F'/K'` a constant field extension of `F/K`, the difference of the two orders of a
  divisor at places over the same point is divisible by the residue degree `[K' : K]` — the arithmetic
  heart of the `mapDomain` dictionary (SET-AF107B/C's rows are its converse direction).
* `Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq` (44) — the **equality**
  companion of SET-AF107B's inequality: with a finite set of exceptional places, the Riemann–Roch finrank
  is preserved by the place reduction.

Homes: the 729 row needs nine premise modules
(`ConstantReductionCorrespondence`, `Genus.ConstantFieldExtensionConsequences`,
`IsCurveOver.{ConstantFieldExtension,EssFiniteType,Transcendental}`, `Place.ConstantFieldExtension`,
`Place.FromValuationSubring`, `RegularProlongationRetraction`, `RiemannRoch.Assembly`) and **no existing
module is above all nine**, so it gets a new one, `AlgebraicCurve/Genus/ConstantFieldExtensionDivisor.lean`.
The 44-row's only premises are SET-AF107B's two rows, so it is an **insertion** into
`Genus/PlaceReductionRiemannRoch.lean` — the module that states them.

### B — the regular prolongation's residue and ord completion

Two rows, **443** silo, both in the `Fin (finrank)`-family of SET-AF107A:

* `exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq` (**237**) — every element of `F` is a
  sum `∑ (c_σ + μ_σ) z_σ` with `c_σ` integral and `μ_σ` of valuation `< 1`, the *multiplicative* form of
  the gauss representation;
* `forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed` (**206**) — the residue span's orders are
  non-negative and a monic polynomial exists, for every valuation subring.

Home `AlgebraicCurve/RegularProlongationResidueOrd.lean` (new): the rows' premises include SET-AF107A's
`RegularProlongationGaussRepresentation.lean` (so `RegularProlongationGaussBasis.lean` cannot host them, the
same FR-0037 shape A met), plus `RegularProlongationGaussDegree`,
`FieldTheory/ValuationSubringResiduePolynomial` (SET-AF107H), `Place/OrdCalculus`, `Defs/PlaceCalculus`,
`DivisorPlaceReduction`, `FieldTheory/ValuationSubringFinrank`, and
`NumberTheory/ValuationSubring/TranscendentalDivision`.

### C — the fibre polynomial is the Vélu product

One row, **544** silo: `ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j` — for a
`ModularPolynomialData ℓ` (`ℓ ≠ 2`) and an `ℓ`-torsion basis of an elliptic `W/K`, the fibre polynomial's
`j`-value is the product of the `j`-invariants of the `ℓ + 1` Vélu quotients. It is the *counting* half of
the modular-polynomial story whose datum half SET-AF106E landed, and its premises are the arithmetic
machinery of the last five sets (`Automorphism.NormalForm`, `ModularPolynomialVelu`,
`Reduction.ReduceHomSurjective`, `Velu.{Discriminant,Reduction}`, `WittVector.Lift`).

Home `ModularCurve/ModularPolynomialFibreVelu.lean` (new): the existing `ModularPolynomialFibreTwo.lean` is
about `ℓ = 2` and is **below** four of the six premise modules (measured), so it cannot host this row.

### D — differentials ⊗ cusp forms, and the `ψ`-finrank

Two rows, **567** silo:

* `exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm` (**329**, 11 premises) —
  the complexified regular differentials of `X₁(M)`'s function field are **linearly equivalent to the
  weight-two cusp forms** at `Γ₁(M)`; the dictionary's `ℂ`-linear form, built on SET-AF107D's two rows
  (the `diffQExp` coefficient map and its regular-differential refinement);
* `finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi` (**238**) —
  `[K(j(q)) : K]` inside the full level-`N` function field is `ψ(N)`: the finrank form of the modular
  polynomial's degree, consuming SET-AF107D's `starBank`.

Homes: `ModularCurve/X1/RegularDifferentialsCuspForm.lean` (new — its premises include
`X1/IntegralityDifferential.lean`, `GenusBound`, `CoeffMap`, `Structure`,
`Canonical/RegularDifferentialsFinrank`, `Gamma1CuspStructure`, `WeightOne/Gamma1IntegralBasis` and
`QExpansionDifferentialLift`, and no existing `X1` module is above all eight) and
`ModularCurve/Degree/FinrankDedekindPsi.lean` (new — above `Degree/{FinrankAdjoinJqNModC,PhiData,PrimeNonAdjoin}`,
`FunctionFieldGeneration/ModularPolynomialExistence` and `StarBank/StarBank`).

### E — the Tate curve's normal forms

Two rows, **397** silo: `pointX_normalForm` (198) and `pointY_normalForm` (199) — the `x`- and
`y`-coordinates as `xfun u + ∑' n, (…)` and `yfun u + ∑' n, (…)`, the normal forms the point-arithmetic
layer starts from. Their only premise is SET-AF107H's `sOne_eq_tsum_xfun`, in the module that holds it, so
both are **insertions** into `TateCurve/SeriesIdentities.lean`. They are also the two rows SET-AF101's
deferral dossier named as the first step of the torsion-parametrisation layer (CARRY-FORWARD): landing
them makes that layer's first step cheaper.

### F — the Eisenstein piece's Weyl integrability

One row, **547** silo: `EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization` — the
integrability of the product of a Weyl translate of a unipotent Eisenstein piece with the factorisation
datum. Its five premises (`AdelicFourier.IntegrableTensor`, `EisensteinGeneral/Factorization`,
`LocalRam`, `LocalUnr`, `NumberField/HeightOneSpectrumSummable` — the last landed by SET-AF107F) put it
above the whole Eisenstein factorisation block; home `EisensteinGeneral/PieceWeylIntegrability.lean` (new).

### G — the archimedean height's compact cover

One row, **410** silo: `AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le` — for
`c > 0`, `u`, `T'` there is a **compact** `K` covering the windowed Siegel set truncated at
`archHeight ≤ T'`, up to `GL₂(F)`-translates. It is the compactness input of every `archHeight`-cut
argument, and its three premises are SET-AF107F's `Units` and `MixedEmbedding` leaves plus
`Adelic/Siegel/WindowCriterion.lean` — the second and third of which are the rows that set landed. Home
`AutomorphicForm/Adelic/Siegel/ArchHeightCover.lean` (new; the `Siegel/` directory's cover family).

### H — the adelic compactness and Fourier leaves

Eight rows, **706** silo, each a consumer of a SET-AF107F/H row, and the set's "small rows" order:

| silo | row | home |
|---:|---|---|
| 214 | `NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le` | `NumberTheory/NumberField/InfinitePlaceWeightedSum.lean` (new) |
| 202 | `NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound` | `NumberTheory/NumberField/AdelicCompactness.lean` (new) |
| 86 | `NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet` | `NumberTheory/AdelicFourier.lean` (insert) |
| 48 | `NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace` | same module (insert) |
| 48 | `NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace` | `NumberTheory/NumberField/StandardAddCharTrace.lean` (new) |
| 22 | `NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate` | `NumberTheory/NumberField/MixedEmbedding.lean` (insert) |
| 74 | `MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict` | `Analysis/Measure/LpFinrank.lean` (insert) |
| 12 | `ValuationSubring.krullDimLE_one_of_isAlgebraic_rat` | `FieldTheory/ValuationSubringValuedField.lean` (insert) |

Two homing notes, both measured: `NumberTheory/NumberField/StandardGlobalAddChar.lean` **declares**
`AdelicTraceData` but carries **no `spec-pin:` line**, so the 48-line `psiK` row cannot be inserted there
(it would never be diffed, FR-0316) — hence the new module above it. And
`NumberTheory/AdelicFourier.lean` is wired but imports only mathlib, so it can take the two Fourier rows
and their `AdelicBox`/`GlobalAddChar`/`MixedEmbedding` imports with no cycle.

## 2. The scaffolds

Sixteen modules are touched before any order starts: **eleven new** (header prose, `spec-pin:` wires, a
narrow import list, the headline declarations at the wrapper's statements, body `sorry`) and **five
insertions** (one or two headlines appended to a wired module, with their wires). All sixteen elaborate at
the 200 k edit-loop cap, silent but for their `sorry`s, and are built:

```bash
cd lean && flock -w 900 /tmp/flt-build.lock timeout 2400 lake build <the 16 modules>
# Build completed successfully (5248 jobs) — no non-`sorry` warning from any of them
```

| order | module | new | scaffold `check_port` |
|---|---|---:|---:|
| A | `AlgebraicCurve/Genus/ConstantFieldExtensionDivisor.lean` (new) | 1 | **1 ok** |
| A | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (insert) | 1 | **25 ok** (24 before) |
| B | `AlgebraicCurve/RegularProlongationResidueOrd.lean` (new) | 2 | **2 ok** |
| C | `ModularCurve/ModularPolynomialFibreVelu.lean` (new) | 1 | **1 ok** |
| D | `ModularCurve/X1/RegularDifferentialsCuspForm.lean` (new) | 1 | **1 ok** |
| D | `ModularCurve/Degree/FinrankDedekindPsi.lean` (new) | 1 | **1 ok** |
| E | `TateCurve/SeriesIdentities.lean` (insert) | 2 | **12 ok** (10 before) |
| F | `EisensteinGeneral/PieceWeylIntegrability.lean` (new) | 1 | **1 ok** |
| G | `AutomorphicForm/Adelic/Siegel/ArchHeightCover.lean` (new) | 1 | **1 ok** |
| H | `NumberTheory/NumberField/InfinitePlaceWeightedSum.lean` (new) | 1 | **1 ok** |
| H | `NumberTheory/NumberField/AdelicCompactness.lean` (new) | 1 | **1 ok** |
| H | `NumberTheory/AdelicFourier/PureTensorSummable.lean` (new) | 1 | **1 ok** |
| H | `NumberTheory/NumberField/StandardAddCharTrace.lean` (new) | 2 | **2 ok** |
| H | `NumberTheory/NumberField/MixedEmbedding.lean` (insert) | 1 | **13 ok** (12 before) |
| H | `Analysis/Measure/LpFinrank.lean` (insert) | 1 | **6 ok** (5 before) |
| H | `FieldTheory/ValuationSubringValuedField.lean` (insert) | 1 | **31 ok** (30 before) |
| **total** | **16 modules** | **19** | **100 ok / 0 / 0 / 0 / 0** |

The set-level **collision probe** (`lean/tmp/af108/collision-probe.lean`, importing all sixteen) is
**silent** — run before dispatch, as every set since SET-AF105 has done.

### 2.1 Three homes the scaffold pass had to move — each caught by an instrument, not by reading

1. **`NumberTheory/AdelicFourier.lean` could not take the 86-line pure-tensor row.** The first scaffold put
   both Fourier rows there; the edit loop failed with `fourierIntegral has already been declared`, which is
   not a duplicate in the file at all but a **cycle**: `AdelicBox.Measure` (the row's premise) reaches
   `AdelicFourier` through `AdelicFourier/Transform.lean`. The row moved to
   `AdelicFourier/PureTensorSummable.lean`. This is FR-0037's shape found *before* dispatch rather than
   mid-order, which is the whole point of scaffolding first.
2. **`Mathlib.NumberTheory.NumberField.AdelicFourier` does not exist** — the module is
   `NumberTheory/AdelicFourier.lean`, and the two 48-line rows' statements need
   `InfiniteAdeleRing.ringEquiv_mixedSpace`, declared in `AdelicFourier/Transform.lean`. So the `addChar`
   row went with the `psiK` row into the new `StandardAddCharTrace.lean` (one subject: the archimedean
   trace ↔ `fourierChar` computation), above `Transform`.
3. **Two statements needed names the wrapper's `open` lines did not supply**, both found by the edit loop:
   order F's `FactorizationDatum`/`adelicWeyl` live under `EisensteinGeneral.Piece` and
   `AutomorphicForm.Adelic.WeylIntertwining` (so the scaffold imports both and opens the former), and order
   H's `IsGlobalAddChar` is `AutomorphicForm.IsGlobalAddChar` — a namespace the *statement* writes bare.


## 3. The pricing

`port_advise` on the 19 rows, then `port_plan`:

| figure | value |
|---|---:|
| raw `S_` lines (47 `S_` files) | 4,387 |
| declaration lines | 3,993 |
| of which duplicate copies | 176 |
| boilerplate (imports/attrs/`p2m`) | 394 |
| distinct declaration groups | 183 |
| **already in the port (vetted)** | **553** |
| **net new math lines** | **3,264** |
| substitutions | 45 trusted / 3 suspect |

**This is the cheapest set of the column per silo**, and that is what a *consumer* set looks like: 553 of
3,993 declaration lines are already public (14 %), against SET-AF107's 7 % — because every row here is a
consumer of a row the previous set landed and its engine is therefore already in the port. The two largest
blocks are the ones the advise places wholesale:

* **order C**: the whole `TDescent.*` base-change engine of `ModularCurve/ModularPolynomialVelu.lean` —
  seventeen rows, `mapFun_add` (28) the biggest — so the 544-line pin is an assembly over an existing
  module;
* **order A**: thirteen rows of the constant-field-extension lifting engine (`W7XL2.liftPlace` cluster,
  `TorsionDescentDeriv.constantsAreBase_of_isAlgClosed`, and two `LowerSemicontinuity` rows from SET-AF107B's
  own module).

The **three suspects** are the parser's type-only `def` matches, each assigned to its order's work order:
`IsLam → ValuationSubring.ZfSol.IsW` and `IsLamPlus → ValuationSubring.P1aSol.IsLam` (B — the pin's
`IsLam`-family against the `ValuationSubring` family's predicates), and
`latPt → NumberField.AdelicFourier.toIntegerLattice` (H — a `def` whose body may be the lattice or only its
carrier).

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6, unchanged from SET-AF107 (§4 of that brief): `check_port` **0 mismatch / 0 missing / 0 own**, the
engine diff by hash, `#print axioms`, the silent edit loop and one locked `lake build`, `dedup --within`,
`move_dead --dry-run`, a heartbeat probe pair recorded and not installed.

The four house policies SET-AF107 settled are now precedents and carry unchanged:

1. **the low-cap probe ladder** for any heartbeat site; a module never installs a `set_option
   maxHeartbeats` (SET-AF107 found three pins whose budgets were unnecessary);
2. **the surface gate at review** (drop `private`, re-run `check_port`, read the three numbers);
3. **no `import Mathlib`** — and only mathlib modules whose `.olean` exists in this checkout;
4. **declaration-scoped linter options only**, with the measured reason in the header (the three
   precedents: C's `linter.style.haveILetI` on two declarations, E's `linter.unusedVariables` on three,
   B's 23 `haveI`s rewritten as `have`).

New in this set, from the last one's frictions: **FR-0316** (a module with no `spec-pin:` line cannot host
a new row — check the wire *and* the import direction before scaffolding), **FR-0318** (a pin row whose
hypotheses are all section variables hashes as its bare conclusion, so the advise "matches" any
same-conclusion row), **FR-0320** (a moved headline's stale `.olean` keeps its name until the old module is
rebuilt).

## 5. Not cut — named and deferred (FR-0040)

* **The three ready rows that are not ready:** `ModularCurve.rep_tateModule_jOne_comm` (24) and
  `TateCurve.defectCoeff_zero` (13) stay held for their definition modules
  (`Def_EllipticCurve_TateModule` 8/100, `Def_TateCurve_Defect` 0/29); and
  `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36) is the **false ready** SET-AF107H found
  (its premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, 261 `S_` lines, is unported and
  its two premises with it) — a small chain, still the next set's business, still registered in
  CARRY-FORWARD.
* **The five leaves, all definition-gated (13,761 silo):** `M4aTorus.completedRayL_fe` (12,126, on
  `Def_NumberField_{CompletedRayL,RayCharacterData,FrobeniusDensity_ClassGroupLSeries}` +
  `NarrowRayClassGroup`), `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` (684, the same pair),
  `NumberField.ncard_primesOver_…` (233, `Def_LanglandsTunnell_NormClass`), and the two Tate-curve
  points-law rows (471 + 247, `Def_TateCurve_TorsionParametrization` 1/43). A definition-layer wave, not
  this set.
* **Withheld by the FR-0044 guard (5 rows / 1,648):** unchanged — the prunable subject's work.
* **`hasCanonicalDivisor_of_fg`'s promotion** (a hub edit, deferred to a quiet tree) and the four other
  CARRY-FORWARD items SET-AF107 registered: not this set's business, and none of them blocks a row here.

## 6. The landing

**LANDED (2026-11-27).** Sixteen modules (eleven new, five insertions), **19 rows / 4,387 silo**,
**107 new checked declarations** (188 in the sixteen modules), **~4,400 written lines**, no `sorry`, no
`sorryAx`, and every module silent at the 200 k edit loop.

| order | module(s) | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `AlgebraicCurve/Genus/ConstantFieldExtensionDivisor.lean` (new) | **610** | **16 ok / 0 / 0** | 26 → 16, **16 hash** | 16 clean | 0 | 0 / 0 | 40,000 / 20,000 (`exists_of_conorm`) |
| A | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (insert) | **1,156** (+6) | **25 ok / 0 / 0** (24 before) | 56 → 25, **24 hash** | 25 clean | 1 (the pin's own pair) | 0 / 0 | 20,000 / — (two declarations, `finrank_adjoin_algebraMap_eq` + `main`) |
| B | `AlgebraicCurve/RegularProlongationResidueOrd.lean` (new) | **531** | **16 ok / 0 / 0** | 22 → 16, **16 hash** | 16 clean | 0 | 0 / 0 | 10,000 / 5,000 |
| C | `ModularCurve/ModularPolynomialFibreVelu.lean` (new) | **502** | **10 ok / 0 / 0** | 30 → 10, **10 hash** | 10 clean | 1 (the pin's `main`↔`solution`) | 0 / 0 | 20,000 / 10,000 |
| D | `ModularCurve/X1/RegularDifferentialsCuspForm.lean` (new) | **419** | **18 ok / 0 / 0** (+1 `private`) | 19 → 19, **18 hash** + 1 unaccounted (the FR-0324 workaround) | 18 clean | 0 | 0 / 0 | 120,000 / 80,000 |
| D | `ModularCurve/Degree/FinrankDedekindPsi.lean` (new) | **282** | **15 ok / 0 / 0** | 17 → 15, **15 hash** | 15 clean | 0 | 0 / 0 | 40,000 / 20,000 |
| E | `TateCurve/SeriesIdentities.lean` (insert) | **836** (+215) | **12 ok / 0 / 0** (10 before) | 57 → 40, **33 hash** + 1 name + 6 pre-existing `solution`s | 12 clean | 0 (all tiers) | 2 / 22 (**pre-existing** dead pair) | 2,500 / 2,200 |
| F | `EisensteinGeneral/PieceWeylIntegrability.lean` (new) | **614** | **1 ok / 0 / 0** (+21 `private`) | 26 → 22, **22 hash** | 1 clean | 0 | 0 / 0 | 10,000 / 5,000 (**floor 5,000** — the statements cost) |
| G | `AutomorphicForm/Adelic/Siegel/ArchHeightCover.lean` (new) | **449** | **14 ok / 0 / 0** | 19 → 14, **14 hash** | 14 clean | 1 (the pin's own pair) | 0 / 0 | 60,000 / 59,000 (`lowRegion_cover`) |
| H | `NumberTheory/NumberField/InfinitePlaceWeightedSum.lean` (new) | **264** | **7 ok / 0 / 0** | 10 → 7, **7 hash** | 7 clean | 0 | 0 / 0 | **120,000 / 100,000** — the set's floor |
| H | `NumberTheory/NumberField/AdelicCompactness.lean` (new) | **257** | **1 ok / 0 / 0** (+4 `private`) | 6 → 5, **5 hash** | 1 clean | 0 | 0 / 0 | 20,000 / 10,000 |
| H | `NumberTheory/AdelicFourier/PureTensorSummable.lean` (new) | **124** | **1 ok / 0 / 0** | 2 → 1, **1 hash** | 1 clean | 0 | 0 / 0 | 10,000 / 5,000 |
| H | `NumberTheory/NumberField/StandardAddCharTrace.lean` (new) | **164** | **2 ok / 0 / 0** | 4 → 2, **2 hash** | 2 clean | 0 | 0 / 0 | 10,000 / 5,000 |
| H | `NumberTheory/NumberField/MixedEmbedding.lean` (insert) | **500** (+8) | **13 ok / 0 / 0** (12 before) | 18 → 13, **13 hash** | 13 clean | 1 (pre-existing) | 0 / 0 | 100,000 / 80,000 (unchanged) |
| H | `Analysis/Measure/LpFinrank.lean` (insert) | **300** (+75) | **6 ok / 0 / 0** (5 before) | 8 → 6, **6 hash** | 6 clean | 0 | 0 / 0 | 40,000 / 20,000 (unchanged) |
| H | `FieldTheory/ValuationSubringValuedField.lean` (insert) | **1,122** (+13) | **31 ok / 0 / 0** (30 before) | 43 → 36, **35 hash** + 1 name (pre-existing) | 31 clean | 0 | 0 / 0 | 20,000 / 10,000 (unchanged) |
| **set** | **16 modules** | **8,110** (~4,400 written) | **188 ok / 0 / 0 / 0 / 0** | **188 by hash**, 1 unaccounted (FR-0324) | **188 clean, no `sorryAx`** | 4 clusters, all recorded and pin-internal | 0 / 0 | no edit-loop gap; two floors (H1 100 k, D1 80 k) |

The set-level gates, run on the landed tree:

* **wave build** — `flock`ed `lake build` of all sixteen: `Build completed successfully (5252 jobs)`, **no
  warning line naming any of the sixteen**;
* **collision probe** — `lean/tmp/af108/collision-probe.lean` over all sixteen: **silent, exit 0** (every
  order had tried it early and hit a missing `.olean`; the set-end run is the FR-0274 gate);
* **home audit** — `lean/tmp/af108/homes_audit.py` over the landed tree: **69 premise edges over 19 rows,
  `problems 0`** — no order hit the import-direction cycle that re-homed a row in SET-AF107;
* **cross-module `dedup`** over all sixteen (`--cross --min-cost 8`, two groups): **0 duplicate clusters,
  0 removable lines**;
* **consumer zone** — `spec/SetAF108Consumer.lean`, two zones, exit 0, and both are genuine
  *compositions*, not instantiations: **(1)** order C's product formula with the datum hypothesis
  **eliminated** through the port's `nonempty_modularPolynomialData` (the form a call site wants), and
  **(2)** order E's two normal forms **composed with** order H's `pointX/Y_zpow_mul` — the normal forms at
  every `q`-translate of `u`, which is the form the point-arithmetic layer works in.

### 6.1 What the orders decided, and the three suspects

* **`IsLam → ZfSol.IsW` — the advise was wrong** (order B). The pin's predicate is the *strict*
  `IsGoodAt` shape (one coefficient exactly 1, all others `< 1`); `IsW` asks only `≤ 1` with one `= 1`.
  Measured: `IsLam → IsW` provable, not conversely; and the row-237 headline writes the clause out itself,
  so substituting would have changed the statement. Restated at the pin's body.
* **`IsLamPlus → P1aSol.IsLam` — right and definitional** (order B): `↔` closes by `Iff.rfl`; kept as a pin
  `def` because `main`'s statement names it.
* **`latPt → NumberField.AdelicFourier.toIntegerLattice` — right and body-for-body** (order H): the same
  term, with `toIntegerLattice_injective` as the pin's `latPt_injective`; both rows imported, neither
  re-proved.
* Two of this set's pins are **public in the pin, `private` in the port**, so their consumers transcribed
  them: `ArchKType.majorant_integrable` (F) and the nine `W7XL2`/`TorsionDescentDeriv` rows (A). Both
  promotions are registered in CARRY-FORWARD; A's is not mechanical (two of the nine also need the hub's
  `private divOf`).
* **Three `private` surfaces were measured and deliberately not promoted** (orders E, F, H's
  `AdelicCompactness`): the pin keeps them `private`, so the 22-ok / 22-ok / 5-ok surface readings are hash
  credit, not a public surface claim.
* **Linter policy held**: order B silenced nothing at all, F carried three declaration-scoped
  `linter.style.haveILetI` (instance bindings that `have` cannot supply), C carried five declaration-scoped
  ones. No module-wide silencing anywhere.

### 6.2 Plan vs actual

| figure | plan (§1, §3) | actual |
|---|---:|---:|
| rows / orders | 19 / 8 | **19 / 8** |
| silo | 4,387 | **4,387** |
| written lines | net-new 3,264 predicted | **~4,400** (+35 % over the net-new, **+0.4 % over the silo**) |
| modules | 16 scaffolded | **16** |
| checked declarations | not predicted | **107 new** (188 in the sixteen modules) |
| recorded edit-loop gaps | 0 | **0** |

The written-lines figure lands almost exactly on the silo (4,400 against 4,387) — the closest of any set in
the column, and what a *consumer* set should look like: `port_plan`'s net-new (3,264) under-predicts because
it counts proof text, while a module also pays for statements, headers and the `TDescent`-style assembly
rows it declares even when the proofs are one-liners.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af108_final.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 266 / 154,725 | **247 / 150,338** |
| ready rows | 22 / 4,460 | **14 / 5,576** |
| leaves | 5 / 13,761 | 5 / 13,761 |
| withheld (FR-0044 guard) | 5 / 1,648 | 5 / 1,648 |

The delta is **−19 nodes / −4,387 lines**, *exactly* the cut. The correction list is unchanged (the same 20
names, `--selfcheck` re-run on the landed tree) because this set's rows are new declarations.

**Eleven rows became ready (5,503 silo)** — and the shape of the new head is the story:

* **`EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant`
  (2,468)** — order F's consumer, and by far the largest row on the shelf: the entire partial Euler
  product's identification with the Whittaker coefficient, which F's integrability row was the last input
  for;
* order B's two: `exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one` (**783**) and
  `exists_forall_finrank_residueSpan_inf_add_card_le` (**638**) — the `krullDimLE`-conditioned and
  finrank forms of the residue-span story;
* order A's `Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction` (**485**);
* order D's `ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq` (299) and
  `modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos` (114);
* order E's `TateCurve.pointX_qExpansion` (284) and `pointY_qExpansion` (284) — the `q`-expansion forms of the
  two normal forms, which are the next step of the torsion-parametrisation layer;
* order H's `AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual` (85) and
  `mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice` (50);
* `NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace` (13) — the standard additive
  character's version of the row H3 landed.

The three rows that stayed are the two definition-gated ones (`rep_tateModule_jOne_comm` 24,
`defectCoeff_zero` 13) and the false ready (`exists_sum_smul_eq_of_isIntegralQExp_gamma1` 36).

## 8. What the set leaves behind

**The shelf is now a consumer shelf with one giant row on it**, and the next set is a different shape from
the last three: 5,576 ready silo of which 2,468 is a single Eisenstein row, and the five leaves are all
definition-gated and unchanged.

Five things carried beyond the files:

* **five new frictions**, and three of them are about *the checker and the elaborator disagreeing about what
  a statement is*: **FR-0321** (a pin that writes its binders explicitly must be written with them, or
  `check_port` reads a false MISMATCH — FR-0318's mirror image), **FR-0322** (a namesake collision is fixed by
  `open` order, not by qualification, because the checker hashes text; plus `set_option … in` must precede
  the doc comment), **FR-0323** (a local hypothesis of class type is already an instance, so the pin's
  `haveI := h` and the `linter.style.haveILetI` complaint are avoidable), **FR-0324** (a public lemma whose
  signature fixes an instance is `ok` and unappliable — the one failure class no gate sees), and the
  set-level note that **the collision probe cannot run until the last order lands** (every order discovered
  it; the cure is an order-scoped probe over built modules plus a name sweep, then the full probe at set
  end).
* **three carry-forward items**: `ArchKType.majorant_integrable`'s promotion (deletes order F's 18-line
  copy), the nine `W7XL2`/`TorsionDescentDeriv` promotions (with `divOf`, or re-routed — order A's route is
  the model), and the `CoeffMap.linearIndependent_coeffMap_comp_of_linearIndependent` instance fix (state the
  polymorphic form as a *second* lemma, keep the pin's row as its corollary, so the checker stays green).
* **the column's substitution record changed character**: `port_plan`'s "already in the port" is 553 of
  3,993 (14 %) here against SET-AF107's 7 %, and one row (G) was 369 of 388 — i.e. 6 net-new lines. The
  instrument that matters for such a set is `premcheck.py`'s *statement-level* premise check, not the line
  budget: a consumer set's risk is a premise that is only name-matched, and this set had none (one
  generalisation, zero shadows, out of 48).
