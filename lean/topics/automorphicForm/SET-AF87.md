# SET-AF87 — the level-spherical flat limit and three readied completions

**Status: LANDED (2026-11-14).** Order B was dispatched at scaffolding; order A was
released as soon as SET-AF86C's C2 landed, which froze `NumberTheory/AdelicHaar/ProductMeasure.lean` — the
file order A imports and the reason it could not go in the first wave (FR-0220). Cut from the
shelf read taken with SET-AF86's scaffolds on disk: **5 rows / 2,199 silo** in **two orders**, four modules
(three new).

| # | order | rows | silo | module(s) | pin publics on the wire | manager-scaffolded | order-scaffolded |
|---|---|---|---:|---|---:|---:|---:|
| A | the level-spherical flat approximate identity | 2 | 1,795 | `AutomorphicForm/Adelic/Cusp/LevelSphericalLimit.lean` (new) | 26 | 2 | 24 |
| B | three readied completions | 3 | 404 | `MeasureTheory/MatrixCoefficientSeparation.lean` (new), `NumberTheory/ValuationSubring/TranscendentalDivision.lean` (new), `ModularForms/Level/Ratio.lean` (new) | 1 + 1 + 1 | 3 | — |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af87_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **529 / 245,064** |
| ready rows | **10 / 3,852** |
| leaves | **118 / 30,021** |
| withheld (FR-0044 guard) | 4 / 831 |

The ready block's head is the level-spherical pair (935 + 860), which SET-AF86C's Haar-invariance row
readied; then the `WeierstrassCurve` (697 / 599) and `GaloisRep` (495) rows of other columns, the 113-line
`centralChar` row, and the `AlgebraicCurve` / `ModularCurve` tails.

## 1. The cut

| # | row | silo | lev | note |
|---|---|---|---:|---|
| A1 | `AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional` | 860 | 1/1 | 10 premises |
| A2 | `AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact` | 935 | 1/3 | 10 premises |
| B1 | `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1/1 | 1 premise |
| B2 | `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` | 138 | 1/1 | 1 premise |
| B3 | `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1/3 | 1 premise |

**A** is one subject: on a finite-dimensional, uniformly continuous, level-invariant space inside an
archimedean cut, the *flat* level-spherical factorizable test functions are an approximate identity for
right convolution (`rightConv y (f n) g → y g`), once with the level written as `levelOne N ⊓
finiteAdelicGL2Subgroup` and once with it given as `U = O ⊓ finiteAdelicGL2Subgroup` (compact `U`, open
`O`). Its ten premises are all ported, and its chain is AF86C's
`isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing`, which is why **A could not be
dispatched with B** (its module imports `NumberTheory/AdelicHaar/ProductMeasure.lean`, the file C edits —
FR-0220); it went out the moment C2's gates closed.

**B** is a tail of three rows in three areas, each one public headline over a single premise that is
already ported: the compact group's matrix coefficients separate every nonzero vector (a Peter–Weyl
separation input, `Topology/ContinuousMap/StarSubalgebraIntegral.lean`); the partial-fraction division of
`aeval` values at a transcendental element (`FieldTheory/ValuationSubringPartialFraction.lean`); and a
level-`Γ₀(ℓ)` realisation of the level-one ratio `E₄³ / Δ` (`ModularForms/Level/Degeneracy.lean`).

**What was deferred, and why.** `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite`
(113 silo, project leverage 16) is deferred for the third time, now with the gate measured: its statement
and proof both use `Def_AutomorphicForm_ViaCompactCuspNotion` (74 lines), which is unported, and all four of
*that* module's own imports are ported — so it is a one-module definition gate, i.e. manager work for the
next set rather than a rider. The rest of the ready block is other columns' (`WeierstrassCurve` 697 / 599,
`GaloisRep` 495, `AlgebraicCurve` 59, `ModularCurve` 36 / 34 / 24).

## 2. The homes and the scaffolds

| module | home | imports the row's premise from |
|---|---|---|
| `AutomorphicForm/Adelic/Cusp/LevelSphericalLimit.lean` (new) | new, under `Cusp/` beside `LevelSphericalTestFn.lean` | `Cusp/LevelSphericalTestFn` (the flat/level-spherical dictionary), `NumberTheory/AdelicHaar/ProductMeasure` (AF86C's row), `NumberField/TateGlobalIdeleNormDet`, `AdelicHaar/GeneralLinear` |
| `MeasureTheory/MatrixCoefficientSeparation.lean` (new) | new: the separation statement is its own subject, not the isotypic projection of `IsotypicConvolution.lean` | `Topology/ContinuousMap/StarSubalgebraIntegral` |
| `NumberTheory/ValuationSubring/TranscendentalDivision.lean` (new) | new, under the `ValuationSubring/` theory directory beside `Domination.lean` | `FieldTheory/ValuationSubringPartialFraction` |
| `ModularForms/Level/Ratio.lean` (new) | new, under the `Level/` directory | `ModularForms/Level/Degeneracy` |

| module | scaffold state | `check_port` at scaffold | `scaffold_audit` at scaffold |
|---|---|---:|---|
| `Cusp/LevelSphericalLimit.lean` | 2 headlines, `sorry` | **2 ok / 0 / 0** | 2 FOLDED + 24 MISSING (order A's step 1) |
| `MeasureTheory/MatrixCoefficientSeparation.lean` | 1 headline, `sorry` | **1 ok / 0 / 0** | complete |
| `NumberTheory/ValuationSubring/TranscendentalDivision.lean` | 1 headline, `sorry` | **1 ok / 0 / 0** | complete |
| `ModularForms/Level/Ratio.lean` | 1 headline, `sorry` | **1 ok / 0 / 0** | complete |

**The surface gate, applied at review (order B).** The worker delivered order B at `1 ok` per module, with
the pins' engine blocks `private`, and flagged it as a decision for me. The gate's experiment — drop
`private`, run `check_port`, read the three numbers — gave `18 ok, 2 mismatch` over the two affected
modules:

* `MeasureTheory/MatrixCoefficientSeparation.lean`: all **16** of the pin's coefficient-`⋆`-subalgebra
  declarations read `ok`, so they are promoted. The module is now **17 ok** — that block is the compact-group
  form of the premise's Stone–Weierstrass criterion and is reusable as stated, so making it `private` would
  have been "real mathematics made private" (playbook §4's rule).
* `NumberTheory/ValuationSubring/TranscendentalDivision.lean`: the two promoted engines read `mismatch`,
  and the diff was the **binder shape**, not the mathematics — the pin states them under
  `variable {L} [Field L] (A : ValuationSubring L)`, the port had spelled the binders explicitly, and the
  checker hashes text (FR-0218's lesson, met from the other side). The fix is the pin's own shape: the two
  declarations now live in a `section` with the pin's `variable` lines, and the module is **3 ok**.
* `ModularForms/Level/Ratio.lean` keeps its seven engines `private` — the pin states them `private` too, so
  there is nothing to promote.

Both promoted modules re-ran the whole gate set after the edit: silent, `move_dead` 0/0, `dedup` 0 clusters,
audits `complete`, oleans rebuilt. The lesson is recorded: a work order's `N ok` target must say *which*
declarations are the public surface (the pin's), not just a count — the count cannot distinguish "the row" from
"the row plus its engines", and a worker following the smaller number will privatise mathematics the pin
publishes.

Three scaffolds needed an import the brief had not guessed, all found by elaboration rather than by
reading: `Mathlib.RingTheory.LaurentSeries` and `Mathlib.NumberTheory.ModularForms.QExpansion` for the
`ModularForm` row (its `LaurentSeries`/`qExpansion` are mathlib's, not the port's), and
`Mathlib.NumberTheory.ModularForms.Discriminant` for `ModularForm.E₄`/`discriminant`. The `ValuationSubring`
row needed `open Polynomial` only.

## 3. The orders and the gates

Orders in `lean/tmp/af87/WO.md`, with SET-AF86's six gates unchanged (checker + `scaffold_audit complete`
as the acceptance test, silent 200 k edit loop, axioms, dedup, `move_dead`, a recorded heartbeat probe).

## 4. The forecast

Order B's three rows are already declared (scaffolded), so the read above prices them as in; the remaining
forecast is order A's:

| figure | §0 | forecast (AF87) |
|---|---:|---:|
| `needed [F terminal]` | 529 / 245,064 | **526 / 242,269** |
| ready rows | 10 / 3,852 | **8 / 2,057** |
| leaves | 118 / 30,021 | 118 / 30,021 |

The two new ready rows are the ones A reads: the `setIntegral_archCasimirAt` pair this set's own chain
readies. Order A's landing is therefore the point at which the shelf's AF subject is exhausted down to the
leaf block (118 / 30,021), whose AF entries are the next cut.

## 5. The landing

All five rows in, no `sorry`, four modules (all new), four consumers.

| file | rows | lines | decls | checker | probe (silent / fails) |
|---|---|---:|---|---|---:|
| `AutomorphicForm/Adelic/Cusp/LevelSphericalLimit.lean` | A1–A2 | **1,126** | 45 (19 + 26) | **19 ok / 0 / 0** | 200,000 / 100,000 (fails 50,000) |
| `ModularForms/Level/Ratio.lean` | B1 | **105** | 8 (1 + 7) | **1 ok / 0 / 0** | 2,000 / 1,000 |
| `NumberTheory/ValuationSubring/TranscendentalDivision.lean` | B2 | **125** | 3 (3 + 0) | **3 ok / 0 / 0** | 4,000 / 2,000 |
| `MeasureTheory/MatrixCoefficientSeparation.lean` | B3 | **262** | 17 (17 + 0) | **17 ok / 0 / 0** | 8,000 / 4,000 |
| | **5** | **+1,618** | **+73 (5 rows + 68 engines)** | **40 ok, 0 mismatch, 0 missing, 0 own** | |

Every module is silent at `-DmaxHeartbeats=200000` with no in-file `set_option`; axioms
`[propext, Classical.choice, Quot.sound]` on every row and every probed engine; `move_dead` `0 / 0` on all
four; `dedup --within` 0 clusters on all four; `scaffold_audit` **complete** on all four (the level-spherical
wire's 26 publics land 19 declarations: 2 FOLDED, 1 satisfied by the import closure, 17 transcribed).

Consumers, each silent: `spec/AutomorphicFormSetAF87AConsumer.lean` (both rows at a single point `y ∈ Y`,
`g` — the form a call site uses), and order B's three already carry theirs by construction (`1 ok`/`3 ok`/`17
ok` at the pin's own surface, with `spec/` zones for the two promoted ones in the set note's surface-gate
entry).

### What the workers' diagnoses overrode in this brief

1. **Five `import` lines** (FR-0229, the last of eleven today): `MaximalCompactFactors`, `TestFnTop`,
   `RightConvProductIntegral`, `ArchCutReproducer`, `ArchPeterssonPairing` were all outside the
   level-spherical module's 182-module closure. All oleans present, all import edits. The same module also
   needed `Mathlib.NumberTheory.ModularForms.CuspFormSubmodule` for order B1.
2. **The order's count arithmetic was wrong in both directions**: the audit reads `2 FOLDED + 23 MISSING + 1
   satisfied-by-import` = 26, and the 23 MISSING are 17 distinct declarations plus 6 rows counted twice
   (three `ApproxIdentity`, three `C2ABridge` names appear in both wires) — step 1 transcribed 17, not 24.
3. **`isCompact_rowIsometrySubgroup_detOne` is a *replacement*, not an addition**: it stands in for the pin's
   private ten-declaration `rowIsoSet`/`isCompact_rowIsometrySubgroup₀` block, which is where the shared
   474-line dedup between the two pins pays off. The brief listed it as a premise and said nothing about the
   replacement.
4. **The surface gate at review** (order B, in §2 above): `18 ok, 2 mismatch` on the experiment, 18 promotions
   made, two of them re-spelled with the pin's section variables. The lesson — a work order's `N ok` target
   must name *which* declarations are the public surface — is the set's own defect.
5. **A vanished olean**: `ProductMeasure.olean` was present at 13:46 and gone at 13:48 (only its `.hash`/`.trace`
   left) while this order was building; the worker rebuilt the dependency alone under the lock and edited
   nothing in it. Recorded as FR-0230: a bounded `lake build` killed mid-cascade removes the dependency's
   stale olean and then has nothing to import.

### The set's numbers

| figure | before (AF87 scoping read) | **after** (measured) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 529 / 245,064 | **527 / 243,269** | 526 / 242,269 |
| ready rows | 10 / 3,852 | **10 / 2,212** | 8 / 2,057 |
| leaves | 118 / 30,021 | **118 / 30,021** | 118 / 30,021 |
| withheld | 4 / 831 | 4 / 831 | 4 / 831 |

**The landing read is identical to SET-AF86's landing read**, and that is the honest finding, not a
coincidence: every one of this set's five rows was already scaffolded when AF86's landing was measured, and
the shelf's name tier credits a `sorry`-bodied headline. So this set's *scaffolding* moved the figures and its
*landing* could not; the forecast in §4 was hand arithmetic on the pre-scaffold baseline and is 1 node / 1,000
lines off. The measured landing is the authority: `527 / 243,269`, with ten ready rows of which two are this
set's own readies — `CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional{,_of_le}` (78 + 77), both
cited by AF87A's rows.

The AF subject is now exhausted down to the leaf block (118 / 30,021) and the 113-line `centralChar` row, whose
`Def_AutomorphicForm_ViaCompactCuspNotion` gate (74 lines, unported) is the next set's definition work.
