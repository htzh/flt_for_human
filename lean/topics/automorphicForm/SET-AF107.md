# SET-AF107 — the ready shelf's whole clean block: gauss representation, Riemann–Roch under place reduction, Pic0 base change, the star bank, and eleven leaves

**Status: PLANNED (2026-11-27).** The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. It is deliberately the **largest set of the column**: it clears every row of the
ready block and every leaf whose `S_` file passes the definition gate, **27 rows / 6,433 silo**, in
**eight orders** and **thirteen new modules plus four insertions**. What it does not take is exactly
the definition-gated residue (§5): the ray-class L-series pair, the Langlands–Tunnell norm-class leaf,
the Tate curve's torsion parametrisation, the `p`-adic Tate module row, the Tate defect row, and
`M4aTorus.completedRayL_fe`.

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | the gauss representation of the integers | 2 | 1,392 | `AlgebraicCurve/RegularProlongationGaussRepresentation.lean` (new) |
| B | Riemann–Roch under a place reduction | 2 | 1,197 | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (new) |
| C | Pic0 under a constant field extension | 2 | 562 | `AlgebraicCurve/Pic0/BaseChange.lean` (new), `AlgebraicCurve/ConstantReductionCorrespondence.lean` (insert) |
| D | the star bank and the cusp-form differential | 2 | 680 | `ModularCurve/StarBank/StarBank.lean` (new), `ModularCurve/X1/IntegralityDifferential.lean` (insert) |
| E | the `q`-expansion of a slash by a peaked auxiliary | 1 | 951 | `ModularForms/QExpansionSlashCoeff.lean` (new) |
| F | the archimedean and mixed-embedding leaves | 9 | 821 | `NumberTheory/NumberField/{MixedEmbedding,HeightOneSpectrumSummable,UnitsLog,InfinitePlaceSign}.lean` (new), `RingTheory/DedekindDomain/HeightOneSpectrumRat.lean` (new), `Analysis/Measure/LpFinrank.lean` (new) |
| G | the isogeny leaves: cyclic quotients and reduction | 2 | 425 | `WeierstrassCurve/Velu/StepCurveSubgroup.lean` (insert), `WeierstrassCurve/Velu/Reduction.lean` (new) |
| H | the small rows' subject homes | 6 | 369 | `FieldTheory/ValuationSubringValuedField.lean` (insert), `FieldTheory/ValuationSubringResiduePolynomial.lean` (new), `TateCurve/SeriesIdentities.lean` (insert), `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` (insert) |
| **total** | | **26** | **6,397** | 12 new, 5 insertions |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af107/unport20.txt)) > build/shelf_af107_read.json
```

The correction list is the `--selfcheck` output of the **current** tree, re-taken at the start of this
scoping: 20 false ported markers, byte-identical to SET-AF106's
(`lean/tmp/af107/unport20.txt` diffs empty against `lean/tmp/af106/unport20.txt`). Quote this figure
with the marker set that produced it; a stale list understates the shelf.

| figure | value |
|---|---:|
| `needed [F terminal]` | **292 / 161,122** |
| ready rows | 18 / 5,224 |
| leaves | 16 / 15,007 |
| withheld (FR-0044 guard) | 5 / 1,648 |

The shelf is the same one SET-AF106's landing left (`292 / 161,122` — its §7 figure, reproduced to the
line), and this set consumes everything on it that is not behind a definition gate: **the whole ready
block except two rows (37 silo)** and **eleven of the sixteen leaves**. After it, the shelf is the
definition layer's.

## 1. The stories

### A — the gauss representation of the regular prolongation's integers

Two rows, **1,392** silo, both stated over a finite family of regular prolongations `R i` of one
`A`-algebra `F`:

* `exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq` (**1,116**, 9 premises) — the
  **gauss basis**: the `F`-basis of the adjoined field whose every element is in *every* `(R i).integers`,
  which is simultaneously a basis over `L` and a valuation-theoretically integral basis (the third
  conjunct quantifies over all valuation subrings containing `L` and `f`), and which represents every
  integral element with a `p/q` coefficient pair (`p` integral, `q` a unit of `A`);
* `forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf` (**276**, 5 premises) — the residue of an
  element of the intersection of the residue spans is a constant.

This is the pin's *infra* layer at the top of the `RegularProlongation` family: it consumes
AF106C's `exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed`
(`DivisorPlaceReduction.lean`) and the family's own `NonunitSmul` / `ResidueBasis` rows.

**Landed (2026-11-27): 1,469 lines, 54 declarations, 54 ok, 53/54 by hash, silent at 200 k.** Two
findings the order produced, both about the *advise* rather than the mathematics: (i) the pin's `IsMW`
is the **maximal-ideal numerator** predicate, and its body is `ValuationSubring.ZfSol.IsMW`
(`ValuationSubringPolynomial.lean:391`) byte for byte — `port_advise` named `ZfSol.IsW` instead, i.e. the
wrong twin of the pair; the three `IsT`/`IsW`/`IsMW` predicates were restated inside the module because
the pin's statements pass `L` by name (`IsT (L := L) f u`) while the port's `InT` takes it positionally,
so importing would have MISMATCHed four rows (the pin's own file restates them too); (ii) the advised
`linearIndependent_adjoin → …_adjoinField_z` substitution is a **false match**: the two statements hash
equal only because the pin's declaration text is the bare conclusion with every hypothesis a *section
variable*, so the parser's signature stops at `:=` (FR-0318) — it was transcribed, not imported.

**Home `AlgebraicCurve/RegularProlongationGaussRepresentation.lean` (new), and it must be new.** The
obvious home, `RegularProlongationGaussBasis.lean`, is *below* three of the row's premises —
`RegularProlongationNonunitSmul.lean`, `RegularProlongationResidueBasis.lean` and
`ConstantReduction`'s consumer `DivisorPlaceReduction.lean` all import it, so inserting there closes a
cycle. No existing module imports both `DivisorPlaceReduction` and `RegularProlongationNonunitSmul`;
that empty cell of the import graph is what the new module fills. This is the FR-0037/0038 rule's
third recurrence in the column and the reason A is a new module rather than an insertion.

### B — Riemann–Roch under a place reduction

Two rows, **1,197** silo, one subject: *what a place reduction does to the Riemann–Roch space*.

* `Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le` (**687**, **14
  premises**) — the Riemann–Roch space of the reduced divisor has finrank at most that of the original
  (`finrank 𝓛(mapDomain ρ D) ≤ finrank 𝓛 D`), with the finite set of places that the proof needs to
  control;
* `Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction` (**510**, 7
  premises) — the same inequality in the form the genus comparison consumes, from the span of the
  residue image.

The 14-premise row is the set's named risk (`premises` is a risk column, not a size column): it
consumes the retraction (`RegularProlongationRetraction.lean`), AF106C's `mapDomain`-commutation
(`DivisorPlaceReduction.lean`), the constant-field-extension place calculus
(`Place/ConstantFieldExtension.lean`), the genus equality (`Genus/ConstantFieldExtension.lean`), the
index theorems (`Genus/Index.lean`, `Genus/Stichtenoth.lean`) and the assembly
(`ResidueTheorem/RRAssembly.lean`). Give it its own wall time.

Home `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (new), above `RRAssembly`,
`Place/ConstantFieldExtension`, `Genus/{Index,Stichtenoth,ConstantFieldExtension}` and
`DivisorPlaceReduction`.

### C — Pic0 under a constant field extension

Two rows, **562** silo:

* `Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange` (**532**, 7 premises) — a lifted
  correspondence that is a coboundary upstairs is a coboundary after the free-algebra base change: the
  Pic0-side form of `Divisor.mapDomain_placeReduction_correspondence`;
* `exists_constantReduction_of_constantFieldExtension` (**30**, 2 premises) — a constant reduction
  exists as soon as the constant field's valuation subring has a section — six lines of proof over
  AF106C's section row, and the cheapest row of the set.

Homes: the Pic0 row in `AlgebraicCurve/Pic0/BaseChange.lean` (new — the `Pic0/` directory's fourth
module, beside `DivisorPairing`/`Torsion`/`WeilPairing`), the 30-line row in
`AlgebraicCurve/ConstantReductionCorrespondence.lean` (insertion; it is the module that already states
the `mapDomain_placeReduction_correspondence` row). Its proof opens with the Chevalley extension
`IsAlgClosed.exists_valuationSubring_ringHom_retraction`, so the insertion adds
`RingTheory/Valuation/ChevalleyExtension` and `DivisorPlaceReduction` to that module's imports — both
import-safe (neither reaches it).

### D — the star bank, and the cusp-form differential's `q`-expansion

Two rows, **680** silo, both `ModularCurve` `q`-expansion statements:

* `StarBank.starBank` (**453**, 11 premises) — the star bank itself: the `ℓ`-adic bank of
  `q`-expansions closed under `*`, from the Eisenstein series `E₄³/Δ`'s Hasse derivatives, its count,
  its normalisation (`deltaNorm`), and the prime non-adjoin input;
* `exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials`
  (**227**, 6 premises) — an integral cusp form whose `q`-expansion coefficients lie in `ι₀.range` gives
  a **regular differential** whose `diffQExp` coefficient map is that `q`-expansion. This is the
  `regularDifferentials` refinement of AF102's `QExpansionDifferentialLift` row, and it is the input the
  `X₁` `q`-expansion ↔ differential dictionary consumes.

Homes: the star bank in `ModularCurve/StarBank/StarBank.lean` (new; the `StarBank/` directory's third
module, above `Hasse`/`Norm`), and the differential row in `ModularCurve/X1/IntegralityDifferential.lean`
(insertion). The differential row's home was first cut as `QExpansionDifferentialLift.lean` — the module
that holds the row it refines — and the order's first report showed that this is a **cycle**: its first
premise *is* `X1/IntegralityDifferential.lean`, and the chain
`X1/IntegralityDifferential → X1/GenusBound → X1/JqRamification → Analytic/JqModCIntegral →
QExpansionDifferentialLift` puts QEDL above its own premise, so the proof is unprovable at that home
(the module already records FR-0280's shape for its previous row, and the scaffold read green only
because its body was `sorry`). The re-home is the §4 rule applied: the row's subject is the
*regular differential*, and its premise module is the home. Counts: `QExpansionDifferentialLift` returns
to **57 ok**, `X1/IntegralityDifferential` goes **5 → 6 ok**.

### E — the `q`-expansion of a slash by a peaked auxiliary

One row, **951** silo: `ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` (8 premises) — if
`f` is a cusp form whose `q`-expansion coefficients lie in a subring after multiplication by a *peaked*
auxiliary form, then they lie in it outright. The proof is the pin's `T`/`S` transversal argument over
`Γ₀(N)`-cosets: `exists_levelOne_coe_eq_sum_slash`, `exists_finset_transversal_adapted_T_S`,
`qExpansion_coeff_mul_width`, `qExpansion_coeff_sum_vAdd_eq_mul_coeff` and the
`isBigO`-vanishing of the non-constant terms.

This is the row every set since SET-AF104 named as "the one single-row `ModularForm` story; it wants an
order of its own and a `ModularForms` home". It gets both here. Home
`ModularForms/QExpansionSlashCoeff.lean` (new), above `LevelOneSlash`,
`IsArithmeticQExpansion`, `FrickeReciprocity` and `NumberTheory/ModularForms/QExpansionCoeff.lean`.

### F — the archimedean and mixed-embedding leaves

Nine rows, **821** silo, all mathlib-shaped (**no `Definitions/` import in the `S_` file** — checked per
row, FR-0298) and yet all deferred by earlier sets on a definition-layer reading that does not survive
the check: `NumberField.mixedEmbedding` is **mathlib's** namespace
(`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic`), not a pin `Def_` module. The rows:

| row | silo | module |
|---|---:|---|
| `mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg` | 237 | `NumberTheory/NumberField/MixedEmbedding.lean` (new) |
| `mixedEmbedding.exists_forall_norm_embedding_sub_le` | 71 | same |
| `mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate` | 67 | same |
| `mixedEmbedding.trace_mixedEmbedding` | 17 | same |
| `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` | 69 | `NumberTheory/NumberField/HeightOneSpectrumSummable.lean` (new) |
| `Units.exists_forall_abs_sub_mult_mul_log_le` | 98 | `NumberTheory/NumberField/UnitsLog.lean` (new) |
| `InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` | 94 | `NumberTheory/NumberField/InfinitePlaceSign.lean` (new) |
| `IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat` | 20 | `RingTheory/DedekindDomain/HeightOneSpectrumRat.lean` (new) |
| `MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` | 148 | `Analysis/Measure/LpFinrank.lean` (new) |

Three of them carry project fan-in worth naming: `summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt`
(41 citers), `InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` and
`Units.exists_forall_abs_sub_mult_mul_log_le` are the archimedean engine of the height and zeta
machinery. The pin is `v4.33.1` and the port `v4.34.0`, so **API drift is this order's risk**, not line
count: every statement here names mathlib objects, and a rename in the canonical embedding's API shows
up as a statement that will not elaborate. The scaffold pass is the measurement (§2).

### G — the isogeny leaves

Two rows, **425** silo, `WeierstrassCurve`:

* `stepCurve_stepSubgroup_two_eq` (**231**) — the cyclic subgroup of the `stepCurve` at `p = 2` is the
  one `stepSubgroup` names: the definitional bridge the `ℓ = 2` Velo quotient needs;
* `exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` (**194**) — a point map to the
  Velo quotient that commutes with the reduction homomorphism.

Both definition closures are ported (`Def_WeierstrassCurve_{CyclicQuotientJ,VeluPointMap2,Velu,
OddOrderSummingSet,ReduceHom}`: 52+14+29+5+17 of 52+14+30+5+18 public), so this is a proof order, and
it is the pair SET-AF101 deferred as "a cyclic-quotient set's rows".

### H — the small rows' subject homes

Seven rows, **405** silo, in five homes chosen by subject rather than by the row's namespace:

| row | silo | home |
|---|---:|---|
| `ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one` | 75 | `FieldTheory/ValuationSubringValuedField.lean` (insert) |
| `ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem` | 42 | `FieldTheory/ValuationSubringPolynomial.lean` (insert) |
| `TateCurve.sOne_eq_tsum_xfun` | 101 | `TateCurve/SeriesIdentities.lean` (insert) |
| `TateCurve.pointX_zpow_mul` | 22 | same |
| `TateCurve.pointY_zpow_mul` | 22 | same |
| `AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep` | 107 | `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` (insert) |

The seventh row this order was scoped with, `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`
(36), was **cut mid-order at a missing premise** (§5): its first premise is not in the port, and the
port's same-last-name declaration is the *`CuspForm`* statement — a false ready row, not a home.

Each is a **consumer** of a row a recent set landed — the `ValuationSubring` pair of
`ValuationSubringValuedField`'s `ringKrullDim`/`adjoin` engine, the three `TateCurve` rows of
`SeriesIdentities`' convergence block, the cuspidal-spectrum row of AF106D's
`ConstituentIntersection`, the `Γ₁` integral `q`-expansion row of the `WeightOne` integrality engine —
which is why every one of them is small and why their homes are insertions (except the last, which has
no module to sit in: `ModularCurve/X1/Defs.lean` is below its two `ModularForms/WeightOne` premises).

## 2. The scaffolds

Twenty modules were scaffolded before any order started: **thirteen new** (header prose, `spec-pin:`
wires, a narrow import list, the headline declarations at the wrapper's statements, body `sorry`) and
**six insertions** (one to three headlines appended to a wired module, with their wires). Nineteen
remain — order H's `ModularCurve/WeightOneIntegral.lean` was cut with its row (§5) — and order D's
insertion moved up one module during the order (§1 D, the re-home). All twenty elaborate at the 200 k
edit-loop cap, silent but for their `sorry`s, and are built:

```bash
cd lean && flock -w 900 /tmp/flt-build.lock timeout 2400 lake build <the 20 modules>
# Build completed successfully (5182 jobs) — no non-`sorry` warning from any of them
```

| order | module | new | scaffold `check_port` |
|---|---|---:|---:|
| A | `AlgebraicCurve/RegularProlongationGaussRepresentation.lean` (new) | 2 | **2 ok** |
| B | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (new) | 2 | **2 ok** |
| C | `AlgebraicCurve/Pic0/BaseChange.lean` (new) | 1 | **1 ok** |
| C | `AlgebraicCurve/ConstantReductionCorrespondence.lean` (insert) | 1 | **14 ok** (13 before) |
| D | `ModularCurve/StarBank/StarBank.lean` (new) | 1 | **1 ok** |
| D | `ModularCurve/X1/IntegralityDifferential.lean` (insert, **re-homed** by the order) | 1 | **5 ok** → 6 with the row |
| E | `ModularForms/QExpansionSlashCoeff.lean` (new) | 1 | **1 ok** |
| F | `NumberTheory/NumberField/MixedEmbedding.lean` (new) | 4 | **4 ok** |
| F | `NumberTheory/NumberField/HeightOneSpectrumSummable.lean` (new) | 1 | **1 ok** |
| F | `NumberTheory/NumberField/UnitsLog.lean` (new) | 1 | **1 ok** |
| F | `NumberTheory/NumberField/InfinitePlaceSign.lean` (new) | 1 | **1 ok** |
| F | `RingTheory/DedekindDomain/HeightOneSpectrumRat.lean` (new) | 1 | **1 ok** |
| F | `Analysis/Measure/LpFinrank.lean` (new) | 1 | **1 ok** |
| G | `WeierstrassCurve/Velu/StepCurveSubgroup.lean` (insert, **migrated**) | 1 | **2 ok** (1 before) |
| G | `WeierstrassCurve/Velu/Reduction.lean` (new) | 1 | **1 ok** |
| H | `FieldTheory/ValuationSubringValuedField.lean` (insert) | 1 | **30 ok** (29 before) |
| H | `FieldTheory/ValuationSubringResiduePolynomial.lean` (new) | 1 | **1 ok** |
| H | `TateCurve/SeriesIdentities.lean` (insert) | 3 | **10 ok** (7 before) |
| H | `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` (insert) | 1 | **3 ok** (2 before) |
| ~~H~~ | ~~`ModularCurve/WeightOneIntegral.lean` (new)~~ — **cut mid-order**, §5 | ~~1~~ | deleted |
| **total** | **19 modules on disk** | **26** | **135 ok / 0 / 0 / 0 / 0** |

The set-level **collision probe** (`lean/tmp/af107/collision-probe.lean`, importing all twenty) is
**silent** — run before dispatch, as SET-AF105 taught (a `Definitions` port can collide with an
already-public declaration, and no per-module gate sees it).

### 2.1 Two homing decisions the scaffold pass made, both measured

* **Order A could not be an insertion.** `RegularProlongationGaussBasis.lean` is below three of the
  gauss row's premises (`RegularProlongationNonunitSmul`, `RegularProlongationResidueBasis`,
  `DivisorPlaceReduction` all import it), so it is a new module in the empty cell above all of them.
* **Order G's `StepCurveSubgroup.lean` was a legacy module** (in the frozen checker's `PORT_FILES`,
  no `spec-pin:` wire). The ℓ = 2 row's subject *is* that module, so the module was migrated in the
  same touch: its own wire (its `Theorems/` wrapper and `S_` copy, both already in `SOURCES`), the
  `PORT_FILES` row deleted, `check_port` **2 ok**, silent build. That is the §4 rule paid rather than
  dodged.
* **Order H could not use `ValuationSubringPolynomial.lean`** for the residue-polynomial row: the
  module is *unwired*, and the checker iterates a module's own declarations, so a declaration added
  there would never be diffed. The row got a new module above both of its premise modules instead.


## 3. The pricing

`port_advise` on the 27 rows, then `port_plan`:

| figure | value |
|---|---:|
| raw `S_` lines (47 `S_` files) | 6,433 |
| declaration lines | 5,982 |
| of which duplicate copies | 166 |
| boilerplate (imports/attrs/`p2m`) | 451 |
| distinct declaration groups | 269 |
| **already in the port (vetted)** | **425** |
| **net new math lines** | **5,391** |
| substitutions | 39 trusted / 2 suspect |

**This is the column's most expensive set per silo**, and the inverse of SET-AF106: 425 of 5,982
declaration lines are already in the port (7 % against AF106's 33 %), because these rows are the
*engines*, not the consumers — the pin's own proof text is what has to be written. Two hundred and
sixty-nine distinct declaration groups over 27 rows is a flat public surface with little shared prelude;
the biggest single block is order A's `exists_lift`/`finrank_le`/`const` (227 lines, nothing in the
port), and the two largest substitutions are order B's `sigma` block (36+14+11+5+4+2 per row, in
`DeuringNormResidue.lean`) and order F's `summable_absNorm_rpow_neg` (58 lines — the order found the
copy at `NumberField.TateGlobal.summable_absNorm_rpow_neg`, `TateGlobal/PlaceSum.lean:121`, and *imported*
it, so the 425 figure undercounts by those 58 lines because the advise is name-anchored, FR-0314).
B measured its `sigma` caveat away: the port's copies are byte-identical **at the same `A`-hypotheses**
(`A`, `hKA`, `hArat`), so the whole block is a clean import and the order wrote only the three rows the
port lacks (`sigma_apply`, `sigma_algebraMap`, `sigma_surjective`).

The **two suspects** are the parser's type-only `def` matches, both read at order level: `IsMW →
ValuationSubring.ZfSol.IsW` (A — and the advise paired the *wrong twin*: the pin's `IsMW` is
`ZfSol.IsMW` byte for byte, so the row restated its three `Is`-predicates rather than importing them) and
`Fb → ModularCurve.x1FunctionFieldBar` (D — an `abbrev` against the row's explicit `↥(…)`). A third,
different trap the A order met is FR-0318: a pin row whose hypotheses are all *section variables* hashes
as its bare conclusion and so "matches" any port row with the same conclusion
(`linearIndependent_adjoin` against the port's `Σ i, Fin (d i)`-indexed twin).

The three **big orders** are priced at 1,392 (A), 1,197 (B) and 951 (E) silo; the other five are
between 405 and 821 and are transcription rather than engine work.

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` **0 mismatch / 0 missing / 0 own** with every declaration `ok`; the engine diff;
`#print axioms`; the silent edit loop and one locked `lake build`; `dedup.py --within`; `move_dead.py
--dry-run`; a heartbeat probe pair recorded and **not installed**. The house policies of SET-AF104/105/106
carry unchanged:

1. **the low-cap probe ladder** for any heartbeat site — probe at 20 k first, and only then up; a
   module never installs a `set_option maxHeartbeats`, supplying the instance by hand is the first cure;
2. **the surface gate at review** (drop `private`, re-run `check_port`, read the three numbers);
3. **no `import Mathlib`** in a new module; the import list is `premise_imports.py`'s plus what
   elaboration asks for;
4. **`flock`ed, backgrounded `lake build`** of the module alone; no tree build; no `lake env lean`
   against the tree while a build is in flight;
5. after any header-prose edit, run the edit loop, not just the checker (**FR-0315**);
6. `check_port`'s count is a *size*, not an acceptance test (**FR-0226**): the acceptance test is
   `scaffold_audit: complete`.

The frictions this set's pins can hit, from the work order preamble: FR-0266, FR-0298 (a leaves row's
gate is the `S_` file's `Definitions` imports), FR-0306–FR-0315 (the AF106 batch), and FR-0049 (a
statement whose vocabulary is not a graph node).

## 5. Not cut — named and deferred (FR-0040)

* **The definition-gated leaves, five rows / 13,761 silo:**
  `M4aTorus.completedRayL_fe` (12,126) — its `S_` file alone imports four `Definitions` modules the
  port lacks (`NumberField_CompletedRayL` 0/4, `NumberField_RayCharacterData` 0/10,
  `FrobeniusDensity_ClassGroupLSeries` 0/5, `NarrowRayClassGroup` 4/67); it is a column, not a row;
  `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` (684) — the same `CompletedRayL` +
  `RayCharacterData` gate;
  `NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one` (233) —
  `Def_LanglandsTunnell_NormClass` 0/9;
  `TateCurve.point_mul_eq_add_of_norm_le_one` (471) and `…_of_norm_eq_one` (247) — the gate SET-AF101
  measured at 28 files / 9,859 lines (`Def_TateCurve_TorsionParametrization` 1/43 here).
  These five are one wave of definition-layer work, and it is not this set.
* **Two ready rows held for a definition gate, not for size:**
  `TateCurve.defectCoeff_zero` (13) — `Def_TateCurve_Defect` 0/29, a module the port does not carry at
  all; and `ModularCurve.rep_tateModule_jOne_comm` (24) — `Def_EllipticCurve_TateModule` 8/100, the
  `p`-adic Tate module the port's `X1/HeckeModule.lean` already records as absent. Neither is cuttable
  into this set: each is cheap only *after* its definition module exists.
* **Cut mid-order — `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36 silo).** Its first
  premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (**261 pin `S_` lines**) is not in
  the port; the port's only same-last-name declaration is
  `CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (`ModularForms/WeightOne/Gamma1IntegralBasis.lean`,
  in a pin-label namespace `WLightS11.S_CuspForm_…`), a **different statement on a different type** — so
  the name tier credited the row as *ready* and my recon's premise read inherited the shadow (**FR-0047**'s
  class, not an FR-0266 `def` suspect). The missing node is itself a two-premise chain
  (`ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp`,
  `ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply`), so the row plus its closure is a small order of
  the next set, not a patch to this one. Order H landed six rows / 369 silo, and its scaffold module
  `ModularCurve/WeightOneIntegral.lean` was deleted rather than left `sorry`-bodied (SET-AF101's
  precedent).
* **Withheld by the FR-0044 guard (5 rows / 1,648):** the same five SET-AF106 §5 names — the
  `periodLatticeOf` quotient row (817), the two `padicInt` Tate-module rows (327, 283), the
  prescribed-divisor `_complex` row (126) and the `Pic0` torsion finiteness (95). They are the prunable
  subject's work.

## 6. The landing

**LANDED (2026-11-27).** Twenty modules (twelve new, seven insertions, one legacy migration), **26 rows /
6,397 silo**, **221 new checked declarations**, **7,074 written lines**, no `sorry`, no `sorryAx`, and
**every module silent at the 200 k edit loop**.

| order | module(s) | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `AlgebraicCurve/RegularProlongationGaussRepresentation.lean` (new) | **1,469** | **54 ok / 0 / 0** | 63 pin → 54 decls, **53 hash** + 1 dup | 54 clean | 1 (pin's `IsT.zero`↔`IsT.self`) | 0 / 0 | 40,000 / 20,000 (`exists_generators`) |
| B | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (new) | **1,093** | **24 ok / 0 / 0** | 54 → 24, **23 hash** (2 `main`s share a last name) | 24 clean | 1 (pin's headline↔engine) | 0 / 0 | 40,000 / 20,000 (`finrank_adjoin_algebraMap_eq`) |
| C | `AlgebraicCurve/Pic0/BaseChange.lean` (new) | **651** | **24 ok / 0 / 0** | 25 → 24, **24 hash** | 24 clean | 0 | 0 / 0 | 200,000 / 20,000 |
| C | `AlgebraicCurve/ConstantReductionCorrespondence.lean` (insert) | **689** (+64) | **14 ok / 0 / 0** (13 before) | 32 pin → 14, **14 hash** | 14 clean | 0 | 0 / 0 | — |
| D | `ModularCurve/StarBank/StarBank.lean` (new) | **475** | **10 ok / 0 / 0** (12 decls, 2 `private`) | 16 → 12, **12 hash** | 12 clean | 0 | 0 / 0 | 200,000 / 10,000 (`endgame_read`) |
| D | `ModularCurve/X1/IntegralityDifferential.lean` (insert, **re-homed**) | **698** (+271) | **18 ok / 0 / 0** (5 before) | 29 → 18, **17 hash + 1 name** (pre-existing) | 18 clean | 0 | 0 / 0 | 200,000 / 50,000 (the AF105E headline) |
| D | `ModularCurve/QExpansionDifferentialLift.lean` (restored) | **641** | **57 ok / 0 / 0** (58 → 57) | — | — | 0 | 0 / 0 | — |
| E | `ModularForms/QExpansionSlashCoeff.lean` (new) | **1,010** | **44 ok / 0 / 0** | 49 → 44, **44 hash** | 44 clean | 0 | 0 / 0 | 40,000 / 20,000 (the headline) |
| F | `NumberTheory/NumberField/MixedEmbedding.lean` (new) | **461** | **12 ok / 0 / 0** | 16 → 12, **12 hash** | 12 clean | 1 (pin's headline↔engine) | 0 / 0 | 100,000 / 80,000 (`weight_le`'s `Finset.univ` instance; **floor 1,000**) |
| F | `NumberTheory/NumberField/HeightOneSpectrumSummable.lean` (new) | **64** | **1 ok / 0 / 0** | 2 → 1, **1 hash** | 1 clean | 0 | 0 / 0 | 1,000 / — (**a substitution**, see below) |
| F | `NumberTheory/NumberField/UnitsLog.lean` (new) | **151** | **3 ok / 0 / 0** | 4 → 3, **3 hash** | 3 clean | 1 (pin's headline↔`_impl`) | 0 / 0 | 10,000 / 5,000 |
| F | `NumberTheory/NumberField/InfinitePlaceSign.lean` (new) | **145** | **5 ok / 0 / 0** | 6 → 5, **5 hash** | 5 clean | 1 (pin's `main`↔row) | 0 / 0 | 5,000 / 1,000 |
| F | `RingTheory/DedekindDomain/HeightOneSpectrumRat.lean` (new) | **62** | **1 ok / 0 / 0** | 2 → 1, **1 hash** | 1 clean | 0 | 0 / 0 | 1,000 / — |
| F | `Analysis/Measure/LpFinrank.lean` (new) | **200** | **5 ok / 0 / 0** | 6 → 5, **5 hash** | 5 clean | 0 | 0 / 0 | 40,000 / 20,000 (**floor 2,000 — the statements cost**) |
| G | `WeierstrassCurve/Velu/StepCurveSubgroup.lean` (insert, **migrated**) | **584** (+265) | **14 ok / 0 / 0** (1 before) | 30 → 14, **14 by name *and* hash** | 14 clean | 1 pre-existing (odd row's `[Finite H]` wrapper) | 0 / 0 | 5,000 / 1,000 (pre-existing helper) |
| G | `WeierstrassCurve/Velu/Reduction.lean` (new) | **296** | **5 ok / 0 / 0** | 11 → 10, **10 hash** | 5 clean | 0 | 0 / 0 | 10,000 / 5,000 |
| H | `FieldTheory/ValuationSubringValuedField.lean` (insert) | **1,089** (+35) | **30 ok / 0 / 0** (29 before) | 41 → 35, **34 hash + 1 name** | 30 clean | 0 | 0 / 0 | 20,000 / 15,000 (unchanged) |
| H | `FieldTheory/ValuationSubringResiduePolynomial.lean` (new) | **93** | **1 ok / 0 / 0** | 2 → 1, **1 hash** | 1 clean | 0 | 0 / 0 | 2,000 / 1,500 |
| H | `TateCurve/SeriesIdentities.lean` (insert) | **546** (+169) | **10 ok / 0 / 0** (7 before) | 33 → 28, **21 hash + 1 name** + 6 `solution`-labelled | 10 clean | 2 pre-existing (documented pair) | 0 / 0 | 2,000 / 1,500 (unchanged) |
| H | `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` (insert) | **1,107** (+100) | **3 ok / 0 / 0** (2 before) | 44 → 39, **36 hash** + 3 documented spelling rows | 3 clean | 0 | 0 / 0 | 50,000 / 45,000 (the sibling, never the new row) |
| ~~H~~ | ~~`ModularCurve/WeightOneIntegral.lean`~~ — **cut**, §5 | deleted | — | — | — | — | — | — |
| **set** | **19 modules on disk + 1 migration** | **11,524** (7,074 written) | **335 ok / 0 / 0 / 0 / 0** | | **335 clean, no `sorryAx`** | 9, all recorded and pin-internal | 0 / 0 | **no edit-loop gap**; three floors (MixedEmbedding 80–100 k, B 20 k, D 10 k) |

The set-level gates, run by me on the landed tree:

* **wave build** — `flock`ed `lake build` of all twenty modules: `Build completed successfully (5286
  jobs)`, **no warning line naming any of the twenty** (all 108 are in the cascade's other modules);
* **collision probe** — `lean/tmp/af107/collision-probe.lean` over all twenty: **silent, exit 0** (the
  FR-0274 gate; H ran it first, D's re-home then changed the module set, so this is the final run);
* **the §4 home audit, re-run on the landed tree** — every one of the **80** premise edges of the 26 rows
  is reachable from its row's landed home (`lean/tmp/af107/homes_audit.py`, which reads the row table
  `recon.json` and the landed-home table `homes.json` and prints `problems 0`); no other order had D's
  cycle;
* **cross-module `dedup`** over all twenty (`--cross --min-cost 8`, in three groups): **0 duplicate
  clusters, 0 removable lines**;
* **consumer zone** — `spec/SetAF107Consumer.lean`, three zones, exit 0: the `ℚ` case of order H's
  valed-field Krull-dimension bound (`ringKrullDim (⊤ : ValuationSubring ℚ) ≤ 1`); the two order-F rows
  **composed** (the spectrum's classification `v = span{p}` together with the `σ > 1` summability — the
  pair a `ℚ` Euler product consumes); and order D's star bank **instantiated** at `ZMod ℓ` with `p = 3`
  (the reduction situation, all three of its hypotheses exercised).

### 6.1 The one substitution that was already in the port, and the one row that was not ready

* **`NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` is a substitution, not a
  transcription.** The port already states it — `NumberField.TateGlobal.summable_absNorm_rpow_neg`
  (`NumberTheory/NumberField/TateGlobal/PlaceSum.lean:121`) — so order F imported it and the row is one
  line. `port_advise` was **blind** to it (name-anchored, FR-0314): all 21 of its "substitutions" on this
  order were the scaffold's own headlines. The row's home therefore sits *above* `TateGlobal` in the
  import order — a deliberate layering inversion, since the statement's subject is the height-one
  spectrum and the adelic module merely happens to state it first.
* **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` was not ready** (§5): the port's
  same-last-name declaration is the *`CuspForm`* statement, so the name tier credited a different theorem.
  The row was cut, its scaffold deleted, and the chain registered.

### 6.2 Plan vs actual

| figure | plan (§1, §3) | actual |
|---|---:|---:|
| rows / orders | 27 / 8 | **26 / 8** (one cut at its premise) |
| silo | 6,433 | **6,397** |
| written lines | net-new 5,391 predicted | **7,074** (+31 % over the net-new, **+11 % over the silo**) |
| modules | 20 scaffolded | **19 on disk + 1 migration** |
| checked declarations | not predicted | **221 new** (335 in the twenty modules) |
| recorded edit-loop gaps | 0 | **0** |

The +31 % over `port_plan`'s net-new is the same lesson SET-AF106 stated and this set confirms from the
other side: **price a port by its silo and its statement count**, because the net-new counts proof text
only, while a module also pays for every statement it declares (A's 54 declarations are 54 statements over
1,469 lines; B's 24 over 1,093). Against the *silo* the ratio is 1.11 — the closest to 1 of any set in the
column, which is what a set made of engines (rather than consumers) should look like.

### 6.3 The four house calls the orders brought me

1. **A legacy module was migrated rather than dodged** (order G, `Velu/StepCurveSubgroup.lean`): the ℓ = 2
   row's subject *is* that module, so it got its own wire, the `PORT_FILES` row was deleted, and the
   module now reads **14 ok** with the ℓ = 2 block promoted into a subject sub-namespace at the pin's leaf
   names (a duplicate `private` name in one file is the reason the sub-namespace exists).
2. **An insertion had to move up one module** (order D, the 227 row): its first premise *is*
   `X1/IntegralityDifferential.lean`, and `QEDL` is above it through four modules, so the ordered home was
   a cycle. Moved, and `QEDL` restored to its 57 rows with an empty `git diff`.
3. **A 532-line pin came out as a 24-declaration surface** (order C) and a **951-line pin as 44**
   (order E) — the two orders where the pin's `solution` row is a thin wrapper over a transcribed engine,
   so the `check_port` count is the engine's, not one.
4. **Three linter decisions, all declaration-scoped, none module-wide**: C's point-wise
   `linter.style.haveILetI` (the pin's `haveI` feed instance search, so `have` does not elaborate), E's
   `linter.unusedVariables` on three declarations (narrower than the pin's file scope; the `_`-prefix
   alternative measured at 41 hash / 3 name), and B's 23 `haveI`/`letI` rewritten as `have`/`let` — no
   linter silenced at all.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af107/unport20_landed.txt)) > build/shelf_af107_final.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` (20-name correction) | 292 / 161,122 | **266 / 154,725** |
| ready rows | 18 / 5,224 | **22 / 4,460** |
| leaves | 16 / 15,007 | **5 / 13,761** |
| withheld (FR-0044 guard) | 5 / 1,648 | 5 / 1,648 |

The delta is **−26 nodes / −6,397 lines**, *exactly* the cut (the 27th row stayed with its premise). The
correction list did **not** shrink: `--selfcheck` still reports the same 20 names, byte-identical to
SET-AF106's (`unport20_landed.txt` diffs empty against `unport20.txt`), because this set's rows are new
declarations rather than declarations that existed as false markers.

**Nineteen rows became ready (4,387 silo)** — the set's payoff, and every one of them is a consumer of a
landed row:

* order C's: `Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension` (**729**, the biggest new
  row) and `Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq` (44, B's sibling);
* order D's: `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j` (**544**),
  `exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm` (**329**);
* order F's: `NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le` (**214**),
  `exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound` (**202**),
  `NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet` (86),
  `MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict` (74, the Lp
  row's consumer), `AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace` (48),
  `StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace` (48),
  `mixedEmbedding.traceForm_mixedSpace_nondegenerate` (22);
* order G's: `TateCurve.pointX_normalForm` (198) and `pointY_normalForm` (199);
* order H's: `ValuationSubring.krullDimLE_one_of_isAlgebraic_rat` (12), and the two `RegularProlongation`
  rows `exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq` (**237**) and
  `forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed` (**206**) — A's payoff;
* four that are not this set's consumers but arrived with it: `EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization`
  (547), `AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le` (410),
  `ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi` (238) — the three this
  column's earlier sets left one premise short.

**The corrected read is a 21st name.** Order H found that `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`
reads ready only because the port's `CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` shares its last
name (FR-0047). With that shadow unported as well, the honest post-set figure is
**267 / 154,986** with **ready 22 / 4,685** — the 36-line consumer replaced by its 261-line missing premise.
Both figures are quoted because they are two marker sets, and the delta between two reads means one thing
only on the same set (the scoping recipe's rule).

## 8. What the set leaves behind

Twenty modules in one wave, and the column's widest cut: the ready block is now the definition layer's,
plus three rows held for their definitions and one false ready.

Five things carried beyond the files:

* **the shelf's structure changed shape, not just its size:** 15 of the 16 leaves became five (all five
  definition-gated), and the ready block's head is now three 500–730-line `AlgebraicCurve`/`ModularCurve`
  rows, i.e. the next set is a consumer set again, not a leaves set.
* **four new frictions, all about the instruments**: **FR-0316** (an unwired module cannot host a new row:
  the checker iterates the module's declarations, so the insertion is never diffed), **FR-0317** (nine
  leaves were deferred for four sets as "definition-gated" when their namespace is mathlib's — the gate is
  the `S_` file's `Definitions` imports, FR-0298's rule applied to the *statement's* vocabulary),
  **FR-0318** (a pin row whose hypotheses are all section variables hashes as its bare conclusion, so the
  advise "matches" any same-conclusion row), **FR-0319** (`rw [show a = f a by ring]` can rewrite inside its
  own right-hand side, and the `ring` inside the `show` falls to `ring_nf`, leaving an *info* line that
  breaks a silent-module gate).
* **a stale-olean trap for any headline that moves** (order D): after deleting a scaffold headline from its
  old module *source*, the new home still fails "already declared" until the **old module is rebuilt**,
  because the name is baked into its `.olean`. Cure: one `flock`ed `lake build` of the old module. Worth a
  friction of its own at the next refactor round.
* **four carry-forward items**: the `Γ₁` integral `q`-expansion chain (the cut row + 261-line premise +
  two more nodes), the `hasCanonicalDivisor_of_fg` promotion in the `IsCurveOver` hub, the
  `reduceHom_injOn` public/private pair, and the five `TDescent` base-change rows that order G transcribed
  rather than imported (move them down to a Weierstrass-level module and both copies become a deletion).
* **the consumer zones are thinner than the set**: A, B, C and E's headlines are 10–20 binder telescopes
  over the whole reduction/Fricke/place machinery, so a zone would restate the theorem — the same judgement
  SET-AF105/106 recorded. The honest form of the gate for those orders is the per-order engine diff, which
  is 221/221 new declarations by hash with 0 unaccounted.
