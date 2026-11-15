# SET-AF75 — the adelic Fourier transform on the Schwartz–Bruhat space

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF73/AF74 with the
recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The
seventy-fifth set of the column, and the first that **cuts a subject rather than a row**: the twelve
ready leaves of one namespace, `NumberField.AdelicFourier`, whose definition layer
(`NumberTheory/AdelicFourier.lean`) has been in the port since the `Def_` waves.

**12 rows / 1,947 silo / ≈1,253 net** in **five new modules**, four orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A1** | `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | new `NumberTheory/AdelicFourier/Space` |
| **A2** | `NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet` | 84 | 1/1 | same |
| **A3** | `NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat` | 101 | 1/7 | same |
| **A4** | `NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat` | 235 | 5/20 | same |
| **A5** | `NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat` | 236 | 2/3 | same |
| **B1** | `NumberField.AdelicFourier.fourierIntegral_pureTensor_eq` | 359 | 4/8 | new `NumberTheory/AdelicFourier/Transform` |
| **B2** | `NumberField.AdelicFourier.fourierIntegral_comp_mul_left` | 215 | 3/10 | same |
| **C1** | `NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact` | 93 | 1/1 | new `NumberTheory/AdelicFourier/FiniteCoset` |
| **C2** | `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing` | 140 | 1/2 | same |
| **C3** | `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` | 181 | 1/1 | same |
| **D1** | `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` | 93 | 25/74 | new `NumberTheory/NumberField/GlobalAddChar/Circle` |
| **D2** | `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | new `NumberTheory/AdelicHaar/Uniqueness` |

The set is one subject with four parts: **the space** of test functions (`Space`), **the transform** of
a pure tensor and its scaling law (`Transform`), **character orthogonality and the principal coset**
(`FiniteCoset`) and **the two ambient facts** the transform quantifies over — a global character has
values on the unit circle, and the additive Haar measure of `𝔸_F` is unique up to a scalar (`Circle`,
`Uniqueness`).

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_next.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **608 / 268,958** |
| ready rows, all namespaces | **22 / 4,790** |
| leaves, all namespaces | **155 / 39,255** |
| `NumberField` demand | **91 / 32,599** |
| withheld by the FR-0044 guard | 4 / 831 |

`needed` is exactly SET-AF73/AF74 §5's post-landing figure, so this set opens on their re-read; the
read was **taken before any scaffold was written** (FR-0201). `--selfcheck` still FAILS on the fifteen
`ModularCurve.PhiGen`/`ModularPolynomialData` markers (MD-005); no row cut here cites any of them, and
the read is quoted *uncorrected* (the marker set is SET-AF73's).

## 1. What the set says

- **A** — the Schwartz–Bruhat space `schwartzBruhat F` is closed under additive translation
  (`comp_add_right_mem_pureTensorSet`), under multiplication by a rational scalar
  (`comp_mul_algebraMap_mem_pureTensorSet`) and under multiplication by *any* unit idèle
  (`comp_mul_mem_schwartzBruhat`, routed through `pureTensorSet` and the spanning induction
  `schwartzBruhat_induction`); every member is integrable for an additive Haar measure
  (`integrable_of_mem_schwartzBruhat`) by the cell decomposition `mixedCell`/`archCell`/`cell K l` of
  the adèles, and its diagonal translates are summable (`summable_translate_of_mem_schwartzBruhat`)
  with the same majorant `(1 + ‖y‖)^k * ‖g y‖ ≤ C` summed over `mixedEmbedding.integerLattice F`.
- **B** — the Fourier transform of a pure tensor factors (`fourierIntegral_pureTensor_eq`): the
  archimedean transform of `g` times the finite transform of `h` with the constant
  `μ (adelicBox F) / (covolume * ν (integralFiniteAdeles))`, carried by the product split
  `split : 𝔸_F ≃ₜ+ mixedSpace F × 𝔸_F^fin` of the fundamental domain. The change of variable under a
  unit idèle (`fourierIntegral_comp_mul_left`) scales the transform by `(distribHaarChar a)⁻¹` and
  moves `w` to `a⁻¹ w`.
- **C** — orthogonality of an additive character over a compact subgroup `K ≤ 𝔸_F^fin`
  (`setIntegral_addChar_mul_eq_ite_of_isCompact`) — the integral is `ν K` or `0` — and the Fourier
  transform of the indicator of a principal coset `k + d • 𝓞̂` (`…principalCoset_finiteAdeleRing` at a
  principal point, `…_apply` at an arbitrary point): the phase `ψ (-(k * w))` times `ν (coset)` times
  the triviality indicator on `d • 𝓞̂`.
- **D** — a global additive character is bounded (the box is a compact fundamental domain) hence takes
  values on the unit circle (`norm_apply_eq_one_of_isGlobalAddChar`), so it factors through `Circle`
  (`toCircleAddChar`, `exists_compAddChar_eq_of_isGlobalAddChar`); and two additive Haar measures on
  `𝔸_F` differ by a positive scalar (`exists_smul_eq_of_isAddHaarMeasure_adeleRing`), the content being
  that `𝔸_F` is second countable — which `NumberTheory/AdelicLevel/Countability.lean` already supplies.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 22 rows / 4,790 silo — none cut, all deferred** (unchanged from SET-AF71 §1.1).

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred (blocked: needs `AutomorphicForm/Adelic/WeilIntertwining`) |
| `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` | 697 | 1/1 | deferred (blocked: `IsCharTwoJNeZeroNF` not ported) |
| `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` | 599 | 1/4 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1/7 | deferred |
| `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1/1 | deferred |
| `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1/1 | deferred |
| `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` | 138 | 1/1 | deferred |
| `LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen` | 128 | 2/2 | deferred |
| `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 1/2 | deferred |
| `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | 1/16 | deferred |
| `AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup` | 104 | 1/15 | deferred |
| `LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp` | 100 | 1/13 | deferred |
| `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing` | 84 | 4/5 | deferred |
| `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1/3 | deferred |
| `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` | 59 | 2/5 | deferred |
| `AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf` | 56 | 3/5 | deferred |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 1/3 | deferred |
| `ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` | 34 | 1/1 | deferred |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

**The leaves block: 155 rows / 39,255 silo — 12 cut (A–D), 143 deferred.** Its top (the ten largest
deferred rows plus the eleven cut ones in place):

| row | silo | lev | cut |
|---|---:|---:|---|
| `M4aTorus.completedRayL_fe` | 12126 | 1/2 | deferred (its `Def_` layer is not ported) |
| `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` | 684 | 1/2 | deferred |
| `EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing` | 666 | 1/1 | deferred |
| `AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred |
| `NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one` | 600 | 11/40 | deferred |
| `LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` | 589 | 1/1 | deferred |
| `AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred |
| `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred |
| `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 1/33 | deferred |
| `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 2/2 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_pureTensor_eq` | 359 | 4/8 | **cut B1** |
| `NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat` | 236 | 2/3 | **cut A5** |
| `NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat` | 235 | 5/20 | **cut A4** |
| `NumberField.AdelicFourier.fourierIntegral_comp_mul_left` | 215 | 3/10 | **cut B2** |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` | 181 | 1/1 | **cut C3** |
| `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | **cut D2** |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing` | 140 | 1/2 | **cut C2** |
| `NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat` | 101 | 1/7 | **cut A3** |
| `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` | 93 | 25/74 | **cut D1** |
| `NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact` | 93 | 1/1 | **cut C1** |
| `NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet` | 84 | 1/1 | **cut A2** |
| `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | **cut A1** |

The remaining 143 rows are deferred unchanged from SET-AF70 §1.1, as in SET-AF73 §1.1.

**The `NumberField.AdelicFourier` namespace is now cut whole.** Its twelve leaf rows are exactly the
twelve above; the namespace's remaining demand is inside the `AutomorphicForm` rows that *consume*
them, so no row of this namespace is left on the shelf.

## 2. The price and the home

```bash
python3 port_advise.py --nodes <the 12> --with-defs --json build/af75_af_advise.json
python3 port_plan.py --json build/af75_af_advise.json
```

| figure | value |
|---|---:|
| raw `S_` lines | 1,947 |
| declaration lines | 1,578 |
| duplicate copies (port once) | 219 |
| **net new math lines** | **1,253** |
| already in the port | 92 declarations / ≈984 lines |
| shared preludes (port once) | 4 names / ≈102 lines |

The 92 substitutions are almost all in the `Definitions/` files of the slice — `Def_NumberField_AdelicBox`
(36), `Def_NumberField_AdelicHaar` (25), `Def_NumberField_AdelicFourier` (15),
`Def_AutomorphicForm_WhittakerCoefficient` (8) — i.e. **the whole definition layer of this set is
already ported**, and the port's `NumberTheory/AdelicLevel/Countability.lean` covers the countability
prelude the pin repeats in eight of the twelve `S_` files (2× 35-line theorem, 8× 5-line theorem, plus
the countability instances). The four "port once" names are
`secondCountableTopology_restrictedProduct` (8 copies), `isCountablyGenerated_uniformity_of_valued`
(8), `exists_one_add_norm_pow_mul_norm_le` (2) and `mulLeftHomeomorph` (2, and `mulLeftLinearEquiv` /
`mulLeftCLE` next to it); all are homed once in `Space`/`Transform`.

**No `Def_` work and no promotions.** The one home that needed a decision is
`AdelicBox.integralFiniteAdeles`: the pin spells it `AdelicBox.integralFiniteAdeles`, the port homes it
in `NumberField.AdelicLevel` and re-exports it in `NumberTheory/AdelicHaar/PlaceMeasure.lean` as a
port-only `@[reducible] def` (the note is in that module) — the new modules import that re-export, so
the pin's spelling transcribes verbatim.

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `NumberTheory/AdelicFourier/Space.lean` (new) | A1–A5 | **228** lines | 24 | **32 ok / 0 / 0** |
| `NumberTheory/AdelicFourier/Transform.lean` (new) | B1–B2 | **131** | 9 | **11 ok / 0 / 0** |
| `NumberTheory/AdelicFourier/FiniteCoset.lean` (new) | C1–C3 | **145** | 10 | **10 ok / 0 / 0** |
| `NumberTheory/NumberField/GlobalAddChar/Circle.lean` (new) | D1 | **75** | 5 | **6 ok / 0 / 0** |
| `NumberTheory/AdelicHaar/Uniqueness.lean` (new) | D2 | **38** | 1 | **1 ok / 0 / 0** |

All five elaborate silently at the edit-loop cap and build in 3.4–6.5 s. The label namespaces of the
pin's `S_` files (`Ws25`, `Ws25Supply`, `Ws25DIL`, `Ws25OrthK`, `Ws25Fcoset`, `D2cPrime`, `R8Supply`,
`HHaarSupply`) are rectified away; the `_impl` glue of each file is folded into the headline at the
graph node's name, and the pin's `solution` copies are not ported (their statements are the wrappers').

## 3. The orders and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF75A` | A1–A5 | `NumberTheory/AdelicFourier/Space.lean` | ≈430 | 24 |
| `WORKORDER-AF75B` | B1–B2 | `NumberTheory/AdelicFourier/Transform.lean` | ≈340 | 9 |
| `WORKORDER-AF75C` | C1–C3 | `NumberTheory/AdelicFourier/FiniteCoset.lean` | ≈260 | 10 |
| `WORKORDER-AF75D` | D1–D2 | `Circle.lean` + `Uniqueness.lean` | ≈120 | 6 |

The four orders touch **disjoint files** (five new modules, no hub edits), so all four run
concurrently; only the build lock is shared. Gates, per order:

1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` with `grep -E "error|warning"`
   **empty**;
2. `flock .lake/flt_build.lock timeout 110 lake build <Module>` — success, silent, no tree build;
3. `spec/check_port.py --force <module>` — the counts above, 0 mismatch, 0 missing;
4. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`;
5. `dedup.py --within --module <stem> --min-cost 0` (clusters reviewed, not silenced) and
   `move_dead.py --source <file> --target /dev/null --dry-run` (0 declarations);
6. a `spec/` consumer zone with a real cross-module composition (no `#check`s), 0 errors, 0 warnings.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (608 / 268,958).* The forecast is **measured,
not estimated**: the same read with the twelve rows passed in as `--port` (the recipe's §0 dual of
`--unport`) gives

| figure | §0 | **forecast (12 `--port`ed)** |
|---|---:|---:|
| `needed [F terminal]` | 608 / 268,958 | **596 / 267,011** |
| ready rows | 22 / 4,790 | **26 / 5,719** |
| leaves | 155 / 39,255 | **143 / 37,308** |

and the four rows the set **readies** are

| row | silo | lev |
|---|---:|---:|
| `EisensteinGeneral.Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection` | 275 | 2/4 |
| `NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq` | 241 | 2/6 |
| `AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq` | 214 | 2/6 |
| `EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable` | 199 | 6/12 |

This is the column's first positive readiness return in six sets, and it is the expected shape: the
twelve leaves were *not* pure leaves — `integrable_of_mem_schwartzBruhat` (20 pin importers),
`fourierIntegral_comp_mul_left` (10), `fourierIntegral_pureTensor_eq` (8) and
`norm_apply_eq_one_of_isGlobalAddChar` (74) are the last missing premise of four rows one step up.
The withheld block is unchanged (4 nodes / 831 silo: the three `abelJacobiCard`/`pathPeriodLattice`
rows and the `Pic0` torsion finiteness).

## 5. The landing

All twelve rows in, **49 `sorry`s → 0**, five new modules, no hub edited.

| file | rows | lines | `sorry` | checker | axioms |
|---|---|---:|---:|---|---|
| `NumberTheory/AdelicFourier/Space.lean` | A1–A5 | 228 → **567** | 24 → 0 | **33 ok / 0 / 0** | 5/5 clean |
| `NumberTheory/AdelicFourier/Transform.lean` | B1–B2 | 131 → **250** | 9 → 0 | **11 ok / 0 / 0** | 2/2 clean |
| `NumberTheory/AdelicFourier/FiniteCoset.lean` | C1–C3 | 145 → **393** | 10 → 0 | **10 ok / 0 / 0** | 3/3 clean |
| `NumberTheory/NumberField/GlobalAddChar/Circle.lean` | D1 | 75 → **94** | 5 → 0 | **6 ok / 0 / 0** | clean |
| `NumberTheory/AdelicHaar/Uniqueness.lean` | D2 | 38 → **42** | 1 → 0 | **1 ok / 0 / 0** | clean |

1,346 lines written; the five headers/imports are ≈150 of them, so the declaration-and-proof content is
≈1,196 against the 1,253 net-new estimate — **0.95×, the tightest accounting the column has had** (the
previous sets ran 0.54–0.6×, where the pin's own prelude was already in the port). `dedup --within`:
0 clusters / 0 removable lines in every module. `move_dead --dry-run`: 0 declarations, 0 lines. Consumer
zones `spec/NumberTheorySetAF75{A,B,C,D}Consumer.lean` (177 / 111 / 69 / 107 lines): **0 errors,
0 warnings** each. Imports added: 2 + 1 + 0 + 0 (`ZLattice.Summable`, `Integral.Bochner.Set`,
`Group.OpenMapping`) — each the pin's own import made explicit where the pin had `import Mathlib`.

**Heartbeat floors** (probed downward, no `set_option`): `Space` ≈25.5 k (the `integrable_pureTensor`
cell engine), `Transform` 20 k, `FiniteCoset` 12 k, `Circle` 1 k, `Uniqueness` 400 — all ≤13 % of the
200 k cap. The module-level cap is untouched everywhere.

### The scaffolding omission, caught and repaired

The manager's scaffold assembler kept only the `pureTensorSet`-level closure of row **A3** and dropped
its headline: `comp_mul_mem_schwartzBruhat` (pin `:76-87`) was cut by the brief and absent from the
module, so the checker read 32 ok and the row was silently unported. The AF75A worker flagged it instead
of adding the declaration (its order forbade new public declarations, correctly). The manager restored it
with the pin's own proof; the checker then read **33 ok**, and the restored declaration **exceeded the
200 k edit-loop cap** at its `refine` line although the pin's proof is ten lines. The pin file itself
carries `set_option maxHeartbeats 1600000`, so the defect predates the port: a delayed `Coe` metavariable
for `↑y` inside the *spelled* induction motive, whose assignment unfolds the adele-ring/completion type
chain. Diagnosed by a build-fix agent under `porting-playbook.md` §3.5 (floor probe → `one:<line>` →
shrink → tiny-cap `isDefEq` trace) and fixed **in the proof only**, by ascribing the coercion
(`(↑y : AdeleRing (𝓞 F) F) * x`) with a comment saying the ascription is load-bearing. Recorded as
**FR-0217**.

Two smaller things worth carrying: the pin's `variable {F}` re-declaration mid-file is a *binder
annotation* change (`mixedCell F` before it, `cell0 K` after it), and a scaffold that copies the pin's
statement text must reproduce it or the statements stop elaborating — the same shape recurs in SET-AF76
order C. And the pin's `AdelicBox.integralFiniteAdeles` spelling is the port's port-only re-export in
`NumberTheory/AdelicHaar/PlaceMeasure.lean`; both are how the pin's text transcribes verbatim.

### The set's numbers, and the plan-vs-actual

| figure | before (§0) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 608 / 268,958 | **596 / 267,011** | −12 / −1,947 ✓ exact |
| ready rows | 22 / 4,790 | **26 / 5,719** | +4 / +929 ✓ exact |
| leaves | 155 / 39,255 | **143 / 37,308** | −12 / −1,947 ✓ exact |

The readiness forecast held to the row and the line: the four rows named in §4 before dispatch are
exactly the four in the post-landing read, which is the first positive return in six sets and the reason
SET-AF76 is cut from them.
