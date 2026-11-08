# SET-AF23 — the archimedean cut projector and the archimedean approximation

**Status: LANDED 2026-11-07** — one module, four headlines, every gate green; §6 records the landing
and the re-read (exact on every figure except the ready-block row count, which came out better than
forecast: **6 rows readied, not 1**).
Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF22 left. It is the **twenty-third** `AutomorphicForm`-serving set, and it takes the two rows
that AF22's gate leaves were readied *for*: the archimedean approximation identity and the cut
projector's right-convolution identity.

**4 rows / 2,576 silo / 1,342 net new math lines (`port_plan`) / 157 declaration groups, of which
1,148 lines are already in the port** — the column's most composition-heavy set so far.

| row (`AutomorphicForm.` dropped) | silo | prem | lev | return | what it says |
|---|---:|---:|---:|---:|---|
| `apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective` | 80 | 1 | 1/1 | — | a right-equivariant map preserves a supremum of type submodules |
| `rightConv_mem_archCutSubmodule_of_isArchBiFinite` | 190 | 2 | 1/1 | — | convolving by an arch-bi-finite factorizable test function keeps a vector in the archimedean cut |
| `isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule` | 1,175 | 1 | 5/6 | 412 | the row-isometry-product integral of a test factor against a type-decomposed factor is a bi-finite test factor |
| `exists_rightConv_eq_of_archCutProjector` | 1,131 | 9 | 1/1 | — | the cut projector sends `rightConv y f` to `rightConv y f'` with `f'` factorizable and bi-finite |

## 0. The read

```bash
cd tools/deps && python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af23.json
python3 build/af-return.py build/shelf-af23.json AutomorphicForm. 400
```

SET-AF22's post-landing read: `needed` **799 / 337,955**, frontier 1,617 / 789,421, ready **70 /
24,770** (42 of them `AutomorphicForm` / 18,631), leaves 212 / ~54,000. `--selfcheck` PASS.

**Why these four.** They are the head of AF22's return: `exists_isRightEquivariant_comp_subtype_eq_of_injective`
(70) was taken *because* it readies the 1,175 (with 80 and 190), and
`isFactorizableTestFn_sum_mul_comp_mul_mul` (98) *because* it readies the 1,131. A gate set that
takes the gate and not the row it opens leaves the column in the same place next read — SET-10's
point, inverted. The four are ready with **zero unported premises** and they are one subject: the
archimedean type decomposition and the projector built on it.

## 1. The price

`port_plan`: 2,576 raw / 2,493 declaration lines / 3 duplicate copies / 83 boilerplate / **1,148
already in the port** → **1,342 net**; 91 trusted substitutions. The substitutions are the port's
own archimedean machinery — `ArchCutProjector`'s `TypeWitness`/`cutc`/`typeComponents`/`Qc`,
`ArchType`'s `archCutSubmodule`/`typeSubmodule`, and AF22's `TestFnInvariance` — which is why the
figure is in the recipe's band despite 2,576 silo.

No definition gate: the four wrappers' `Def_` closure is `IsotypicCuspSpace`,
`CuspidalConstituent`, `FactorizableTestFn`, `ArchCutSubmodule`… and `gate_scan` is 0 missing.
`twin_scan`: `new` four times before the scaffolding.

## 2. Home

**One new module, `AutomorphicForm/Adelic/ArchApproximation.lean`**, above
`Adelic/ArchCutProjector.lean` (825 lines, 4 in-tree importers) and importing AF22's
`Adelic/TestFnInvariance.lean`. The projector module is the *engine*; this is its consumer, and
inserting 1,342 lines into it would double it and re-elaborate four dependents.

## 3. The cut, and the gates

One order (`lean/tmp/WORKORDER-AF23-arch-approximation.md`), one file, four headlines, written in the
order 80 → 190 → 1,175 → 1,131. The four statements are frozen in the skeleton and checker-green at
**4 ok / 0 mismatch / 0 missing**; gates as in SET-AF14–AF22 (§6 of the recipe), plus a consumer zone
`spec/AutomorphicFormSetAF23Consumer.lean`.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 799 / 337,955 | **795 / 335,379** |
| `needed [literal]` | 811 / 341,420 | **807 / 338,844** |
| frontier F | 1,617 / 789,421 | **1,621 / 791,997** |
| ready rows | 70 / 24,770 | **66 / 23,276** (4 out, 1 in: the 412) |
| `AutomorphicForm` demand | 314 / 138,052 − … | **310 / 135,476** |

**What it readies**: `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` (333)
and the 412 behind the 1,175 are already on the shelf; the real payoff is that **the archimedean cut
projector becomes usable** — it is the machine the `CuspidalConstituent`/isotypic block
(`exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` 646,
`isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` 242, `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` 214)
is written against.

## 5. What this set does not do

- **`su2Derivs_stable_and_hasDerivAt_…`** (755, return 1,077): the `su(2)`/circle-weight string, the
  largest single leaf left on the shelf — a different subject (archimedean Casimir eigenfunctions) and
  the natural AF24.
- **`CuspidalSpectrum.exists_isLift_rightConv`** (199, return 880 + 514 one hop): the carrier-operator
  story, deferred from AF22 by name.
- **The LsXi bound pair** (`exists_forall_setLIntegral_nnnorm_sq_le_…_of_isCompact_of_coversModCentre`
  1,361 and its 447 sibling): the Petersson bound, a third subject.

## 6. The landing (2026-11-07)

`AutomorphicForm/Adelic/ArchApproximation.lean` 137 → **1,229 lines, 49 declarations**; one
consumer `spec/AutomorphicFormSetAF23Consumer.lean`.

| gate | result |
|---|---|
| `check_port --force` | **7 ok / 0 mismatch / 0 missing / 0 own** (4 headlines + the pin's three `TypePush` helpers) |
| build (single module, flock) | silent, 3 s warm / 36 s cold; zero warnings |
| axioms | all four on `[propext, Classical.choice, Quot.sound]` (`lean/tmp/ax_af23.lean`) |
| `dedup --within` | 49 declarations, **0 clusters** |
| `move_dead --dry-run` | 1 declaration / 6 lines — `LamData_toEcf_coe`, **dead in the pin too**, kept for pin parity |
| consumer | **0 errors, 0 warnings** |

**The re-read.**

| figure | before (AF22) | after | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 799 / 337,955 | **795 / 335,379** | 795 / 335,379 ✓ |
| `needed [literal]` | 811 / 341,420 | **807 / 338,844** | 807 / 338,844 ✓ |
| frontier F | 1,617 / 789,421 | **1,621 / 791,997** | 1,621 / 791,997 ✓ |
| ready rows | 70 / 24,770 | **72 / 24,200** | 66 / 23,276 ✗ (better) |
| leaves | 212 / 55,301 | 212 / 55,301 | — ✓ |
| `AutomorphicForm` demand | 308 / 137,660 | **304 / 135,084** | — ✓ (−2,576) |
| `--selfcheck` | PASS | **PASS** (1,440 sources / 1,621 names) | — |

The ready block moved **−4 rows / −2,576 silo and +6 rows / +2,006 silo**: the four taken rows left
and six of their successors entered, so the forecast's "1 in" was a per-row estimate that the
multi-premise effect (FR-0106) overtook. The lesson is the column's oldest: a per-row `return` column
undercounts what a *set* readies, because two of its rows can jointly be the last two premises of a
third.

**Where the 2,576 silo went.** Only ~1,090 lines were genuinely new: row 3's 1,175 pin lines were
~90 % already ported (`RepTheory/ConvolutionLimit.lean`'s `dconvWith` + parametric-integral engine,
`ArchApproxIdentity/ArchInfra.lean`'s `Kprod`/`inclArch`/topology instances, `TestFnTop`,
AF22's `sandwich`/`archEntries_mul_mul`), and row 4 reused `ArchCompactOrbit`, `ArchCutProjector`,
`ArchDualCut`, `ArchCutSpan`, `RightConvRegularity` and `IsotypicCuspSpace`. This is the composition
payoff the scoping priced at 1,148 "already in the port" declaration lines — it landed on the nose.

**Deviations worth carrying.** The `TypePush` helpers are homed in the pin's own namespace
(`AutomorphicForm.TypePush`) because `AutomorphicForm.CuspidalConstituent.rightRegular` already exists;
`dconvWith`'s compact-support lemma was **generalised** from `e e` to `e₁ e₂` (31 lines at
`ConvolutionLimit.lean`'s site rather than a restatement); three pin lemmas that are only *used*
(`rowIsometryInclAt₀_injective`, `le_iSup_archTypeSubmoduleAt_of_surjective'`, `orbitSpan_le_Ecf`) were
not restated because the port proves them elsewhere; and `open scoped Classical` is again load-bearing
(the `{w // IsComplex w}` `Fintype`).

**Row 3 is two arguments, not one**: the `IsArchTestFactor` half is parametric-integration analysis
(differentiate under the integral, bounds from `Kprod`'s compactness, support from
`tsupport h`), while the `IsArchFactorBiFinite` half never sees differentiability — it is two
applications of row 1's type-push lemma to the linear maps `u ↦ dconvWith μ a (u ·⁻¹) e₂ h` and
`u ↦ dconvWith μ a e₁ u h`, intertwined by `dconvWith_rt_left`/`_rt_right`. That split is exactly why
the port reuse divided cleanly between the DUI engine and the type layer.
