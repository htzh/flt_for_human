# SET-AF22 — the archimedean approximation's cheap gates

**Status: LANDED 2026-11-07** — three modules, six headlines, every gate green; §6 records the landing
and the re-read (exact: `needed` 805/338,347 → **799/337,955**, and **8 rows / 4,438 silo readied**, the
forecast's number to the silo). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF21 just landed. It is the **twenty-second** `AutomorphicForm`-serving set and the column's
**cheapest readiness event**: 6 rows / 392 silo / **201 net new math lines in 19 declaration groups**
that ready **4,438 silo** of blocked rows.

| order | rows | silo | to write | decls | home |
|---|---:|---:|---:|---:|---|
| **A** — the factorizable test functions, and the equivariant extension | 3 | 219 | 185 | 10 | new `Adelic/TestFnInvariance.lean` |
| **B** — smooth vectors and the compact level subgroup | 2 | 102 | 58 | 4 | new `Adelic/LevelCompactness.lean` |
| **C** — the character of an `LsXi` function | 1 | 71 | 62 | 3 | new `Adelic/LsXiCharacter.lean` |
| | **6** | **392** | **305** | **17** | |

## 0. The read, and why a 392-silo set

```bash
cd tools/deps && python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af22.json
python3 build/af-return.py build/shelf-af22.json AutomorphicForm. 1
```

SET-AF21 §9's re-read: `needed` **805 / 338,347**, frontier 1,611 / 789,029, ready 62 / 20,332,
leaves 218 / 55,693. `--selfcheck` PASS.

The recipe's §1 measures demand inversely to size on this shelf, and these six rows are its purest
form: every one is **premise-free** (a graph leaf) and every one is the single missing premise of a
blocked row of 100–1,200 silo. Return per row (measured): **1,445, 1,361, 1,131, 260, 133, 108**.

| row | silo | return | what it opens |
|---|---:|---:|---|
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | **1,445** | the archimedean approximation identity (1,175) + 190 + 80 |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | **1,361** | the `SmoothCuspRealizationAt` chain |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | **1,131** | `exists_rightConv_eq_of_archCutProjector` |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | **260** | the cusp-level subcarrier vanishing (+1,217 one hop) |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | **133** | `isFactorizableTestFn_comp_inv_mul` |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | **108** | `IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq` |

**It is a portfolio, not one story**, and the brief should say so: six independent lemmas, grouped
into three orders by the module their subject belongs to. The alternative — taking one of the rows
it *readies* (e.g. the 1,175 or the 1,131) — is a different set, three to ten times the work for the
same subject, and it is the next shelf read's business.

**Deferred by name**: `CuspidalSpectrum.exists_isLift_rightConv` (199 → 215, and 1,179 one edge
behind). It is the carrier-operator story (AF18/AF19's) rather than a gate, and it is the natural
first row of the set that takes `exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact`
(665) with it.

## 1. The price

`port_plan`: 392 raw / 321 declaration lines / 0 duplicate copies / 71 boilerplate / **120 already in
the port** → **201 net**. `af-worklist` per row: 63 / 42 / 80 / 32 / 26 / 62 lines to write.
No definition gate: the six wrappers' `Def_` closure is `IsotypicCuspSpace`, `CuspidalConstituent`,
`SmoothAutomorphicFnAt`, `AdelicDock_LocalEmbedding`, `FactorizableTestFn`, `AdelicLsXi`, and
`gate_scan` over all of them is **0 missing**. `twin_scan`: `new` six times before the scaffolding.

## 2. The rows and their homes

* **A** `Adelic/TestFnInvariance.lean` — `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn`
  (51, a left translate preserves `IsArchTestFactor`/`IsFinTestFactor`),
  `isFactorizableTestFn_sum_mul_comp_mul_mul` (98, a finite sum of double **row-isometry** translates
  is factorizable, via the `sandwich` of archimedean factors), and
  `exists_isRightEquivariant_comp_subtype_eq_of_injective` (70, the generic quotient/setoid
  extension lemma the other two are consumed with).
* **B** `Adelic/LevelCompactness.lean` — `IsKfSmooth.finite_smul_image_of_isCompact` (40, the generic
  `IsSmoothVector` statement specialised) and `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` (62,
  the compactness of the level-one subgroup inside the finite maximal compact, via
  `AdelicDock.finEmbed`).
* **C** `Adelic/LsXiCharacter.lean` — the character of a continuous non-vanishing `LsXi` function is
  trivial on the principal idèles and continuous. It is **not** inserted into
  `AutomorphicForm/Adelic/LsXi.lean` because that module is the pin `Def_` transcription with its own
  wire and its own section variables; the theorem goes in its own module above it.

## 3. Ground prep, and the gates

Headers, imports, wires and the six statements are in place, stated verbatim from their wrappers with
`sorry` bodies, and each module is checker-green at its statement surface: **3 ok** (A), **2 ok** (B),
**1 ok** (C).

Gates per order as in SET-AF14–AF21: `check_port --force` **0 mismatch / 0 missing** with the pin's
public helpers `ok` at their names; `#print axioms` on each headline
`[propext, Classical.choice, Quot.sound]`; the module's own `lake build` under `flock`/`timeout`,
silent, zero warnings; `dedup.py --within` and `move_dead.py --dry-run`; no
`sorry`/`set_option`/`import Mathlib`; a `spec/` consumer zone per order.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 805 / 338,347 | **799 / 337,955** |
| `needed [literal]` | 817 / 341,812 | **811 / 341,420** |
| frontier F | 1,611 / 789,029 | **1,617 / 789,421** |
| ready rows | 62 / 20,332 | **+7 rows / +4,438 silo** (the six readied, less the six taken) |
| `AutomorphicForm` demand | 314 / 138,052 | **308 / 137,660** |

The six rows are all `AutomorphicForm` (no namespace split this time), so the whole 392 leaves that
namespace's demand.

**Rows readied**: 1,445 (`isArchTestFactor_and_isArchFactorBiFinite_integral_prod_…`, 1,175, plus
190 and 80), 1,131 (`exists_rightConv_eq_of_archCutProjector`), 1,361 (the `SmoothCuspRealizationAt`
chain's `isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine`, 199, and its
successors), 260, 133, 108 — **4,438 silo**, and the ones behind them (`su2Derivs` 755 and the
`IsKfSmooth`/lift string) are one premise further.

## 5. What this set does not do

- **The rows it readies** (4,438 silo): that is the next shelf read's business.
- **`CuspidalSpectrum.exists_isLift_rightConv`** (199): deferred by name (§0).
- No definition layer, no promotion, no migration, no insertion into an existing module, no tree build.

## 6. The landing (2026-11-07)

| order | module | lines | decls | checker | build |
|---|---|---:|---:|---|---|
| A | `Adelic/TestFnInvariance.lean` (new) | 243 | 10 | **10 ok** / 0 / 0 | silent, 5.7 s |
| B | `Adelic/LevelCompactness.lean` (new) | 149 | 6 | **6 ok** / 0 / 0 | silent, 4.1 s |
| C | `Adelic/LsXiCharacter.lean` (new) | 105 | 3 | **3 ok** / 0 / 0 | silent, 4.3 s |
| | | **497** | **19 ok** | 0 mismatch / 0 missing | |

All six headlines on `[propext, Classical.choice, Quot.sound]` (`lean/tmp/ax_af22.lean`), no `sorryAx`;
`dedup --within` 0 clusters and `move_dead --dry-run` 0 dead on all three; three consumer zones
(`spec/AutomorphicFormSetAF22{A,B,C}Consumer.lean`) at **0 errors**.

**The re-read, exact.**

| figure | before (AF21) | after | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 805 / 338,347 | **799 / 337,955** | 799 / 337,955 ✓ |
| `needed [literal]` | 817 / 341,812 | **811 / 341,420** | 811 / 341,420 ✓ |
| frontier F | 1,611 / 789,029 | **1,617 / 789,421** | 1,617 / 789,421 ✓ |
| ready rows | 62 / 20,332 | **70 / 24,770** | +4,438 silo ✓ |
| leaves | 218 / 55,693 | **212 / 55,301** | — |
| `AutomorphicForm` demand | 314 / 138,052 | **308 / 137,660** | −392 ✓ |
| `--selfcheck` | PASS | **PASS** (1,440 sources / 1,621 names) | — |

**The eight rows readied are exactly the ones these gates were taken for**:
`isArchTestFactor_and_isArchFactorBiFinite_integral_prod_…` (1,175),
`exists_rightConv_eq_of_archCutProjector` (1,131),
`exists_forall_setLIntegral_nnnorm_sq_le_…_of_isCompact_of_coversModCentre` (1,361),
`apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective` (80),
`rightConv_mem_archCutSubmodule_of_isArchBiFinite` (190),
`CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_…` (260),
`IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq` (108),
`isFactorizableTestFn_comp_inv_mul` (133). They are **SET-AF23**.

**Two findings worth carrying.**

* **The checker's statement hash is syntactic in three ways a skeleton can get wrong**: an explicit
  binder's *name* (`_hle`, FR-0145 symptom 3), a section variable vs an inline binder (order B: three
  `MISMATCH` when `F` was inlined), and a *qualified* name inside a statement whose normaliser erases
  only some namespace prefixes (`AutomorphicForm.globalPoints`, order C) — so a helper's statement
  must keep the wrapper's spelling, qualifier included.
* **`open scoped Classical` is load-bearing** in `TestFnInvariance.lean` (the skeleton dropped the
  pin's `S_…comp_inv_mul…:6`): without it the `ContDiff ℝ ⊤ Φ` elaboration fails on
  `NormedAddCommGroup (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)`, because the `Fintype` of
  `{w // IsReal w}` comes only from `Classical.propDecidable`.
