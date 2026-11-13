# SET-AF51 — the Euler product of the Dedekind zeta, and the regularized zeta

**Status: LANDED (2026-11-12)** — §0 the read, §1 the cut and the price, §2 the homes and the manager's
landed layer, §3 the order, §4 the forecast, §5 what the set does not do, **§6 the landing record**. Read off the same eleven-marker
corrected shelf as SET-AF50.

**2 rows / 685 silo / ≈630 net** in **44 declaration groups** and 306 written scaffold lines: the Euler
product of the Dedekind zeta function and the regularized zeta's zeros. The column's first
`NumberField.CompletedDedekindZeta` set since that package landed, and the first whose proofs are (near)
applications of a single ported headline.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul` | 580 | 1/2 | the Euler product converges and is differentiable for `re s > 1`, equals the Dedekind zeta there, and tends to the pole term at `1` |
| **B1** | `NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero` | 105 | 6/18 | the regularized zeta is entire, nonvanishing at `1`, equals `(s-1)·ζ` on `re s > 1`, and vanishes at every `-2(n+1)` |

## 0. The read

Same command and correction as SET-AF50 §0: `needed` **703 / 294,693**, ready 50 / 10,473, leaves
185 / 46,068, `NumberField` demand unchanged at 99 / 34,198. Both rows' only premise is
`NumberField.exists_completedDedekindZeta_package` (7,554 pin lines, ported as the
`NumberTheory/NumberField/CompletedDedekindZeta/` directory) — **the definition gate is empty**
(`wrapper defs: none`) and the premise audit is closed.

## 1. The cut, and the price

One story: the zeta function's Euler product and its regularized form. A1 is a real development (43
declarations: the ideal-count series, its summation by parts, the primes/spectrum index, the Euler product,
and the archimedean normalisation `Dinv`); B1 is a **105-line, one-declaration application** of the ported
completed-zeta package with **18 in-graph consumers** — the column's cheapest high-leverage row in a long
time.

| figure | AF51 |
|---|---:|
| raw `S_` lines | 685 |
| declaration lines | 657 |
| distinct declaration groups | 44 |
| boilerplate dropped | 28 |
| **net new math lines** | **≈630** |

Same instrument caveat as SET-AF50 §1 (FR-0184: the scaffold is in the tree, so a post-scaffold
`port_plan` reads "net 8").

## 2. The homes, and the manager's landed layer

| module | row | namespace | imports |
|---|---|---|---|
| `NumberTheory/NumberField/CompletedDedekindZeta/EulerProduct.lean` | A1 | `EulerProduct.EulerZeta` and `EulerProduct.ArchimedeanNormalization` (pin labels `Ws41.EulerZeta`, `Ws41.N1bProof`) | `NumberTheory.NumberField.CompletedDedekindZeta` + mathlib's Dedekind zeta/LSeries/Gamma |
| `NumberTheory/NumberField/CompletedDedekindZeta/RegularizedZeta.lean` | B1 | root (`NumberField.<name>` at the wrapper's name) | the same |

**The manager's layer is landed and measured**:

| module | lines | decls | `sorry` | `check_port --force` |
|---|---:|---:|---:|---|
| `EulerProduct.lean` | 252 | 43 | 38 | **43 ok / 0 / 0** |
| `RegularizedZeta.lean` | 54 | 1 | 1 | **1 ok / 0 / 0** |

All **44 statements** verified before a proof; the pin's machine label `Ws41` rectified to `EulerProduct`
and `N1bProof` to `ArchimedeanNormalization`; the nine data definitions (`idealCount`, the **scoped**
`finite_fiber` instance, `Primes`/`primeSet`, `primesEquiv`, `Dinv`) transcribed and building, with one
v4.34 deprecation applied at generation time (`Ideal.finite_setOf_absNorm_eq` → `…setOfPred_absNorm_eq`).

## 3. The order, and the gates

One dispatch, two modules: `tmp/af51/WORKORDER-AF51A-euler-product-and-regularized-zeta.md`. The gates are
the recipe's §6 per module (silent at 200,000 heartbeats, `sorry`-free, own `lake build` under
`flock`/`timeout`, the checker at §2's counts, `#print axioms`, `dedup`/`move_dead`, one consumer zone).

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 703 / 294,693 (→ 701 / 293,390 after AF50) | **699 / 292,705** |
| frontier F | see AF50 §4 | **+685 over AF50's** |
| ready rows | 50 / 10,473 | read at the landing |
| `NumberField` demand | 99 / 34,198 | **97 / 33,513** |

B1's eighteen consumers are the return to watch: several are `AutomorphicForm` continuation rows of 300–1,200
silo, and one is `tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family` (1,062). The
re-read prices how many of them become ready; none is forecast here.

## 5. What this set does not do

As SET-AF50 §5, with AF51's two rows removed. Not taken: the `EisensteinGeneral.Piece` factorization (890,
six `Def_` modules), the `AutomorphicForm` `tsum`-average row (635, lev 1/1), the `GaloisRep` semisimplicity
row (495), the `ModularCurve` diamond row (485), and the Kummer root-lifting family (two sets away, per
SET-AF50 §5). `M4aTorus.completedRayL_fe` (12,126 silo) stays the queued big effort.

## 6. The landing (2026-11-12)

One order, two modules, **zero `sorry`**, no statement moved (the checker counts are the scaffold's):

| module | lines | decls | `sorry` → | `check_port` | build | axioms | consumer |
|---|---|---:|---|---|---:|---|---:|
| `EulerProduct.lean` | 252 → **609** | 43 | 38 → 0 | **43 ok / 0 / 0** | 4,049 jobs, 11 s | clean | 73 lines, 0 err |
| `RegularizedZeta.lean` | 54 → **143** | 1 | 1 → 0 | **1 ok / 0 / 0** | 4,047 jobs, 4.7 s | clean | in the same zone |
| | **306 → 752** | **44** | **39 → 0** | **44 ok, 0 mismatch, 0 missing** | | **2/2** | **73 lines, 0 err** |

Both modules are silent at 200,000 heartbeats with zero warnings and carry no `set_option`; each builds
alone under `flock`/`timeout` (no tree build, no dependents). `dedup` reports one intra-module *shape*
cluster and 0 removable lines — the pin's own wrapper pair (`exists_continuation` :515 vs the headline
:573), both frozen and kept; `move_dead` reports 0 declarations, and the worker calibrated it against three
other modules of the same family (which also report 0) so that the reading is known to be a tool-state
limitation rather than a dead-code verdict.

### 6.1 What the order found

1. **Heartbeat margin measured**: `EulerProduct` passes at 100,000 and 140,000 and fails at 80,000, with the
   single hotspot `hasProd_spectrum` (the `(primesEquiv K).hasProd_iff` defeq check) — ≈2× headroom under
   the gate. `RegularizedZeta` passes even at 20,000 (≥10× headroom).
2. **One typeclass-incompatible `Finset` lemma** (now a drift row): v4.34's `Finset.prod_le_prod` requires
   `[MulLeftMono ℝ]`, which is false, so the pin's call had to move to `Finset.prod_le_prod₀`. That is a
   *type* error, not a deprecation — the drift table's row says so explicitly, because the old spelling is
   the kind a worker would "fix" by silencing a warning instead. Three `Prime.not_unit` →
   `Prime.not_isUnit` renames and one `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` beside it.
3. **One mathlib import added** (`Mathlib.Analysis.SpecialFunctions.Log.Summable`, for
   `Complex.multipliable_one_add_of_summable`): the only import added in either module, and the order
   sanctions exactly that kind.
4. **The manager's scaffold put one headline in the pin's file-level namespace** (FR-0186): the module, the
   checker (`1 ok`), the axioms probe and the consumer all passed with the headline at
   `P2MW.S_….NumberField.exists_…` instead of `NumberField.exists_…`, because `check_port` matches
   *content*. It was found by `#check`ing the wrapper's qualified name — and only after the module was
   `lake build`, since `#check` reads the olean. The fix was one line deleted and one consumer
   qualification; the rule is recorded.
5. **The set's build cone now includes warning-carrying modules**: `RegularProlongationResidueIntegralClosure`'s
   `lake build` replays 41 warnings from modules its new imports pull in (`P1/TraceEngine` 14,
   `P1/PerfectResidue` 11, `Genus/Stichtenoth` 8, `P1/Separating` 3, `Defs/LocalResidue` 3,
   `Tate/CompletionTraceSum` 1). None is in this set and none is silenced; they are carried forward as a
   hygiene item (the modules are outside the set's scope, and fixing them is a separate wave).

### 6.2 The re-read

Taken with SET-AF50's (see [SET-AF50.md](SET-AF50.md) §6.2): this set's two rows account for 685 lines of
the 1,988 the two sets moved together, and its own consumer chain
(`AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family`,
574; `NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar`, 209) is priced
there.
