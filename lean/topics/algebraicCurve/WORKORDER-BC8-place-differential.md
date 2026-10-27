# WORKORDER BC8 — the place/differential dictionary after a constant field extension

Scope: **one new module** and **two insertions into one existing, wired module**.

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | home |
|---|---|---:|---|
| `AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber` | `S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber` | 672 | **new** `Place/EvalAtNorm.lean` |
| `AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain` | `S_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain` | 51 | **new** `Place/EvalAtNorm.lean` |
| `AlgebraicCurve.Place.ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem` | `S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem` | 517 | insert `Differential/RegularDiffs.lean` |
| `AlgebraicCurve.Place.ordDiff_eq_ordDifferential` | `S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential` | 44 | insert `Differential/RegularDiffs.lean` |

Pin at `aa2d8b3`. Statements from the wrappers, proofs from the `S_` files.

**The mathematics.** `evalAt_norm_eq_prod_fiber`: at a rational place `v`, the value of the norm
of `f` is the product of `f`'s values over the fibre — the valuation-theoretic companion of
`ord (norm f) = ∑ inertiaDeg · ord f`. `mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain`:
the `K'`-coefficients of a Riemann–Roch element descend. The two differential nodes identify the
two notions of order of a differential and show that a divisor whose support is `F`-integral has
vanishing order-differential along the extension.

## Why these homes (do not re-home them)

`Place/EvalAtNorm.lean` must import `Defs/PushPull.lean`, `Place/ConstantFieldExtension.lean`,
`Place/IntegralClosureAtFiber.lean`, `RingTheory/Norm/Elementary` **and**
`Place/ConstantFieldExtensionRamification.lean` (the second node's premise): no existing module is
above that set. `Differential/RegularDiffs.lean` is above the differential nodes' three premises
and is wired (2 `spec-pin:` lines, green); append the two wrappers and their `S_` files.

## Rules

- New module: header with prose and `spec-pin:` lines (wrapper + `S_` file for each of its two
  nodes), `set_option autoImplicit false`, `noncomputable section`; statements from the wrappers,
  binder spelling character-for-character.
- Insertions only into `Differential/RegularDiffs.lean`; no existing declaration touched.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>`; finished module `flock .lake/flt_build.lock timeout 110 lake build <module>`.
  Commands under 2 minutes, own `timeout`, no loops; logs under `lean/tmp/bc8-*.log`.
- `check_port.py --force` → 0 mismatch / 0 missing per module; axioms clean; 0 warnings; no
  `sorry`; no markers; no commit; stop and report rather than promoting a `private` helper.

## Report (one message)

per module: build + warnings, the checker summary line; then the four axioms lines, deviations
beyond a tactic rename, and any blocker.
