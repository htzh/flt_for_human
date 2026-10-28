# WORKORDER PC1 — the charted space on the places over ℂ

Scope: **one new module** and **one insertion**. Nothing else may be edited. (Part of SET 5,
[SET-5.md](SET-5.md) §1; the new module is forced by the import direction — reviewer's call 2.)

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` | `S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` | 482 | 49 | **new** `FLTForHuman/AlgebraicCurve/Place/ChartedSpace.lean` |
| `AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict` | `S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict` | 23 | 1 | insert into `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluation.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements come from each node's
`Theorems/Thm_<stem>.lean` wrapper**, proofs from the `S_` file.

**The mathematics.** Over `ℂ`, the places of a one-variable function field carry a structure of
connected compact Hausdorff complex manifold — a chart at each place, in which the meromorphic
function `v ↦ evalAt v f` has `meromorphicOrderAt` equal to `v.ord f`. This is the charted-space
capstone of the `localParam` family: the pin assembles it from the chart (`localParam`), its
branch uniqueness, the finite cover, the place dictionary of `ComplexDictionary`, `OrdCalculus` and
weak approximation. The second node is one line of that dictionary — evaluation at a `restrict`
agrees with evaluation in the base field.

## Why these homes (do not re-home them)

**The capstone cannot be inserted into any existing module.** Its six pin premises live in
`Place/LocalParamDatum`, `Place/BranchUniqueness`, `Place/FiniteCover`, `Place/ComplexDictionary`,
`Place/OrdCalculus` and `Place/Approximation`, and **no single port module is above all six** —
`Place/ComplexDictionary.lean` (the nearest, and the natural subject) is above only
`Place/ConstantFieldExtension` among them. A new module that imports all six is the only
non-cyclic home; add whatever else the proof needs.

`Place.evalAt_algebraMap_eq_evalAt_restrict` goes into `Defs/PlaceEvaluation.lean` (11 `spec-pin:`
lines, green): it is an `evalAt` law at a `restrict`, and that module is above `Defs/PushPull.lean`,
where `Place.restrict`, `restrictInclusion` and `restrictResidueMap_residue` live.

**Import, do not copy** — 127 of the capstone's declaration lines and 145 more of its substitutions
are already in the port:

- the six premises, by name (above);
- from `Defs/PushPull.lean`: `restrict_fiber_finite` (36), `irreducible_mk_comap` (35),
  `ord_restrict` (34), `ramificationIndex_dvd_ord` (30), `SumRamificationInertia` (29),
  `pullback_mem_degZero` (22), `pullback_apply`, the `instIsScalarTowerResidueFieldRestrictPushforward`
  / `instIsLocalHomRestrictInclusion` instances;
- from `P1/EnginePrelude.lean`: `isPrincipalIdealRing_comap` (51), `isUnit_mk_comap_iff` (25);
- from `Defs/Place.lean`: `not_isField_of_ne_top` (28), `exists_unit_mul_zpow` (16),
  `ofHeightOneSpectrum` (12);
- from `Place/OrdCalculus.lean`: `ord_pos_of_mem_maximalIdeal` (14),
  `residue_eq_zero_of_ord_pos` (12), `evalAt_eq_of_ord_sub_algebraMap_eq_one` (11);
- from `Defs/Repartitions.lean`: `adicValuation_le_one_of_mem`, `adicValuation_eq_exp_neg_ord`;
- from `Defs/PlaceEvaluation.lean`: `evalAt_mul`, `evalAt_algebraMap`; from
  `Place/BranchUniqueness.lean`: `t_mem`; from `Defs/WeilOfKaehler.lean` / `Defs/PushPull.lean` /
  `Differential/ConstantFieldExtension.lean`: `ord_nonneg_of_mem`, `mem_of_ord_nonneg`,
  `mem_iff_ord_nonneg` (take the `Theorems/` wrapper's binders);
- in `Place/ComplexDictionary.lean` (SET 4): the `ConnectedOfCharted` dictionary — `reading`,
  `OrderHypothesis`, `finite_setOf_ord_ne_zero`, `exists_nonconst_mem_of_ne`,
  `eventually_mem_chart`, `tendsto_reading`, `continuousAt_reading`, `analyticAt_reading`,
  `continuousAt_evalAt`, `false_of_isClopen` — and `connectedSpace_…`, which is the premise.

## Rules

- The new module: header `/- … -/` with prose on the mathematics and `spec-pin:` lines for both
  the wrapper and the `S_` file, no cross-references to port modules or notes;
  `set_option autoImplicit false`, `noncomputable section`. Universe and binder spelling from the
  wrapper, character for character.
- The pin's `S_` file opens with three `attribute` walls (`[-instance]` / `[-simp]`, ≈150 instances).
  **Do not transcribe them** (BC6/BC8 precedent): they exist to disable the pin's own global
  instances, and the port does not carry them.
- The insertion: append the wrapper **and** the `S_` file to `Defs/PlaceEvaluation.lean`'s existing
  `spec-pin:` block; keep every existing declaration untouched.
- Imports stay specific: **never `import Mathlib`** in a library module. Replace the pin's
  `import Mathlib` (and any broad import a `S_` file carries) with the specific mathlib modules the
  file needs — playbook §4's hygiene rule.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished module `flock .lake/flt_build.lock timeout
  110 lake build <module>`. Every command under 2 minutes, its own `timeout`, no loops; logs under
  `lean/tmp/pc1-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module, every added
  declaration `ok`; `#print axioms` on the capstone → `[propext, Classical.choice, Quot.sound]`;
  0 warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; no commit; no
  `spec/decl_markers.tsv` row.
- If a proof needs a `private` port helper or a declaration below its home, **stop and report** —
  do not promote, do not restate, do not edit a hub.
- This module's 49-declaration surface is the largest this set adds. Leave every declaration
  public as the pin states it; if the checker objects, keep the pin's *own* prelude re-spellings
  `private` and say which, and do not invent names for the rest.

## Report (one message)

per module: build + warnings, the checker summary line, the declaration count; the capstone's
axioms line; which prelude copies stayed `private` and why (one line each); any blocker.
