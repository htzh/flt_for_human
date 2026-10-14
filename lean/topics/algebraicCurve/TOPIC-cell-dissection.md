# The cell-dissection / radial-region layer — plan and structure (phase 3)

**Set R is landed (2026-10-14); phase 3 is paused here.** The nine
`AlgebraicCurve.RadialRegion.*` nodes are ported as **17 modules** (eight tier-3 engines +
nine tier-1 façades, 9,934 lines), checker `9780 → 9789` — delta **+9**, exactly the nine
headlines, 0 mismatched / 0 missing — and the register gained 489 engine rows, all green
and `--check`-current. The `CellDissection` sets — **C1** (`exists_polygonWord`,
`exists_tree_cotree`, `euler_count_grid`, `kirchhoff_and_jump_formula_of_arc_values`),
**C2** (the seven path-integral/residue nodes and the four external premises they need)
and the **consumer** `exists_pairedCellFamily` — are **not begun**. The work stops at the
Set R boundary because the D-S column does not need any of it yet: the subject is prunable
and its D-S-side exclusion is
[../deligneSerre/PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md).

**What this is.** The curve-theory analytic layer that dissects a compact Riemann
surface into radial cells and integrates differentials over the resulting loops:
`AlgebraicCurve.RadialRegion.*` (a rectangle, and then a grid, realised as a radial
region), `AlgebraicCurve.CellDissection.*` (the cell complex, its words/trees, the
Kirchhoff and jump formulas, the path-integral and residue identities), and the
consumer `AlgebraicCurve.exists_pairedCellFamily`. It is the input to the
Abel–Jacobi / period-lattice route to `CuspForm.exists_galoisRep_of_point`.

**Ownership.** This is the **Riemann–Roch column's phase 3**, not the
`DeligneSerre` column's. `PORTING-RR.md` scopes it out of phase 1/2, and
`riemannRoch/WORKORDER-H3-weildifferential.md` lists `CellDissection` under "not this
set — phase 3, out of phase-1 scope". (The `24 nodes / 56,383 lines` figure in
`PORTING-RR.md` §3 is the *residue* block `residueTheorem | tateAgreement |
residueTrace`, which has since been ported — 0 unported in the cone; this subject's
figure is the 205 one below.)

**In the D-S cone by closure, not by need (measured 2026-10-14).** All **21** cluster
nodes are in the *default* forward closure of
`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` (2,307 nodes): their
own closure is **147 nodes, 6.4%** of it, and the 21 `S_` files are **27,169 raw
lines ≈ 2.5%** of its 1,089,430. The route is 13–14 hops through the Abel–Jacobi /
`Pic0` layer:

```
D-S target ← …_weightOne_hecke_eigen ← …_weightTwo_hecke_eigen
 ← CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt
 ← …exists_ringHom_rationalHeckeAlgebraOne_mul_eq
 ← ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm
 ← Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero(_complex)
 ← Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
 ← exists_loops_pathIntegral_reciprocity(_raw) ← exists_cellDissection
 ← exists_pairedCellFamily ← (the cluster)
```

It is nonetheless **prunable**, and the mechanism is concrete. The step this route
feeds, `ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm`,
cites **two independent supplies for the same job**: the differentials ↔ cusp-forms
transport
`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
— the route the D-S/RR columns actually port — and
`AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`,
which is what the Abel–Jacobi / path-integral / `CellDissection` route (this cluster)
supplies. So the D-S column takes the transport and drops the second route:
**prunable = 205 nodes / 107,257 lines**, taking the D-S forward target to
1,666 / 798,338 — a saving of 201 nodes / 103,660 lines, at a **13-node rewiring
frontier** (the kept nodes that directly cite the pruned route and are rewired to the
transport) — `deligne-serre-weight-one-scout.md` §4.2, which puts it plainly: "that
transport is the bottleneck, not RR itself". The cluster is therefore on *a* route
from the D-S target — hence in its closure and on its ready shelf, which is where
`exists_rect_sixArcs` was first seen — but not on the route the D-S column takes.
Schedule it as RR phase 3.

The D-S-side exclusion is written down once, as a canonical set with the exact
frontier flags, in
[../deligneSerre/PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md);
it is what a future D-S frontier read uses so these leaves do not reappear on the
shelf.

## 1. The definition layer (manager pre-round)

Every node in the cluster imports the same two pin `Definitions/` modules, and both
were absent from the port. They are homed whole (playbook §2.3) as tier-1 modules,
built on the already-homed `Defs/PlaceEvaluation.lean`,
`Defs/RegularDifferentials.lean`, `Defs/CanonicalDivisor.lean`, `Defs/Divisor.lean`:

| pin `Definitions/` module | decls | lines | port home |
|---|---:|---:|---|
| `Def_AlgebraicCurve_ComplexLineIntegral` | 17 | 101 | `FLTForHuman/AlgebraicCurve/Defs/ComplexLineIntegral.lean` |
| `Def_AlgebraicCurve_CellDissection` | 20 | 155 | `FLTForHuman/AlgebraicCurve/Defs/CellDissection.lean` |

Contents: B is the complex line-integral vocabulary — `Place.dCoordFn`/`dCoord`'s
uniqueness, `chartRead`, `readDifferential`, `IsPrimitiveAlong`, `pathIntegral`,
`abelJacobiVec`/`Div`, `pathPeriodLattice`. A is the dissection vocabulary —
`RadialRegion` (`q`, `r` continuous/`2π`-periodic/positive, break points `φs`,
piecewise `C²`) with `K`/`Kint`/`loop`/`loop'`/`arcIcc`/`arcSet`; `AnalyticCoord`;
`Cell` (`carrier`/`interior'`/`bdry`/`arc`); `CellDissection` (cells, sides, ends,
vertices, the arc-reversal and cover/interior axioms) with `arcOf`/`edgeInt`/
`skeleton`; and `coeffIn`, `Cell.bdryIntegrand`.

**Landed (2026-10-14).** Both homes are in place, green and wired (tier 1): 37
declarations transcribed verbatim (a comment/import-stripped `diff` against the pin is
empty for both files), building clean, and the checker moved
`9743 → 9780 identical, 0 mismatched / 0 missing (9781 → 9818 checked)` — the delta is
exactly the two modules' public surface. The pin's bare `import Mathlib` became
specific imports (notably `Mathlib.LinearAlgebra.Span.Defs`, `Mathlib.LinearAlgebra.Span`
having been removed in v4.34.0); no statement or proof was adapted.

**This is the trap `frontier.py` cannot see.** `--ready` and the leaf views price
all 20 cluster nodes as self-contained (`needed = 1`, no premises) because they do
not walk imports; the missing definition modules make none of them startable. Every
work order in this topic begins by confirming these two modules are built.

## 1a. Visibility — the playbook's rule

This is the playbook's standard rule, not a column choice: **public theorems (the
pin's API) stay public, and a public declaration with no known consumer need not be
wired** ([porting-playbook.md](../../porting-playbook.md) §0.5, §4.1). An unwired
public declaration is not lost — it lives in an **unlisted** (tier-3) module and the
register recovers it from its `-- pin:` comment; real mathematics is written once and
is not demoted to `private` (§5).

The pin's `S_` files declare the development's lemmas public (537 across the nine
`RadialRegion` nodes: `grid_geometry` 194, `window_perimeter` 136, `rect_sixArcs` 59,
the reparam pair 40 each, …). So the port keeps them public — and, since the checker's
tier is per module, puts "public but unwired" where it belongs, in an unlisted module.
Each node is written as the pair the pin already suggests (its internal development
namespace plus a top-level `solution`):

* **engine** `AlgebraicCurve/RadialRegion/Engine/<Node>.lean` (tier 3) — the `S_`
  file's development at the pin's visibility, registered in `spec/UNWIRED-PUBLIC.md`
  with `-- pin:` provenance: importable, reusable, not diffed; and
* **façade** `AlgebraicCurve/RadialRegion/<Node>.lean` (tier 1) — the wrapper headline
  verbatim, the node's API, proven from the engine so it stays verified.

One module per node cannot express this: a listed module has *every* public
declaration diffed, and demoting the internals to `private` would hide the pin's API
and force a visibility edit on the first consumer. Same shape for the other cluster:
`AlgebraicCurve/CellDissection/Engine/<Node>.lean` beside `.../<Node>.lean`. (The
`NumberField.CompletedDedekindZeta` port is the same pattern — a natural-named theory
plus a thin listed façade — recorded under "Tier-3 theories not in `PORT_FILES`" in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md).)

## 2. The cluster

Measured with `port_advise`/`port_plan` over each half
(`tools/deps/build/{celldiss,radial}_{advise,plan}.txt`):

| group | nodes | raw | decl lines | duplicate | **net new** | groups |
|---|---:|---:|---:|---:|---:|---:|
| `RadialRegion.*` (geometry) | 9 | 9,652 | 9,522 | 1,084 | **8,438** | 618 |
| `CellDissection.*` (combinatorics + integration) | 11 | 12,787 | 12,556 | 4,111 | **8,445** | 374 |
| consumer `exists_pairedCellFamily` | 1 | 4,730 | — | — | — | — |

All are graph leaves in the D-S demand (`build/leaves.txt`), so they never reach the
frontier `F`; none appears on the phase-1/2 ready shelf.

**The duplication is per family, not per node.**

* the `RadialRegion` reparametrisation pair is a **near-twin**:
  `exists_reparam_across_edge` vs `exists_reparam_same_side` share **614 lines / 37
  declarations**, differing by 52 diff lines (`bottom_shape`, `right_shape`,
  `left_shape`, `top_shape`, `core_anti`, `core_mono`, …). Port once as a shared
  `private` development with two public headlines (the WORKORDER-E shape).
* `CellDissection` shares substantial preludes across 2–6 files: `edge_pair` (234
  lines, 3 files), `book` (127, 2), `hasDerivAt_γ` (66, **6** files),
  `spanningTree_card` (115, `exists_polygonWord` + `exists_tree_cotree`),
  `local_inverse` (95), `coeff_mul_deriv` (58), `sub_sub_mem_of_atlas` (56, 2),
  `K_eq_image` (49), `isClosed_arc` (41), `coeff_eq_near` (25), …
* the remaining `duplicate` in each half is the `S_`/`Theorems` pairing.

Three *suspect* substitutions are flagged (`IsJump` → `PeriodPair.DiscriminantNeZero`,
type-only `def` matches) — read both copies before applying any.

## 3. The external premises

Nine nodes the cluster cites but which sit outside it, all in the D-S cone, all
leaves (silo lines in parentheses): `exists_dissectionScaleData` (2,429),
`coeffIn_local_calculus` (777), `exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg`
(740), `Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue` (646),
`pathIntegral_finset_sum_smul` (619), `Place.sum_fiber_ord_eq_finrank` (605),
`Place.sum_ramification_evalAt_eq` (434), `Place.analyticCoord_of_agree` (265),
`Place.analyticCoord_of_center` (117). They are shared by several cluster nodes and
must land before (or with) them.

## 4. Structure

The internal DAG is thin — the real coupling is the shared definition module plus
the external premises:

```
exists_rect_sixArcs ─┐
exists_refine_exact ─┴─► exists_window_perimeter ─┐
exists_reparam_across_edge ─┐                     │
exists_reparam_same_side ───┴─► exists_grid_geometry
exists_isOpen_starConvex_subset ─┬─► exists_primitives_jump_eq_zero_of_dualTree
                                 └─► exists_int_pathIntegral_eq_sum_periods_add_sum_residues
kirchhoff_and_jump_formula_of_arc_values ─┐
intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt ─┴─► exists_int_pathIntegral_eq_sum_periods_…
8 cluster nodes + 5 external ─► exists_pairedCellFamily
```

`RadialRegion` nodes are 7 at layer 0 and `exists_grid_geometry` /
`exists_window_perimeter` at layer 1; the `CellDissection` nodes are almost all
self-contained against the definition layer and the external premises.

`exists_rect_sixArcs` itself (1,839 raw, 1 public headline, 2 consumers) is the
`K`-and-six-arc description of a rectangle, and is the node the DeligneSerre column
deferred in [WORKORDER-P1](WORKORDER-P1-isPrimeOverValuationSubring.md) §2 for exactly
the missing-`Def_AlgebraicCurve_CellDissection` reason this pre-round fixes.

## 5. The cut, in order

| set | subject | nodes | net new | notes |
|---|---|---|---:|---|
| pre-round | the two definition modules | 2 modules | **landed** — 37 decls, checker +37 | tier 1, wired 2026-10-14 |
| P-ext | the `Place`/curve premises | 5 | ~4,050 | `sum_fiber_ord_eq_finrank`, `sum_ramification_evalAt_eq`, `analyticCoord_of_center/agree`, `dissectionScaleData` |
| R1 | the rectangle and its refinement | 2 | **landed** — 4 modules (2 engines + 2 façades), checker +2 | `exists_rect_sixArcs` (the deferred node) + `exists_refine_exact`; order [WORKORDER-R1](WORKORDER-R1-radial-rectangle.md) |
| R2 | the window perimeter | 1 | **landed** — engine + façade, checker +1 | `exists_window_perimeter`; consumes R1; order [WORKORDER-R2](WORKORDER-R2-window-perimeter.md) |
| R3a | the reparametrisation twin | 2 | **landed** — 1 engine + 2 façades, checker +2 | the two `S_` files are byte-identical through line 704 (development + both theorems); only the `solution` differs. Order [WORKORDER-R3a](WORKORDER-R3a-reparam-twin.md) |
| R3b | the grid geometry | 1 | **landed** — engine (2,908 lines, 193 public) + façade, checker +1 | `exists_grid_geometry`; consumes R3a; order [WORKORDER-R3b](WORKORDER-R3b-grid-geometry.md) |
| R4 | radial miscellany | 3 | **landed** — 3 engines + 3 façades, checker +3 | `exists_isOpen_starConvex_subset`, `exists_recip`, `exists_pow_pullback_laps`; order [WORKORDER-R4](WORKORDER-R4-radial-miscellany.md) |
| C1 | cell combinatorics | 4 | ~2,500 | `exists_polygonWord`, `exists_tree_cotree`, `euler_count_grid`, `kirchhoff_and_jump_formula_of_arc_values` |
| C2 | integration and residues | 7 + 4 ext | ~10,000 | the path-integral/residue nodes, `coeffIn_local_calculus`, `exists_isPrimitiveAlong_*`, `pathIntegral_finset_sum_smul`, `Complex.integral_radial_loop_*` |
| consumer | `exists_pairedCellFamily` | 1 | 4,730 | last; needs 8 cluster + 5 external |

Sets run one at a time (playbook §5); the manager reviews between them. A set's work
order follows the usual template: the pin `S_`/`Theorems` pair, the definition
modules it imports (now homed), the shared preludes to write once, the external
premises it consumes, and the build/verification block.

## 6. Verification

Each set is green when `spec/check_flt_statements.py` is unchanged in `mismatched` /
`missing` and its `identical` delta equals the new public surface, both modules
build at tier 1, and a `#print axioms` probe over the headlines is
`[propext, Classical.choice, Quot.sound]`. The pre-round landed as exactly **+37**
(9743 → 9780 identical, 9781 → 9818 checked).

## 7. Links

- [PORTING-RR.md](../PORTING-RR.md) §3 (phase scope, the 24-node / 56,383-line prune)
  and `riemannRoch/WORKORDER-H3-weildifferential.md` ("not this set").
- [WORKORDER-P1-isPrimeOverValuationSubring.md](WORKORDER-P1-isPrimeOverValuationSubring.md)
  (where `exists_rect_sixArcs` was deferred).
- Measurement artifacts: `tools/deps/build/celldiss_targets.txt`,
  `radial_targets.txt`, `celldiss_{advise,plan}.txt`, `radial_{advise,plan}.txt`.
