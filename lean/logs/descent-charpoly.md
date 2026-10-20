# The descent node — the characteristic-p / subfield descent of a matrix representation (R1)

**Status: landed 2026-10-20.** The `Representation` family's big node is ported whole: three new
modules under `FLTForHuman/GaloisRep/Deformation/`, **1,938 port lines**, **103 public declarations
all wired and checked**, the pin's 11 `private` helpers kept private, `0 mismatch / 0 missing /
0 own / 0 kw`, 0 warnings. Order:
[WORKORDER-R1-descent-charpoly.md](../topics/deligneSerre/WORKORDER-R1-descent-charpoly.md);
sibling cut (the five small leaves):
[logs/representation-leaves.md](representation-leaves.md).

| module | lines | publics | pin pieces |
|---|---:|---:|---|
| `GaloisRep/Deformation/Charpoly.lean` | 357 | 25 | `PieceCS` + `PieceNS` (31–316) |
| `GaloisRep/Deformation/Cocycle.lean` | 682 | 35 | `PieceDCS` + `PieceSUA` (319–903) |
| `GaloisRep/Deformation/FiniteDescent.lean` | 899 | 43 | `PieceGD` + `PieceKF` + headline (906–1692) |

Pin `aa2d8b3`:
`P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean`
(1,692 lines, 105 public declarations) with its `Theorems/Thm_…` wrapper as the statement authority.

**Cover of the 105-declaration surface.** 103 declared and checked here + the two
`Deformation.matrixRepresentation*` declarations imported from
`GaloisRep/Defs/MatrixRepresentation.lean` (a `Definitions/`-module transcription already on the
legacy `PORT_FILES` wire, `spec/old_check_stmts.py:3838`) — imported, not restated (§2.4). The
pin's `theorem solution` is declared at the wrapper's root name
`Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
(equal checker hash to `solution`, the `PoissonSummationPi` precedent). `Matrix.trace_eq_of_charpoly_eq`
is stated at the pin's root `Matrix` name; `RepConjAux.trace_eq_of_charpoly_eq` stays private and
untouched, so nothing was promoted.

## Verification

* `python3 spec/check_port.py --force <module>`: `25 ok` / `35 ok` / `43 ok`, each
  `0 mismatch, 0 missing, 0 own, 0 kw`; `--strict-markers` across the three:
  **`103 ok, 0 mismatch, 0 missing, 0 own, 0 kw — 3 module(s)`**.
* `lake build` green, 0 warnings: Charpoly **5.12 s**, Cocycle **5.52 s**, FiniteDescent **5.79 s**
  wall (≈1.6 s no-op incremental). Edit loop at the 200k cap: clean, no `set_option maxHeartbeats`.
* `#print axioms` (re-checked by the manager): the headline and
  `DeligneSerre.lemme613_realizable_of_finite_of_spanTop` are
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `axiom`, no `import Mathlib`.
* the pin's `p2m_export`/`p2m_reactivate` scaffolding and the `P2MW.S_…` wrapper namespace became
  scopes; the drift is proof-only (`if_neg` → `ite_eq_right`, `Set.mem_setOf_eq` →
  `Set.mem_ofPred_eq`, one dropped `rfl` after `convert`, a `set M` before the `glnPoincare_col`
  rewrite at v4.34's implicit transparency, four `haveI` → `have` for the style linter, and the
  `surjInv` step restated as `ext/show/exact`). No statement, binder or name moved.

## mathlib first

Recorded per declaration in each module header. **Proof substitutions**: `Matrix.map_injective`
(for the pin's `map_injective_of_injective`), `GeneralLinearGroup.scalar_commute` (for
`glnScalar_mul_comm`), `GeneralLinearGroup.map_scalar σ c` (for `glnMap_scalar`); `coe_scalar` is
definitional. **Ingredients used verbatim**: `AlgEquiv.fintype` (which forced
`import Mathlib.FieldTheory.Fixed` — the pin got it from `import Mathlib`; without it every
`∑ σ : L ≃ₐ[K] L` fails), `linearIndependent_monoidHom`,
`Submodule.exists_dual_map_eq_bot_of_lt_top`, `Submodule.exists_fun_fin_finrank_span_eq`,
`Matrix.exists_mulVec_eq_zero_iff`, `GeneralLinearGroup.center_eq_range_scalar`,
`algEquivEquivAlgHom`, `IsGalois.mem_range_algebraMap_iff_fixed`, the `FiniteField`
Frobenius/norm API, `Algebra.norm_eq_prod_automorphisms`,
`Matrix.trace_eq_neg_charpoly_coeff`/`det_eq_sign_charpoly_coeff`. **Negatives**: the charpolyRev
transport and coefficient fixing; all subring-descent/carrier declarations (`subringPreimage`,
`subringDescent*`, `conjRep`, `CharpolyCoeffsInSubfield`, `SubfieldDescentInputs`,
`DescentConjugatorSupply`); Hilbert 90 for `GLₙ` (mathlib's `Hilbert90` is the `Lˣ`/group-cohomology
form; `Hilbert90.aux_ne_zero` is the scalar analogue of `eq_zero_of_forall_dotProduct_glnPoincareVec`);
`glnPoincare`, `glnTwistedNorm`, `scalarGL`, `IsConjugatorCocycle`/`Family`; the finite-field
norm-one normalisation; and the Brauer–Nesbitt bridge (that node is imported from
`Algebra/BrauerNesbittRepresentation.lean`).

**No deviations, no `own:` rows, no blockers, nothing owed.** `spec/decl_markers.tsv` was not
touched.

## Family status

The `Representation` family in the D-S cone is now **complete**: six nodes, 2,351 raw pin lines →
2,893 port lines in eight modules (R2's five + R1's three), **124 checked declarations**
(`21 + 103`), 0 mismatch / 0 missing. Global checker after both landings:
**3,010 ok / 0 mismatched / 0 missing / 11 own / 0 kw over 117 wired modules** (was
2,884 / 109 before the family; the +126 is 21 + 103 + the 2 promoted helpers now diffed in
`Algebra/BrauerNesbittRepresentation.lean`).
