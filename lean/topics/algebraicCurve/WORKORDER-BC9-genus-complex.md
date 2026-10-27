# WORKORDER BC9 — the Kummer splitting-field genus and the complex place dictionary

Scope: **two new modules**, nothing else edited.

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | home |
|---|---|---:|---|
| `AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord` | `S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord` | 263 | **new** `Genus/SplittingFieldGenus.lean` |
| `AlgebraicCurve.Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` | `S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` | 369 | **new** `Place/ComplexDictionary.lean` |

Pin at `aa2d8b3`. Statements from the wrappers, proofs from the `S_` files.

**The mathematics.** The genus of the function field of a Kummer splitting field: with
`α ^ q = f`, `F⟮α⟯ = ⊤` and `q ∣ v.ord f` at every place, `genusFF (F⟮α⟯) - 1 = q · (genusFF F - 1)`
— fifteen pin premises, the heaviest node of the set. The other is the analytic side of the
place dictionary: the place space of a complex function field is connected, and the meromorphic
order of a function at a charted point is its `ord`.

## Why these homes

Both need material that no single existing module sits above: the genus node consumes eleven
modules (`RiemannRoch/Assembly`, `Differential/Hurwitz`, `Canonical/PolarDifferentials`, the
genus and place layer), the complex node seven (`ResidueTheorem/RRAssembly` among them). Each new
module imports its premise modules plus what its proof needs. Neither may import a module the
set is editing in another order without saying so in its report.

## Rules

- Each module: header with prose and `spec-pin:` lines (wrapper + `S_` file),
  `set_option autoImplicit false`, `noncomputable section`; statements from the wrappers,
  binder spelling character-for-character.
- The genus node has **fifteen premises** and a 263-line pin file: budget the wall time, and if a
  premise's port declaration is `private` or below the new module, **stop and report**.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>`; finished module `flock .lake/flt_build.lock timeout 110 lake build <module>`.
  Commands under 2 minutes, own `timeout`, no loops; logs under `lean/tmp/bc9-*.log`.
- `check_port.py --force` → 0 mismatch / 0 missing per module; axioms clean; 0 warnings; no
  `sorry`; no markers; no commit.

## Report (one message)

per module: build + warnings, the checker summary line; then the two axioms lines, deviations
beyond a tactic rename, and any blocker.
