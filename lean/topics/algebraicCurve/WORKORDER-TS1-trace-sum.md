# WORKORDER TS1 — the trace sum: `∑_P ord(g) • y_P^* ω = 0`

Scope: **one new module**, `FLTForHuman/AlgebraicCurve/ResidueTheorem/TraceSum.lean`. Nothing else
may be edited (no existing module, no `spec/`, no `spec/decl_markers.tsv`). Part of SET 6,
[SET-6.md](SET-6.md) §1 (TS) and §5.

## Node

| node | pin stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero` | `S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero` | 629 | 33 | **new** `ResidueTheorem/TraceSum.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`:
<https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean>
and its wrapper <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean>.
The statement is the wrapper's; the proof is the `S_` file's (its namespace is `W11AbelDiff`).

**The mathematics.** For a tower `K ⊆ F ⊆ FE`, `K ⊆ E ⊆ FE` with `FE` a curve over `E`,
`F`/`K` of transcendence degree one, `g ∈ FE` and a finite set `S` of places of `FE` with local
`K`-algebra sections `y` of the `F`-algebra structure, the sum over `S` of `ord_P(g)` times the
pull-back along `y_P` of a regular differential of `F/K` is zero. This is the residue theorem
applied along a finite cover — the pin's Abel-differential sum.

## What to import (17 of the pin's 33 declarations are already in the port)

Byte-identical port copies — **import, do not restate**:

| pin decl (line) | port declaration |
|---|---|
| `ord_nonneg_of_mem` (37) | `Place.ord_nonneg_of_mem_vs` (`Defs/WeilOfKaehler.lean`) |
| `one_le_ord_of_mem_of_inv_not_mem` (52) | `Place.one_le_ord_of_mem_of_inv_not_mem` (`Place/ConstantFieldExtension.lean`) |
| `mem_iff_ord_nonneg` (69) | `Place.mem_iff_ord_nonneg_vs` |
| `uniformizer_mem` (86) | `Place.uniformizer_mem_toValuationSubring` (`Defs/PolarDifferentials.lean`) |
| `polyBasis` / `polyBasis_zero` / `ratFuncBasis` / `ratFuncBasis_zero` / `towerBasis` / `towerBasis_zero` (188–216) | the `HorizDeriv.*` six (`Differential/ConstantFieldExtension.lean`) |
| `coeffLin` / `coeffDer` / `coeffDer_uniformizer` / `differentialCoeff_D_mem` (259–284) | `coeffLin`, `coeffDer`, `coeffDer_uniformizer`, `differentialCoeff_D_mem` (`Differential/RegularDiffs.lean`) |
| `exists_basis_D` (224) | `exists_basis_D` (`Differential/ConstantFieldExtension.lean:141`, **public**; it takes `hfg` and derives the finiteness the pin passes as `hfin`, so call it with `hfg` and `ht`) |

`ord_eq_zero_of_isUnit`, `mem_maximalIdeal_of_not_isUnit`, `one_le_ord_of_mem_of_inv_not_mem`'s
port copies in `Differential/RegularDiffs.lean` are `private`; use the public ones named above
where they exist and otherwise write the 3–6-line lemma at the pin's name (public):
`irreducible_unifElt`, `coe_unifElt`, `ord_eq_zero_of_isUnit`, `mem_maximalIdeal_of_not_isUnit`.

So the new declarations are, in the pin's order: `irreducible_unifElt` 4, `coe_unifElt` 4,
`ord_eq_zero_of_isUnit` 3, `mem_maximalIdeal_of_not_isUnit` 3, `exists_unit_mul_uniformizer_zpow`
6, `exists_mem_eq_uniformizer_mul` 21, the five `logDer_*` (`logDer_mul` 6, `logDer_zpow` 8,
`logDer_mem_of_ord_eq_zero` 7, `logDer_eq` 14, `logDer_uniformizer_mem` 29), `coeffLin_apply` 3,
`coeffDer_apply` 3, `trace_localResidue_eq` 12, `trace_localResidue_eq_zero` 5,
`residueTheorem_of_curve` 46, `main` 222, and the wrapper's headline 20.

## Routes and traps

- The five `logDer_*` lemmas are about an **arbitrary derivation** `Θ : Derivation R L L`
  (`section LogDer` in the pin), not about a place: keep that generality, they are the module's
  self-contained prelude.
- `residueTheorem_of_curve` (46 lines) is the pin's local restatement of the general residue
  theorem for a curve. **First** check whether `ResidueTheorem/GeneralFromK.lean`'s headline
  (`residueTheorem_of_isAlgClosed`) already gives it at these binders; if it does, use it and drop
  the 46 lines; if not, transcribe it and say so in the report.
- `main` (222 lines) is the proof body; the wrapper's `solution` is its instantiation at the
  wrapper's binders. Do not weaken either.
- The pin's three `attribute [-instance]`/`[-simp]` walls are dropped (the port installs none of
  those instances).
- The `S_` file's `#check`/`#print axioms` tail and its `P2M.Util` scaffolding are dropped.

## Imports (start here, adjust only with need)

```
import FLTForHuman.AlgebraicCurve.ResidueTheorem.GeneralFromK
import FLTForHuman.AlgebraicCurve.LocalResidue.Instance
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.RegularDifferentialsFinrank
import FLTForHuman.AlgebraicCurve.Genus.RatFunc
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Differential.RegularDiffs
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.DifferentialPushPull
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisorUniformizer
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.LocalResidue
import FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
```

Header `/- … -/` with prose and the two `spec-pin:` lines (wrapper + `S_` file); `set_option
autoImplicit false`; `noncomputable section`; `namespace AlgebraicCurve` (the wrapper's names are
`AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero`).

## Rules

- Statements are the wrapper's character for character; proofs are the `S_` file's, adapted to
  mathlib `v4.34.0` and the port's names. If a proof needs a `private` port declaration or one
  below the home, **stop and report** — do not promote, do not restate, do not edit a hub.
- Specific imports only (`import Mathlib` forbidden); no `set_option maxHeartbeats`; no
  `sorry`/`admit`/`axiom`; no commit.
- Edit loop from `lean/`: `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
  FLTForHuman/AlgebraicCurve/ResidueTheorem/TraceSum.lean`; finished:
  `flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.AlgebraicCurve.ResidueTheorem.TraceSum`.
  **No tree build, no dependents**; every command under two minutes, its own `timeout`; log under
  `lean/tmp/ts1-*.log`.
- `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/ResidueTheorem/TraceSum.lean` →
  **0 mismatch, 0 missing**; `#print axioms` on the headline → `[propext, Classical.choice,
  Quot.sound]`; **0 warnings** (read the edit loop's output; `lake build` alone hides linters);
  `python3 tools/deps/dedup.py --module FLTForHuman/AlgebraicCurve/ResidueTheorem/TraceSum.lean
  --within` afterwards and report its clusters.

## Report (one message)

The build line and warnings, the `check_port` summary, the axioms line, the module's line count
and public/private declaration counts, whether `residueTheorem_of_curve` was transcribable or
replaceable, and any blocker or deviation.
