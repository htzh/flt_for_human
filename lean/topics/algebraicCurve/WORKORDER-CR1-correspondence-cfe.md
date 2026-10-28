# WORKORDER CR1 — the correspondence on regular differentials under a constant field extension

Scope: **one new module**, `FLTForHuman/AlgebraicCurve/Differential/CorrespondenceRegularCFE.lean`.
Nothing else may be edited (no existing module, no `spec/`, no `spec/decl_markers.tsv`). Part of
SET 6, [SET-6.md](SET-6.md) §1 (CFE) and §5.

## Node

| node | pin stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension` | `S_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension` | 309 | 6 | **new** `Differential/CorrespondenceRegularCFE.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`:
<https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean>
and its wrapper <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean>.
The statement is the wrapper's (its namespace is `OmegaBaseChangeProof`); the proof is the `S_`
file's.

**The mathematics.** Under a constant field extension `K ⊆ E`, `F ⊆ FE`, `F' ⊆ F'E` with
`φ, ψ : F →ₐ[K] F'` lifted to `φE, ψE : FE →ₐ[E] F'E` along the two inclusions, the Kähler map
commutes with the correspondence, is injective, sends regular differentials to regular ones, and
the regular differentials of `FE/E` are spanned by the image of those of `F/K`. Four conjuncts —
transcribe all four.

## What you write (4 declarations; two of the pin's six are already in the port)

- `ord_coe_nonneg` (10 lines) — the pin's unguarded form (a nonzero element of the valuation ring
  has nonnegative order; the `0` case is handled by the guard being absent). **The private
  `ord_coe_nonneg` in `Place/LaurentSeriesModel.lean` is a different statement** (it carries
  `y ≠ 0`), so do not reuse it; write the 10 lines at the pin's name.
- `mem_of_ord_nonneg'` (6 lines) — the unguarded variant of `Place.mem_of_ord_nonneg`
  (`Defs/PushPull.lean`, imported): `f = 0` case, then the public lemma. Keep it local.
- `exists_smul_D_eq_smul_dCoord` (23 lines) — new, and the proof's local engine; it uses
  `Place.exists_eq_smul_D_of_ord_ne_zero`, `Place.ord_diffCoeff_D_nonneg_of_perfectField`,
  `Place.diffCoeff_smul_D_eq` and `Place.exists_ord_eq_one_and_dCoord_eq`, all public in
  `Differential/Coefficient.lean` / `Defs/PlaceD*`.
- the wrapper's headline (213 lines) at
  `AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension`.

The pin's `ord_nonneg_of_mem` (line 56) and the second `mem_of_ord_nonneg` (line 60) are the
existing public `Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg`: import them.

## Imports (start here, adjust only with need)

```
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.AlgebraicCurve.Canonical.RegularDifferentialsFinrank
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.TranscendentalOfOrdNeZero
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
```
(`WeilExchange/Transport.lean` for `separableAlong_of_charZero`; the Defs come through these.)

Header `/- … -/` with prose and the two `spec-pin:` lines; `set_option autoImplicit false`;
`noncomputable section`; `namespace AlgebraicCurve`.

## Traps

- The proof's final step uses the **char-0** `Place.exists_comap_algebraMap_eq_of_constantFieldExtension`
  (`Place/ConstantFieldExtension.lean`). SET 6 made it a corollary of the char-free statement; its
  statement is unchanged, so call it by that name — do not switch to the `_of_isAlgClosed` one
  (this row carries `[CharZero K]` and its proof is the char-0 development).
- The pin's huge `attribute [-instance]`/`[-simp]` walls are dropped.
- `KaehlerDifferential.map K E F FE` is mathlib; the naturality conjunct is
  `LinearMap.map_smul`-level, not a new lemma.
- The row's own `ord_coe_nonneg` and `mem_of_ord_nonneg'` are *public in the pin's `S_` file*:
  state them public (the checker matches them by statement; they are this module's only helpers).

## Rules

- Statements are the wrapper's character for character; proofs are the `S_` file's, adapted to
  mathlib `v4.34.0` and the port's names. If a proof needs a `private` port declaration or one
  below the home, **stop and report** — do not promote, do not restate, do not edit a hub.
- Specific imports only (`import Mathlib` forbidden); no `set_option maxHeartbeats`; no
  `sorry`/`admit`/`axiom`; no commit.
- Edit loop from `lean/`: `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
  FLTForHuman/AlgebraicCurve/Differential/CorrespondenceRegularCFE.lean`; finished:
  `flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegularCFE`.
  **No tree build, no dependents**; every command under two minutes, its own `timeout`; log under
  `lean/tmp/cr1-*.log`.
- `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Differential/CorrespondenceRegularCFE.lean`
  → **0 mismatch, 0 missing**; `#print axioms` on the headline → `[propext, Classical.choice,
  Quot.sound]`; **0 warnings**; `dedup.py --module … --within` afterwards and report the clusters.

## Report (one message)

The build line and warnings, the `check_port` summary, the axioms line, the module's line count
and public/private counts, and any blocker or deviation (in particular if the 213-line headline
needed a proof step the port does not have).
