# S-2 work order — the lattice/index arithmetic

**Status: drafted 2026-10-07, for dispatch after S-1 (`HoloLift.lean`) is committed and
reviewed.** Second set of row S; the reconnaissance is
[TOPIC-V5-row-S-scoping.md](TOPIC-V5-row-S-scoping.md) §2.2 and §3, re-measured here against
the tree at dispatch. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
Depends on already-landed sets: S-1 (`Elliptic/PeriodPair/HoloLift.lean`),
P-SET-1/P-SET-2 (`Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,JLine}.lean`),
D-1/D-4/D-5 (`Isogeny/{BaseChange,KernelCyclicTransfer,KernelBaseChange}.lean`),
`Place/Dictionary.lean`, `IsogenyEndDatum/Engine.lean`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2, §2.1–§2.4, §3.1–§3.5, §4–§5.

## 1. Scope

Land the row's **lattice/index arithmetic**: the two pin nodes

* `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker` (the 978-line
  file) — given `α : ℂˣ` and `ψ : E(ℂ) →+ E'(ℂ)` intertwining the two ℘-maps, produce
  `β : ℂˣ` with `(L'.scale β).lattice ⊆ L.lattice` and `sublatticeIndex L (L'.scale β) =
  Nat.card ψ.ker`;
* `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`
  (the 2,021-line file) — given a **cyclic** kernel of order `N`, produce `β` with the same
  inclusion, `sublatticeIndex L (L'.scale β) = N`, and `IsAddCyclic (sublatticeQuotient L
  (L'.scale β))`;

together with the three `ModularCurve` classes they prove —
`KwD5BetweenCurvesIndexDual`, `KwD5BetweenCurvesKerQuotEquivBC`,
`KwD5BetweenCurvesPointHomSublatticeCyclic` — and the `hID_*` / `kqe_*` engines that prove
them. This is the arithmetic converse of S-1: S-1 lifts the point map to `ℂ`, S-2 reads the
lattice index and the cyclicity of the quotient off it.

The pin's 2,021-line `solution` is assembled from the other two: it derives
`hH2 : KwD5BetweenCurvesHoloLift` from S-1's headline, `hID : KwD5BetweenCurvesIndexDual`
from the 978 headline, and closes with
`kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three hH2 hID kw_surgehgf4_kqe_proved`. **The port
does not need to re-derive `hH2`**: S-1 landed
`ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift : KwD5BetweenCurvesHoloLift` directly
(`HoloLift.lean:894`), so use it.

**Not this set:** the primitive-coset / `jLattice` column (S-3, the 848 node), the
`E₄³ − E₆²` / `jLattice` tail (S-4), and the capstone (SC). The S-3 ℤ²-lattice invariants
(`natGen`, `latticeOf`, `aOf`, `dOf`, `bOf`, `KwSublatticeQuotientZZTransport`) are **not**
this set's and must not be declared here (checked absent from the port). A worker who reaches
an unported prerequisite stops at the boundary and reports.

## 2. Source and the dedup

Statement authorities (spell the binders **exactly**):

* `Theorems/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean`
  (11 lines):
  `(L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (α : ℂˣ)
  (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
  (hψ : ∀ z, L'.toPoint hL' ((α : ℂ) * z) = ψ (L.toPoint hL z)) : ∃ β : ℂˣ, …`
* `Theorems/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean`
  (26 lines): the same `L L'` plus the gate/`AbelTheorem` instances, `ι hι hfin hN`,
  `(N : ℕ) [NeZero N]`, `(hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)`,
  `(hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)`, concluding
  `∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
  PeriodPair.sublatticeIndex L (L'.scale β) = N ∧
  IsAddCyclic (PeriodPair.sublatticeQuotient L (L'.scale β))`.

The two `S_` files: `S_…natCard_ker.lean` (978 lines, 48 declarations) and
`S_…isAddCyclic_sublatticeQuotient.lean` (2,021 lines, 136 declarations). The 978 file
imports only `Def_PeriodPair_Uniformization` and the two ported `Thm_PeriodPair_{discriminant_ne_zero,isUniformization_toPoint}`
wrappers; the 2,021 file imports S-1's wrapper and the 978 wrapper (plus the ported place
dictionary). So the intra-set dependency is **978 first, then 2021**, and S-1's headline is an
import of the 2,021 node only.

`port_advise` on the two files (`--targets build/rowS2_targets.txt`): **68 substitutions
≈ 868 lines** — `Place/Dictionary.lean` 16, `PeriodPair/Lattice.lean` 16,
`PeriodPair/Uniformization.lean` 13, `IsogenyEndDatum/Engine.lean` 11, `PeriodPair/Basic.lean`
5, `Velu/RestrictAlong.lean` 4, `WeilDifferential.lean` / `Discriminant.lean` /
`PlaceEvaluationAlgebra.lean` 1 each. **41 names are proved in both target files (≈768
removable lines)**, dominated by `kw_surgehgf4_hID_dualIndex_eq` (75),
`card_torsionBy_latticeQuotient` (53), `kw_surgehgf4_hID_sublatticeIndex_scale_nat` (53),
`KwD5BetweenCurvesIndexDual` (47), `kwSublatticeIndex_scale` (43),
`kw_card_torsionBy_zlatticeQuotient_finrank_real` (39), `gate_scale_mul` (32) — i.e. the two
files ship the same `hID_*` block and the same torsion prelude twice, **which is why S-2 is
one module**.

**The three classes are new content.** `port_advise` reports
`KwD5BetweenCurves{IndexDual,PointHomSublatticeCyclic,KerQuotEquivBC}` as "substitutes"
against `PeriodPair.DiscriminantNeZero` — that is the known `def … : Prop` type-only blind
spot, not an identity; the checker's `--prop-bodies` pass is the instrument, and none of the
three exists anywhere in the port (grep-verified, with the `kw_` prefix stripped as well).

Regions, with dispositions (the `S_` line numbers of each file):

| lines | contents | disposition |
|---|---|---|
| 978 `:1–147` | `kw_toPoint_add`, `kw_isUniformization`, the `PeriodPair` prelude | **ported** (`Uniformization.lean`, `Basic.lean`); import |
| 978 `:148–302` | `divNHom`/`divNHom_smul`, `latticeDivQuot`/`_surjective`, `mem_ker_latticeDivQuot`, `ker_latticeDivQuot`, `latticeQuotTorsionEquiv`, `card_torsionBy_latticeQuotient` | **shared with 2021 `:943–1101`** — one home |
| 978 `:303–371` | `kw_toPointHom`, `kw_toPointHom_apply`, `kw_ker_toPointHom` | **ported promotions** (`Uniformization.lean`); import |
| 978 `:372–451` | `mulLeftR`/`mulLeftZ`, `scale_lattice`, `mem_scale_lattice_iff`, `gate_scale_mul` | `scale_lattice`/`scaleLatticeEquiv` **ported public** (import); `mulLeftR`/`mulLeftZ`/`mem_scale_lattice_iff` port-**`private`** (re-derive `private`); `gate_scale_mul` **absent** — shared with 2021 `:727`, write once |
| 978 `:452` | `kw_zlatticeQuotientTorsionCountBridge_axiomAnchor : True` | **skip** (p2m anchor stub) |
| 978 `:483–592` | `kwLatticeCoeAddEquiv`, `kw_card_torsionBy_zlatticeQuotient`, `…_finrank_real`, `kw_scale_lattice_toAddSubgroup`, `kwSublatticeIndex_scale` | **new + shared with 2021 `:883–921`** |
| 978 `:593–639` | `KwD5BetweenCurvesIndexDual` | **new class** |
| 978 `:640–965` | the `hID_*` block (`kerIndexHom`, `scale_subset`, `kerIndexHom_surjective`, `ker_kerIndexHom`, `forwardIndex_eq_card_ker`, `card_smul_subset`, `dualUnit`, `dual_subset`, `sublatticeIndex_congr_snd`, `scaleIndexHom`, `sublatticeIndex_scale_nat`, `card_ker_pos`, `dualIndex_eq`) and `…betweenCurvesIndexDual_proved` | **new; shipped twice** — write once here, 2021 `:1316–1580` is the copy |
| 978 `:966–978` | `solution` | the 978 headline, ~13 lines |
| 2021 `:52–799` | the place dictionary, `normFormulaAlong_of_elliptic`, the `PeriodPair` prelude, `KwD5BetweenCurvesHoloLift` | **ported** (`Dictionary.lean`, `Engine.lean`, `PeriodPair/*`, D-5's class); import |
| 2021 `:923–942` | `MilneI72IntersectionData` (a `structure` with fields and **no uses anywhere**) | **skip** — verify with `grep -n MilneI72` before dropping |
| 2021 `:1103–1272` | `KwD5BetweenCurvesIndexDual` (44), `kwLatticeCoeAddEquiv`, `kw_card_torsionBy_zlatticeQuotient*`, `KwD5BetweenCurvesPointHomSublatticeCyclic` (1242), `KwD5BetweenCurvesKerQuotEquivBC` (1259) | **new classes** |
| 2021 `:1273–1315` | `kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three` | **new** — 3-line assembly |
| 2021 `:1316–1580` | the `hID_*` block | **duplicate of 978 `:640–941`** — port once |
| 2021 `:1581–1990` | the `kqe_*` block (`map_fst`, `map_snd`, `map_eq`, `negSwap_mem_ker`, `addOrderOf_negSwap`, `lcm_addOrderOf_eq`, `card_ker`, `isAddCyclic_ker_of_surjective{,′}`, `toZModSq*`, `zmodSqEquiv`, `forwardEquiv`, `alpha_mem`, `Psi`, `ker_Psi`, `Nu_le_alpha`, `Phi'*`, `Phi'_comp_Psi`) and `kw_surgehgf4_kqe_proved` | **new — this set's core** |
| 2021 `:1991–2021` | `solution` | the 2021 headline, ~30 lines |

## 3. The mathematics, and the direction of the chain

1. **The torsion prelude** (`divNHom`/`latticeDivQuot`/`latticeQuotTorsionEquiv`/
   `card_torsionBy_latticeQuotient`): the `n`-torsion of `Λ'/nΛ` is `Λ'/nΛ' ≅ (ZMod n)²`; the
   pin proves `Nat.card` of it by `Mod_n`/`finrank` arithmetic. **Audit this block against
   mathlib's `ZLattice`/`ModN` first** (§5): `card_torsionBy_latticeQuotient` is the one place
   a mathlib call may replace a transcription.
2. **The `hID_*` block** (one home): `kerIndexHom : L'.lattice.toAddSubgroup →+ ψ.ker`,
   `forwardIndex_eq_card_ker`, `card_smul_subset`; then the **dual homothety**
   `dualUnit : ℂˣ` with `dual_subset` (the inclusion) and `dualIndex_eq`
   (`sublatticeIndex L (L'.scale β) = Nat.card ψ.ker`), assembled by
   `kw_surgehgf4_hID_betweenCurvesIndexDual_proved`. This is elementary ℤ-lattice arithmetic
   over the pin's `sublatticeIndex`/`sublatticeQuotient`; mathlib has the index/covolume API
   (§5) but **not** the pin's `dualUnit` construction.
3. **The `kqe_*` block** (2021 only): the kernel-quotient engine. `ψ.ker` is a finite
   subgroup of `E'(ℂ)`; the block builds `ψ.ker ≅ ZMod N × ZMod N` from `hcard` and the
   `IsAddCyclic` hypothesis, transports along `sublatticeQuotient`, and produces the `β` whose
   quotient is cyclic — `KwD5BetweenCurvesKerQuotEquivBC`, proved by
   `kw_surgehgf4_kqe_proved`. This is the set's genuinely new algebra; the scoping note's
   audit found **no** mathlib product-cyclicity or HNF-coprimality criterion to lean on.
4. **The assembly** `kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three`:
   `hH2 → hID → hKQE → KwD5BetweenCurvesPointHomSublatticeCyclic`, and the two headlines fall
   out (the 2021 `solution`; the 978 `solution` is `hID_betweenCurvesIndexDual_proved` at the
   restated `toPointHom` hypothesis, after setting `IsElliptic` from `discriminant_ne_zero`).

A `def … : Prop` is never dropped on a tool's word (P-2 §6): the three classes are all
load-bearing, and `grep -c` each body.

## 4. Deliverable

**`FLTForHuman/Elliptic/PeriodPair/LatticeIndex.lean`** (new leaf), one module for the two
nodes. Namespaces as the pin: the torsion/index/`kwLattice*`/headlines in `PeriodPair`, the
three classes and the `hID_*`/`kqe_*`/`hscd_*` chain in `ModularCurve`.

- **Public, at the pin names** (the checker diffs them): the two headlines; the three classes;
  the shared `hID_*` block written **once**; the shared torsion prelude written **once**; the
  `kqe_*` block; `kwLatticeCoeAddEquiv`, `kw_card_torsionBy_zlatticeQuotient{,_finrank_real}`,
  `kw_scale_lattice_toAddSubgroup`, `kwSublatticeIndex_scale`,
  `kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three`, `kw_surgehgf4_kqe_proved`,
  `kw_surgehgf4_hID_betweenCurvesIndexDual_proved`, and the pin-public `divNHom*`/
  `latticeDivQuot*`/`latticeQuotTorsionEquiv`/`card_torsionBy_latticeQuotient`.
- **Not landed**: the ported prelude (import), `MilneI72IntersectionData` (unused), the
  `*_axiomAnchor : True` stubs, the `p2m_*` scaffolding, and the 2021 file's duplicate copies
  of the `hID_*`/torsion block.
- **`private` with content names**: helpers local to the module (the `mulLeftR`/`mulLeftZ`/
  `mem_scale_lattice_iff` layer if re-derived, the interior steps). A pin-`private` name stays
  private; a public statement must not name a private helper.
- Imports: `Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,HoloLift}`,
  `WeierstrassCurve/Isogeny/{ConditionalCurrency,KernelBaseChange}`,
  `WeierstrassCurve/IsogenyEndDatum/Engine`, `WeierstrassCurve/Place/Dictionary`, plus mathlib
  `Mathlib.Algebra.Module.ZLattice.{Basic,Covolume}`,
  `Mathlib.LinearAlgebra.FreeModule.{Finite.CardQuotient,ModN}`,
  `Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic` (and `Mathlib.Tactic`). Never `import
  Mathlib`. **Never** import `WeierstrassCurve/GenusOnePlaceGateCentred.lean` or
  `WeierstrassCurve/Place/RRSpace.lean` (the gate instances are `∀` binders here; the
  co-import collision with `Engine.lean` still holds — `Engine.instInfinitePlace` is
  `private` now, but the ban is the standing rule).
- The 2,021 file's `solution` uses S-1's headline to rebuild `hH2`; **use the ported
  `ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift` instead**, and
  `ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved` for `hID` (both declared in
  this set / S-1).

## 5. Route, with recorded negatives

- **The mathlib lattice API is present and audited** (all `v4.34.0`):
  `ZLattice.module_free` / `ZLattice.module_finite` (`Algebra/Module/ZLattice/Basic.lean:509,
  485`), `ZLattice.rank` (`:522`, `finrank ℤ L = finrank K E`),
  `ZLattice.covolume` + `covolume_div_covolume_eq_relIndex`
  (`Algebra/Module/ZLattice/Covolume.lean:148`), `ModN.natCard_eq`
  (`LinearAlgebra/FreeModule/ModN.lean:106`), and
  `AddSubgroup.index_eq_natAbs_det` / `relIndex_eq_natAbs_det` / `relIndex_eq_abs_det`
  (`LinearAlgebra/FreeModule/Finite/CardQuotient.lean:98,106,114`). `PeriodPair` carries
  `IsZLattice ℝ L.lattice` from mathlib itself, so every `[IsZLattice ℝ L]` lemma applies to
  `L.lattice` directly, and `L.lattice` carries `DiscreteTopology`. **Use these on the torsion
  and index steps where they shorten the pin**; audit `card_torsionBy_latticeQuotient` and
  `kw_card_torsionBy_zlatticeQuotient_finrank_real` before transcribing.
- **Recorded negatives.** mathlib has **no** product-cyclicity criterion and no
  HNF/`gcd`-coprimality criterion for `IsAddCyclic`, and no `sublatticeIndex`-as-covolume
  bridge for the pin's `dualUnit`; the `kqe_*` block and `dualUnit`/`dual_subset` are written
  as the pin has them. `ZLattice` also does not supply the pin's `divNHom` packaging.
- **Reuse wins, and what is *not* reusable.** The 68 substitutions are imported, not
  re-proved; the **public** port vocabulary is `PeriodPair.{scale,scale_lattice,
  scaleLatticeEquiv,sublatticeIndex,sublatticeQuotient}` and the `kw_toPointHom` promotion set
  (`Uniformization.lean`). The following are **absent** from the port and belong to this module:
  `gate_scale_mul`, `kwSublatticeIndex_scale`, `kw_scale_lattice_toAddSubgroup`,
  `kwLatticeCoeAddEquiv`, the torsion prelude, the `hID_*` block and the `kqe_*` block.
  `mem_scale_lattice_iff` and `mulLeftR`/`mulLeftZ` exist **only as `private`** in
  `PeriodPair/Lattice.lean` (not importable): re-derive them `private`, as the S-1 worker
  re-derived `countable_lattice`. Verified with `port_advise` on the landed tree.
- **Ported prelude, not re-proved.** The place dictionary, `normFormulaAlong_of_elliptic`,
  `pointEnd'`, the `PeriodPair` scale/`jLattice` block and the `toPointHom` promotion set are
  all in the port; do not transcribe them.
- **The pin's `attribute [-instance]`/`attribute [-simp]` blocks and its
  `set_option maxHeartbeats 6400000` / `synthInstance.maxHeartbeats 8000000` on the `kqe`
  region are not transcribed.** The port's cap is 4,000,000; **never raise it**. If a
  declaration cannot fit, stop and report.
- **The `Polynomial.Bivariate` `scoped notation "Y"` trap**: do not open that scope file-wide
  (playbook §6). Write prose in `/- … -/` blocks, not `--` lines (playbook §4's
  namespace-tracker quirk).
- **Dedup discipline.** Write the shared `hID_*` block and the torsion prelude exactly once,
  in this module; the 2021 file's copies are not transcribed. `grep -c` every declaration
  dropped as already-present, with the reason.

## 6. Stop conditions

Stop and report, do not push on: an unported prerequisite outside §2 that is not the ported
prelude; a statement that does not transcribe to `v4.34.0`; a declaration that will not fit
the 4,000,000-heartbeat cap; any pull toward S-3/S-4 or the capstone; any pressure to import
the two forbidden modules. Keep the tree green: a blocked region goes to a `Scratch` probe and
a written report, not a forced transcription.

## 7. Build discipline (binding) and pre-flight

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop;
> `lake build <module>` when a file is done; **one** `lake build` per wave; bound every build
> with `timeout` and serialize every `lake build` with `flock .lake/flt_build.lock`; time it
> (high user CPU + timeout is a real blow-up, ~0 CPU is contention). **Never raise
> `maxHeartbeats`.** Iterate in a gitignored `lean/Scratch*.lean`, in bounded blocks; split
> the module by region (`torsion → hID → IndexDual → kqe → headlines`) so a hard core does not
> make every check cost minutes.

**Pre-flight, before writing anything** (report the numbers):

1. `timeout 300 lake env lean <opts>` on a stub importing the five `Elliptic/PeriodPair`
   modules + `KernelBaseChange` + `Engine`, timed.
2. `#check` the exact signatures of `ModN.natCard_eq`, `ZLattice.covolume`,
   `covolume_div_covolume_eq_relIndex`, `ZLattice.rank`, `ZLattice.module_free`,
   `AddSubgroup.relIndex_eq_natAbs_det`, and the ported
   `PeriodPair.{sublatticeIndex,sublatticeQuotient,scale_lattice,ker_toPointHom}`,
   `ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift`.
3. A `Scratch.lean` probe of the pin's `card_torsionBy_latticeQuotient` route against
   `ModN`/`finrank` on one concrete `Λ` — the one place mathlib may collapse the block (§5).
   If it does, record the replacement and the measured saving; if it does not, say so and
   transcribe.
4. `port_advise --targets build/rowS2_targets.txt` against the *landed* tree, and report the
   substitution/once figures as re-measured (S-1 changed the corpus).

## 8. Verification

- `lake env lean` clean; `lake build FLTForHuman.Elliptic.PeriodPair.LatticeIndex`; one
  `flock`ed wave build; whole-tree `lake build` green.
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. Baseline at drafting
  (after S-1 landed): `6074 statements identical (313 promoted from pin-private declarations,
  83 renamed), 0 mismatched, 0 missing, 36 own-proof declarations exempted (6110 port
  declarations checked)`. **Re-run it at dispatch.** Reconcile every delta: the set adds the
  two headlines and the pin-public block as `identical`, plus any promotion as `renamed`.
- `SOURCES`: append, in this order, the two `Theorems/` wrappers and their `S_` files —
  `Thm_…natCard_ker`, `S_…natCard_ker`, `Thm_…isAddCyclic_sublatticeQuotient`,
  `S_…isAddCyclic_sublatticeQuotient` — each wrapper **before** its `S_` file (the wrapper is
  the statement authority; the `S_` file declares only `solution`). None of the four is in the
  list today. Confirm with a checker run before and after each insertion and report both
  lines. `PORT_FILES`: append `FLTForHuman/Elliptic/PeriodPair/LatticeIndex.lean` last (after
  `HoloLift.lean`).
- `spec/PeriodPairLatticeIndexConsumer.lean` (new, `spec/` only): real executed cross-module
  zones, no `#check`, no `sorry`; deleting the module must make it fail; exit 0. Model it on
  `spec/PeriodPairHoloLiftConsumer.lean` (the S-1 probe). At least one zone must apply one
  headline at a **concrete** `PeriodPair.ofTau`-style lattice (gate instances as hypotheses),
  one must compose it with the ported `toPointHom_apply` / `sublatticeIndex` API, and one must
  consume the S-1 → S-2 hand-off (`kw_surgehgf4_hH2f_betweenCurvesHoloLift` feeding the 2021
  route). Run it with `timeout 90 lake env lean <opts>`, report exit and wall time; do not add
  it to the lakefile.
- `#print axioms` on both headlines, on the three classes and on `kw_surgehgf4_kqe_proved`:
  `[propext, Classical.choice, Quot.sound]`; no `sorry` (`grep -c` it).
- `build_ladder.py --edit FLTForHuman/Elliptic/PeriodPair/LatticeIndex.lean` — report the
  cascade (S-1 was 0 modules; this one may have dependents in the row).

## 9. Close-out (fill on landing)

Written lines; the once-only blocks with their `grep -c`; checker before → after and the
reconciliation; the measured saving against the 2,999 raw pin lines (68 substitutions ≈868,
41 names ≈768 once-only, and what was actually written); the consumer exit and time;
whole-tree build jobs and seconds; `#print axioms`; the friction findings — in particular
whether the `card_torsionBy_latticeQuotient`/`kw_card_torsionBy_zlatticeQuotient_finrank_real`
block shortened against `ZLattice`/`ModN`, and how much of the `kqe_*` block is the pin's.
Then update `TOPIC-V5-row-S-scoping.md` §2.2/§5 (close the answered questions) and fold the
generalizable part into [../../porting-playbook.md](../../porting-playbook.md) and
[../../logs/velu-port.md](../../logs/velu-port.md).

### Landed 2026-10-07 — the close-out

**`FLTForHuman/Elliptic/PeriodPair/LatticeIndex.lean`, 1,249 lines** (61 checker-visible public
declarations + 4 `scoped instance` + 7 `private` helpers), plus
`spec/PeriodPairLatticeIndexConsumer.lean` (five zones / eleven `example`s). The full record is
in [../../logs/velu-port.md](../../logs/velu-port.md) "S-2 — the lattice/index arithmetic"; the
numbers:

- **Saving.** 2,999 raw pin lines (978 + 2,021). `port_advise` re-measured on the landed tree:
  **68 substitutions ≈ 868 lines** and **41 names proved in both target files ≈ 768 once-only
  lines** — exactly the order's figures. **1,249 lines written** (inside the 1,000–1,200
  estimate plus the ~55-line header), i.e. ≈1,750 pin lines never transcribed. The two
  once-only blocks are the torsion prelude (`divNHom` … `card_torsionBy_latticeQuotient`,
  ≈120 lines, `grep -c` on the two pin files: 2) and the `hID_*` block
  (`kerIndexHom` … `dualIndex_eq` + `…betweenCurvesIndexDual_proved`, ≈250 lines, `grep -c`: 2).
- **Checker.** before `6074 (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
  (6110 checked)` → after `6135 (312, 83), 0 mismatched, 0 missing, 36 own (6171 checked)`.
  The delta reconciles exactly: **+61 `identical` = the 61 public declarations** the checker
  sees in the module (the two headlines, the three classes, the shared `hID_*`/torsion/`kqe_*`
  blocks, `gate_scale_mul`, `kwSublatticeIndex_scale`, …); `renamed`/`own`/`mismatched`/`missing`
  unmoved; and **`promoted` 313 → 312** is a route change, not a loss — `PeriodPair.scale_lattice`
  (in `Lattice.lean`) no longer needs the pin-`private` fallback because the newly-added 978
  `S_` source carries a pin-*public* `scale_lattice`, so it is still `identical`, only counted
  in the public bucket. Measured by toggling only the new `SOURCES` entries.
- **`--prop-bodies`**: 261 identical / 6 textual (was 258 / 6). **+3 = the three classes**,
  all in the identical set; the 6 textual are the pre-existing advisory rows
  (`IsEichlerIntegral`, two `Velu/Discharge`, two `Isogeny/BaseChange`, `KernelCyclicTransfer`),
  none S-2. The 978-flavour `KwD5BetweenCurvesIndexDual` body matches the 978 copy (the 2,021
  copy differs only by unused gate-instance binders).
- **Consumer.** exit 0, wall **55.8 s** (`timeout 90 lake env lean …`); zone 1 the 2,021
  headline at `PeriodPair.ofTau`, zone 2 the 978 headline composed with
  `toPointHom_apply`/`ker_toPointHom`/`sublatticeIndex`, zone 3 the S-1 → S-2 hand-off
  (`kw_surgehgf4_hH2f_betweenCurvesHoloLift` feeding `…hscd…_of_three`), zone 4 the torsion
  count and the index/scale laws. Removing the module source **and** its `.olean` gives exit 1
  (`object file … does not exist`).
- **Axioms.** `#print axioms` on both headlines, the three classes and `kw_surgehgf4_kqe_proved`:
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- **Builds.** edit-loop `lake env lean` (clean run) 76.5 s wall / 18.3 user / 20.8 sys
  (the stub importing the whole PeriodPair + `KernelBaseChange` + `Engine` stack is ~108 s, so
  the loop is import-dominated); module `lake build` 94 s (9,039 jobs), 109.6 s wall, flocked
  `timeout 300`; `build_ladder --edit` prices the cascade at **0** dependent modules (a leaf);
  whole-tree flocked `lake build` green, 9,321 jobs, 12.63 s wall / 9.36 user / 13.90 sys.
- **Friction.** `card_torsionBy_latticeQuotient` did **not** shorten against `ZLattice`/`ModN`:
  `ModN.natCard_eq` is exactly the pin's last step, the `Λ'/nΛ' ≅ (ZMod n)²` packaging
  (`divNHom`/`latticeDivQuot`/`latticeQuotTorsionEquiv`) is not in `ZLattice`, and
  `kw_card_torsionBy_zlatticeQuotient_finrank_real` is the pin's three lines with
  `ZLattice.rank`; the block is transcribed once instead of twice (the audit's "one place
  mathlib may collapse it" answered **no**). The `kqe_*` block is the pin's, ~400 lines, minus
  the 10-line `kw_surgehgf4_kqe_axiomAnchor` and the `set_option` bumps: mathlib supplies the
  primitives, but the product-cyclicity criterion (`negSwap`, `lcm` of `addOrderOf`) is the
  pin's and has no mathlib replacement. `Uncountable ℝ` needed an extra specific mathlib
  import (`Analysis/Real/Cardinality.lean`). Five pin-`private` helpers the order classified as
  "ported prelude; import" were **not** in the port and were re-derived `private`:
  `exists_smul_mem_and_apply_eq_of_forall_sub_mem` (69 lines — `port_advise`'s one new drag),
  `apply_eq_apply_of_continuous_of_mapsTo_lattice` (9), `infinite_point`, `toPoint_add_mem`, and
  the `sub_fract_mem_lattice`/`apply_eq_apply_of_differentiable_of_forall_periodic` pair (the
  latter private in `Uniformization.lean`, not importable across the module boundary — the S-1
  finding recurs). `private` across namespaces needs `PeriodPair.foo L …`, not `L.foo`.
