# S-1 work order — the ℂ-analytic seam

**Status: drafted 2026-10-06, for dispatch once the P-3 (`D-6`) set is reviewed and landed.**
First set of row S (`topics/velu/TOPIC-V5-row-S-scoping.md`). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Depends only on already-landed
sets: P-SET-1/P-SET-2 (`Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,JLine}.lean`),
D-1 (`Isogeny/BaseChange.lean`), D-4/D-5 (`Isogeny/KernelCyclicTransfer.lean`,
`Isogeny/KernelBaseChange.lean`), and `Place/Dictionary.lean`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2, §2.1–§2.4, §3.1–§3.5, §4–§5.

## 1. Scope

Land the row's **ℂ-analytic seam**: given an integral, finite isogeny-direction map
`ι : L'.weierstrassCurve.FunctionField →ₐ[ℂ] L.weierstrassCurve.FunctionField` between the
function fields of two complex elliptic curves, there is a **differentiable** `F : ℂ → ℂ`
with `F 0 ∈ L'.lattice` and
`L'.toPoint hL' (F z) = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z)` for all `z`.

This is the analytic compatibility between the complex uniformization and the algebraic
pushforward: the isogeny descends to a holomorphic map of ℂ that intertwines the two ℘-maps.
It is the row's largest node (2,673 pin lines) and the only one whose subject is not the
pin's own lattice arithmetic.

**Not this set:** the lattice/index arithmetic (S-2: the 2,021 and 978 nodes and the
`KwD5BetweenCurves{IndexDual,KerQuotEquivBC,PointHomSublatticeCyclic}` classes), the
primitive-coset/`jLattice` column (S-3, the 848 node), the modular-polynomial tail (S-4), and
the capstone (SC). The three S-2 classes are **not** imports of this set and must not be
declared here. A worker who reaches an unported prerequisite stops at the boundary and
reports.

## 2. Source and the dedup

- `P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
  (2,673 lines, 133 declarations).
- Statement authority: `Theorems/Thm_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
  (41 lines). Spell its binders **exactly**; note that `hL : L.DiscriminantNeZero` and
  `hL' : L'.DiscriminantNeZero` are explicit **arguments**, not instances, and the conclusion
  is at `L'.toPoint hL'` / `L.toPoint hL`. The pin's `solution` (`:2658–2673`) is 16 lines.

Regions of the pin file, from the scoping note's §2.1:

| lines | contents | disposition |
|---|---|---|
| `:51–960` | the place dictionary and the `PeriodPair` prelude (`IsFinitePlace.*`, `placeOfEquation*`, `InfinitePlace.*`, `placeOfPoint_*`; `kw_discriminantNeZero`, `kw_isUniformization`, `kw_toPoint_add`, `sub_fract_mem_lattice`, `apply_eq_apply_of_differentiable_of_forall_periodic`, `gate_scale_mul`, `kw_countable_lattice`, `kw_toPointHom*`) | **ported** — `Place/Dictionary.lean`, `Elliptic/PeriodPair/*`; import |
| `:961–1111` | `KwD5BetweenCurvesHoloLift` | **D-5**, `KernelBaseChange.lean:89` — import the class, do **not** redeclare it (the module proves it) |
| `:1112–1189` | the covering-map layer: `kw_isDiscrete_lattice`, `kw_isCoveringMap_mk_lattice`, `kw_differentiable_of_locally_differentiable_lift_through_mk`, `kw_toPointHom_eq_toPointAddEquiv_mk` | **new** |
| `:1190–1523` | place algebra (`ord_div`, `mk_mem_XYIdeal_iff`, `ord_placeOfEquation_pos_iff`, `yGen`, `ord_sub_evalAt_pos`) and `Δ_ne_zero_of_isElliptic`, `placeOfPointEquiv`, `kw_surjective_toPointHom` | mostly **ported** (`Dictionary.lean`, `FunctionFieldQuadratic.lean`, `PlaceCalculus.lean`, `Engine.lean`); the tail from `placeOfPointEquiv` is **new** |
| `:1524–2657` | the chain: `KwD5BetweenCurves{LocallyHoloLift,CocountableHoloLift,CocountableAffineHoloCoords,CocountableAffineHoloCoordsWeak}`, `kw_surgehgf4_hH2*`, `kw_fdn2_qephod_hend10_*`, `kw_countable_toPointHom_preimage`, `kw_evalAt_placeOfEquation_mk`, `kw_differentiableOn_eval{,_Eval}_wp`, `mmr73_cs_*`, `kw_fdn2_qephod_hend7_geomMorphBC*` | **this set's content**; `mmr73_cs_evalAt_eq_of_ord_sub_pos` is already ported (`IsogenyEndDatum/Engine.lean`) and `kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub` should be audited against the D-5 import |
| `:2658–2673` | `solution` | the headline, 16 lines |

`port_advise` on the file: **78 substitutions, ≈1,203 lines** (the large homes are
`Place/Dictionary.lean` 316, `PeriodPair/Basic.lean` 201, `Engine.lean` 189,
`PlaceCalculus.lean` 112, `Uniformization.lean` 105, `FunctionFieldQuadratic.lean` 86,
`NatCard.lean` 69, `Lattice.lean` 65). Content: 1,490 lines. **Working estimate ≈1,300–1,400
written lines.** Re-price after the pre-flight (§7).

## 3. The mathematics, and the direction of the chain

The pin reduces the headline through four `Prop`s. The **implication direction** is
`Weak → Coords → Cocountable → Locally → HoloLift`, where `Weak` is the constructive base and
each step removes a defect:

1. **`KwD5BetweenCurvesCocountableAffineHoloCoordsWeak`** (constructive, `:2436–2638`, 203
   lines) — off a countable set `S`, each `z₀` has a neighbourhood `U` and differentiable
   `X, Y : ℂ → ℂ` with `pmop (L.toPointHom z) = Point.some (X z) (Y z) h` on `U`. This is where
   the analytic work is: lift locally through the quotient `ℂ → ℂ/Λ`, using
   `kw_isCoveringMap_mk_lattice` and the ℘-differentiability.
2. **Weak ⟹ Coords** (`kw_surgehgf4_hH2e_…_of_weak`, `:2244`) — recover `Y z ≠ 0` off a
   countable set, using the finiteness of `ker (pointMapOfPushforward …)`
   (`kw_fdn2_qephod_hend10_kerPMOP_finite`, `:2048`) and `L'.kw_surjective_toPointHom`
   (`:1492`).
3. **Coords ⟹ Cocountable** (`kw_surgehgf4_hH2d_…_of_affineHoloCoords`, `:2125`) — turn the
   differentiable coordinates into a differentiable lift `G` through `L'.toPointHom`.
4. **Cocountable ⟹ Locally** (`kw_surgehgf4_hH2c_…_of_cocountable`, `:1964`) — `ℂ` minus a
   countable set is path-connected (mathlib's
   `isPathConnected_compl_of_one_lt_rank` + `rank_real_complex`), so move a good point to any
   `z₀`; `kw_countable_toPointHom_preimage` (`:1903`) transports along the lattice.
5. **Locally ⟹ `KwD5BetweenCurvesHoloLift`** (`kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo`,
   `:1535`) — glue the local lifts into one global differentiable `F`
   (`kw_surgehgf4_hH2f_betweenCurvesHoloLift`, `:2639`, is the 2-line assembly).
6. **The headline** (`solution`, `:2658`) — `KwD5BetweenCurvesHoloLift` is stated with
   `toPointHom`; rewrite both occurrences to `toPoint` by the ported
   `PeriodPair.toPointHom_apply` (pin `kw_toPointHom_apply`), and add the `hN` argument.

A `def … : Prop` is never dropped on a tool's word (P-2 §6): the four classes are all
load-bearing and none is a restatement of another — `grep -c` the body of each.

## 4. Deliverable

**`FLTForHuman/Elliptic/PeriodPair/HoloLift.lean`** (new leaf). The four `Prop`s and the five
chain lemmas at their pin names, in `ModularCurve` (the pin's namespace), plus the headline at
the wrapper's statement in `PeriodPair`.

- The four classes stay at the pin names
  (`ModularCurve.KwD5BetweenCurves{LocallyHoloLift,CocountableHoloLift,CocountableAffineHoloCoords,CocountableAffineHoloCoordsWeak}`)
  — they are pin-public and the checker diffs them against the `S_` file;
- the chain lemmas keep their pin names including the `kw_surgehgf4_hH2*` / `kw_fdn2_*` prefixes:
  they are pin-public transcriptions, and per playbook §5 a transcription keeps its name (the
  `kw_` prefix rule is about *promotions*). What this set **promotes** is anything it takes
  public out of `Elliptic/PeriodPair/*`'s private layer, at the prefix-stripped pin name, as a
  `RENAMED` row;
- `KwD5BetweenCurvesHoloLift` is **imported** from `KernelBaseChange.lean`, never redeclared;
- helpers local to the module are `private` with content names.

Imports: `Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization}`,
`WeierstrassCurve/Isogeny/ConditionalCurrency` (`pointMapOfPushforward`),
`WeierstrassCurve/Isogeny/KernelBaseChange` (the landed class),
`WeierstrassCurve/IsogenyEndDatum/Engine` (`mmr73_cs_*`), `WeierstrassCurve/Place/Dictionary`,
`AlgebraicCurve/*` specifics, and from mathlib
`Mathlib.Topology.Homotopy.Lifting` (the lifting theorem),
`Mathlib.Topology.Covering.AddCircle` (`AddSubgroup.isAddQuotientCoveringMap_of_comm`, §5),
`Mathlib.Analysis.Normed.Module.Connected` (`Set.Countable.isPathConnected_compl_of_one_lt_rank`),
`Mathlib.LinearAlgebra.Complex.FiniteDimensional` (`Complex.rank_real_complex`),
`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` (℘-differentiability, and the
`DiscreteTopology L.lattice` / `IsZLattice` instances, §5). Never
`import Mathlib`.

**Never import** `WeierstrassCurve/GenusOnePlaceGateCentred.lean` or
`WeierstrassCurve/Place/RRSpace.lean`: this module reaches `IsogenyEndDatum/Engine.lean`
through D-5, and `RRSpace`'s `scoped instance instInfinitePlace` collides with `Engine`'s at
the name level. The four classes quantify their gate instances as binders, so no global gate
device is needed — do not reintroduce one.

## 5. Route, with recorded negatives

- **The lift is mathlib's, the differentiability is the pin's.**
  `existsUnique_continuousMap_lifts` exists (`Mathlib/Topology/Homotopy/Lifting.lean`), as do
  `differentiableOn_weierstrassP` / `analyticOnNhd_weierstrassP`
  (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`) — so steps 1 and 5 rest on
  mathlib where the theory allows. But mathlib has **no** `IsCoveringMap.differentiableAt` and
  no covering-map differentiability lemma at all, so
  `kw_differentiable_of_locally_differentiable_lift_through_mk` stays the pin's own argument.
  Do not spend budget looking for a mathlib replacement for it.
- **The covering-map layer is short and its topological foundation is mathlib's — measured
  after this order's first draft, so the earlier "one genuine unknown" label is withdrawn.**
  Neither `kw_isDiscrete_lattice` nor `kw_isCoveringMap_mk_lattice` exists in the port (checked
  with the `kw_` stripped as well; the pin-name check alone is meaningless, since the port
  strips the prefix on promotion), but all four declarations of `:1112–1189` are small and
  three are effectively mathlib lookups:
  - `kw_isDiscrete_lattice` is `isDiscrete_iff_discreteTopology` applied to
    **mathlib's own instance** `DiscreteTopology L.lattice`
    (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:118`);
  - `kw_isCoveringMap_mk_lattice` is `(AddSubgroup.isAddQuotientCoveringMap_of_comm
    L.lattice.toAddSubgroup ‹discrete›).isCoveringMap`
    (`Mathlib/Topology/Covering/AddCircle.lean:30`);
  - `kw_toPointHom_eq_toPointAddEquiv_mk` is `rfl`;
  - only `kw_differentiable_of_locally_differentiable_lift_through_mk` (≈30 lines) is real
    work, and it is `Metric.mem_nhds_iff` + `convex_ball`'s
    `IsPreconnected.constant_of_mapsTo` + `DifferentiableOn.add` — all mathlib.
  The pin's `kw_countable_lattice` (ported) and mathlib's `IsZLattice ℝ L.lattice`
  (`Weierstrass.lean:120`) are the surrounding vocabulary. Do not spend budget re-deriving
  any of it.
- **Reuse wins.** `Set.Countable.isPathConnected_compl_of_one_lt_rank`, `Complex.rank_real_complex`
  and `existsUnique_continuousMap_lifts` are mathlib;
  `mmr73_cs_evalAt_eq_of_ord_sub_pos` is already ported into `IsogenyEndDatum/Engine.lean`;
  and P-2e §1.5 promoted the pin's `PeriodPair.kw_{toPointHom,toPointHom_apply,ker_toPointHom,toPointAddEquiv,toPointAddEquiv_mk,discriminantNeZero}`
  into `Elliptic/PeriodPair/Uniformization.lean` **at the prefix-stripped names**
  (`PeriodPair.toPointHom`, `toPointHom_apply`, `ker_toPointHom`, `toPointAddEquiv`,
  `discriminantNeZero`) — import those spellings, not the `kw_` ones.
- **Ported prelude, not re-proved.** The `placeOfEquation`/`IsFinitePlace`/`InfinitePlace`/
  `pointEquivPlace` dictionary, the `PeriodPair` scale/`jLattice` block and
  `natCard_ker_pointMapOfPushforward_eq_finrankAlong` are all in the port (78 substitutions).
  Do not transcribe them.
- **The pin's `attribute [-instance]` / `attribute [-simp]` blocks are not transcribed**, and
  its `set_option maxHeartbeats 3200000` is below the port's frozen 4,000,000 cap — do not
  transcribe the bump either.
- **Recorded negatives.** No mathlib covering-map differentiability; no mathlib ℘-lift for an
  isogeny; the pin's `IsDomain`/tensor scoped instances in this region are D-1's business and
  are imported.

## 6. Stop conditions

Stop and report, do not push on: an unported prerequisite outside §2 that is not the ported
prelude; a statement that does not transcribe to `v4.34.0`; a declaration that will not fit
the 4,000,000-heartbeat cap; any pull toward S-2/S-3/S-4 or the capstone; and any pressure to
import the two forbidden modules.

## 7. Build discipline (binding) and pre-flight

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop (without
> the options the check runs at the default cap and lies about heavy modules);
> `lake build <module>` when a file is done; **one** `lake build` per wave; the full build at
> the milestone. Bound every build (`timeout 60`/`90`/`300`), serialize every `lake build` with
> `flock .lake/flt_build.lock`, and time it: high user CPU with a timeout is a real blow-up to
> bisect, ~0 CPU is contention. **Never raise `maxHeartbeats`.** Never `import Mathlib` in a
> library module. Iterate in a gitignored `Scratch.lean`, in bounded blocks.

**Pre-flight, before writing anything** (report the numbers):

1. `timeout 300 lake env lean <opts>` on a stub importing the four `Elliptic/PeriodPair`
   modules + `KernelBaseChange` + mathlib's lifting module, timed.
2. `#check @existsUnique_continuousMap_lifts` (**two** forms exist,
   `Topology/Homotopy/Lifting.lean:171` under `[PathConnectedSpace A]` and `:480` under
   `[SimplyConnectedSpace A]` — take the one the pin's lift needs, ℂ being simply connected),
   `#check @Set.Countable.isPathConnected_compl_of_one_lt_rank` (a **dot-notation lemma on
   `Set.Countable`**: the pin uses it as `hSc.isPathConnected_compl_of_one_lt_rank`),
   `#check @Complex.rank_real_complex` (the `rank` form, *not* `finrank_real_complex` — both
   exist in `v4.34`; the pin uses the `rank` one), `#check @PeriodPair.toPointHom_apply`,
   `#check @ModularCurve.KwD5BetweenCurvesHoloLift` — pin the names and signatures before
   writing against them.
3. The covering-map layer first, as a ten-minute confirmation rather than a kill-switch: a
   `Scratch.lean` probe that states the pin's `IsCoveringMap (QuotientAddGroup.mk
   (s := L.lattice.toAddSubgroup))` and gets it by the one-line
   `AddSubgroup.isAddQuotientCoveringMap_of_comm` route of §5. If it does **not** come out,
   stop and report — that would contradict the measurement in §5 and the rest of the chain
   rests on it.

## 8. Verification

- `lake env lean` clean; `lake build FLTForHuman.Elliptic.PeriodPair.HoloLift`; one `flock`ed
  wave build.
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. Baseline at drafting:
  `6037 statements identical (313 promoted from pin-private declarations, 67 renamed), 0
  mismatched, 0 missing, 36 own-proof declarations exempted (6073 port declarations checked)`
  — **re-run it at dispatch**: D-6 lands first and will move it. Reconcile every delta: the
  set adds the four classes, the five chain lemmas and the headline as `identical` (they are
  pin-public transcriptions), plus any promotion as `renamed`.
- `PORT_FILES`: append `FLTForHuman/Elliptic/PeriodPair/HoloLift.lean` (last, so no earlier
  last-name match can flip). `SOURCES`: the `S_` file is **already** there — P-2e §1.5 appended
  `P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
  for the `kw_toPointHom` promotion set, and at drafting it sits at
  `spec/check_flt_statements.py:2237`; the `Theorems/` wrapper is **not** in the list. The
  wrapper is this set's statement authority and the checker takes the first match, so the
  wrapper must come **before** its `S_` file: insert it immediately above line 2237 rather
  than appending it last. This is the one entry that is not appended, and it is safe because
  the wrapper carries exactly one declaration
  (`PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`), whose
  name is the same one the `S_` entry already serves — so no other row's lookup can move.
  Confirm with a checker run before and after the insertion and report both lines.
- A `spec/PeriodPairHoloLiftConsumer.lean` (new, `spec/` only) with real executed cross-module
  zones, no `#check`, no `sorry`; deleting the module must make it fail; exit 0. Model it on
  `spec/KernelBaseChangeConsumer.lean` (the D-5 set's probe, 159 lines, five zones), which is
  the closest precedent in this column: it runs its first zones at *concrete* `PeriodPair`s
  and states the headline zones in hypothesis form, keeping the named instances `private`
  inside the probe. It is the wire test for the seam, so at least one zone must apply the
  headline at a *concrete* `L, L'` reachable from ported material (a `PeriodPair.ofTau`-style
  lattice is the natural one), and one must compose the headline's `F` with the ported
  `PeriodPair.toPointHom_apply` / `toPoint` API. Where a concrete instantiation needs
  unported hypotheses, state the test in hypothesis form and keep the named instances
  `private` in the probe.
- `#print axioms` on the headline and on `kw_surgehgf4_hH2f_betweenCurvesHoloLift`:
  `[propext, Classical.choice, Quot.sound]`; no `sorry` (`#print axioms` cannot see a `sorry`
  inside a `def`).
- **Run the probe, don't build it.** `spec/` is outside every lake target (`lakefile.lean`
  declares only `lean_lib FLTForHuman` and `lean_lib Reserve`), and there is no runner or CI
  list that enumerates the consumers — deliberately, so a library's green/no-`sorry`/seconds-warm
  build stays meaningful. Check the probe with `timeout 90 lake env lean <opts>
  spec/PeriodPairHoloLiftConsumer.lean`, report its exit status and wall time, and cite it in
  the close-out; do **not** add it to the lakefile or try to `lake build` it as a module.
- `grep -c` of every declaration dropped as already-present, with the reason, in the log.
- Whole-tree `flock`ed `lake build`; jobs and seconds.

## 9. Close-out (fill on landing)

Written lines per module; the promotion set with its `grep -c`; checker before → after and the
reconciliation; the measured saving against the 2,673-line file (state both figures: raw, the
1,203 substituted lines, and what was actually written); the consumer exit and time;
whole-tree build jobs and seconds; `#print axioms`; the friction findings — in particular
whether `IsCoveringMap (ℂ → ℂ/Λ)` came out as the pin has it, how much of the chain mathlib
absorbed, and whether the `mmr73`/`geomMorphBC` blocks were importable or had to be written.
Then update `TOPIC-V5-row-S-scoping.md` §5 (close the answered questions) and fold the
generalizable part into [../../porting-playbook.md](../../porting-playbook.md) and
[../../logs/velu-port.md](../../logs/velu-port.md).
