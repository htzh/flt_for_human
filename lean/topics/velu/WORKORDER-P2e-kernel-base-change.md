# P-2e work order — the kernel base change, one home (D-5)

**Status: open, 2026-10-06.** Set D-5 of [WORKORDER-P2-basechange.md](WORKORDER-P2-basechange.md).
New-file-only, **two pin `S_` files become one module**. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Depends on D-1
(`BaseChange.lean`) and D-4 (`KernelCyclicTransfer.lean`, the seam home). Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.4, §3.1–§3.2, §3.5, §3.7, §4.

## 1. Scope

Port the two `IsAddCyclic`-kernel base-change headlines **as one module**:

```
WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom      (5,357)
WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward (5,338)
```

Given the cyclic isogeny kernel over the larger algebraically closed field, prove (i) it is
cyclic over the smaller one and (ii) the base-changed datum exists over the larger one, with
the same `Nat.card`.

This is the set the whole D row was scheduled around. The two pin `S_` files are
near-identical: **163 of their 176 declarations coincide (4,926 removable lines)**. Porting
them as two modules would re-ship every one of them; the deliverable is one module whose
public declarations serve both wrappers. `port_advise` on the pair reports
`once 5659 / inport 2552 / decls 163`.

**Not this set:** the shared `pointPullback`/tensor prelude and the `IsogenyEndDatum`
base-change block (D-1); the `kw_surgehgf4_pck*` conjugation block and the
`KwD5BetweenCurves` seam (D-4); the S row and `eval_modularPolynomial_…`.

## 2. Source (pin) and the dedup

- `P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean` (5,357)
- `P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean` (5,338)

Statements: the two `Theorems/Thm_WeierstrassCurve_Affine_…` wrappers — spell their binders
**exactly** (the `S_` files use `Type u` where the wrappers do, but the `solution` binder
order is not the wrapper's; the wrapper wins). Note the asymmetry: the `…of_baseChange_algHom`
wrapper quantifies `(R₀ : Type u)` with the algHom `χ` and the two isogenies `ι₁, ι₂`, and
concludes a conjunction; the `…exists_algHom_baseChange_…` wrapper quantifies
`(R₀ : Type)` and concludes an existential over `ι₁` and `∀ hN₁`.

Declaration groups (both files have the same skeleton; take the first copy of each shared
declaration, from whichever file, and record where the other lives):

| lines (siloBC) | contents | shared? |
|---:|---|---|
| 51–320 | `CoordinateRing.*`, `IsFinitePlace.*`, `placeOfEquation*`, `InfinitePlace.*`, `placeOfPoint_*` | mostly already ported (`Place/Dictionary.lean`); import |
| 327–340 | `nonempty_pointTorsionBy_zmod` (20) | shared, new |
| 355–400 | `normFormulaAlong_of_elliptic`, `IsogenyEndDatum.{normFormulaAlong_auto,pointEnd',pointEnd_eq_pointEnd',pointEnd'_apply,pointEnd'_eq_of_seam}` | ported (`IsogenyEndDatum/Engine.lean`); import |
| 429–520 | `AlgebraicCurve.Place.{ord_nonneg_of_mem,mem_of_ord_nonneg,mem_iff_ord_nonneg,min_ord_le_ord_le,isRational_of_deg_eq_one,evalAt_div,mem_restrictAlong_iff}` | ported (`Place/Dictionary.lean`, `AlgebraicCurve/Defs/*`); import |
| 535–605 | `isFinitePlace_of_mem`, `isRational_placeOfEquation`, `InfinitePlace.*` | ported; import |
| 613–660 | `kw_fdn2_qephod_hend7_pmopKerCard_proved` (28), `PeriodPair.{kw_discriminantNeZero,kw_isUniformization,kw_toPoint_add,kw_toPoint_surjective,kw_toPoint_eq_zero_iff}` | shared, new (the `PeriodPair` ones are `private` in the port: promote — see P-2 §2) |
| 666–800 | `PeriodPair.{sub_fract_mem_lattice,apply_eq_apply_of_differentiable_of_forall_periodic,toPoint_add_mem,toPoint_neg,apply_eq_apply_of_continuous_of_mapsTo_lattice,exists_smul_mem_and_apply_eq_of_forall_sub_mem}` | shared/promote |
| 806–910 | `PeriodPair.{mulLeftR,mulLeftZ,scale_lattice,mem_scale_lattice_iff,scaleLatticeEquiv,G_scale,g₂_scale,g₃_scale,discriminant_scale,g₂_cubed_scale,jLattice_scale,discriminantNeZero_scale_iff,G_eq_of_lattice_eq,g₂_eq_of_lattice_eq,g₃_eq_of_lattice_eq,jLattice_eq_of_lattice_eq,latticeEquivOfEq}` | ported/promote (`Lattice.lean`, `Discriminant.lean`); import |
| 912–975 | `PeriodPair.{gate_scale_mul,kw_countable_lattice,kw_toPointHom,kw_toPointHom_apply,kw_ker_toPointHom,kw_toPointAddEquiv,kw_toPointAddEquiv_mk}` | shared, new + promote |
| 979–1345 | the `p2m_*` scaffolding and `export` blocks | **not transcribed** |
| 3289–3940 | `pointPullback*`, tensor `General` block, `kw_functionFieldTensorIsDomain_dischargeGeneral` | **D-1** — import |
| 3405–3540 | tensor `NoAC` block | **D-1** — import |
| 4038 | `KwD5BetweenCurvesFFSeamBaseChange` (59) | D-4 seam home — import |
| 4097–5300 | `kw_surge_hgf4_bcTensorIota*`, `bcTensorFracIota*`, `bcIota₁*`, `χE_VSR_compat` (274), `pmop_naturality` (249), `bcTensorFracIotaSeam` (167), `hBC_proved` (104) | shared, new — **this is the set's core** |
| 5141 | `KwD5BetweenCurvesKerTransportAlongEmbed` (58) | D-4 seam home — import |
| 5199–5300 | `kw_surgehgf4_hfgkd_ktd_{axiomAnchor,chiNoAC_eq_chiGeneral,kerTransport_proved}`, `kerTransport_s17`, `hBC_s17` | shared, new |
| 5309–5357 | `hBC_s17`, `kerTransport_s17`, `solution` | the two headlines’ assembly |

The only **node-unique** declarations are the two `solution`s and the binder differences
(`Type u` vs `Type`); `port_advise` reports 0 unique-new for either file.

## 3. Deliverable

**`FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean`** (new). Both headlines at
their wrapper statements, in `WeierstrassCurve.Affine`; the 87 shared declarations written
**once**, at the pin names and namespaces, public where the pin is public; helpers local to
the module `private` with content names (**no `kw_` prefix**). Imports D-1 and D-4, plus the
ported `Place/Dictionary.lean`, `IsogenyEndDatum/Engine.lean`, `Isogeny/NatCard.lean`,
`Elliptic/PeriodPair/` material and specifics from mathlib.

## 4. Route, with recorded negatives

- **One home, two headlines.** Do not create two modules and do not specialise the shared
  declarations to one headline. The `hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x)` commuting square is
  the bridge; both headlines consume the same `KwD5BetweenCurves*` seam and the same
  `kw_surge_hgf4_bc*` tensor transport.
- **The `χ`/`χ'` transport is the mathematical content.** The proof builds the base-changed
  isogeny `ι₁` from `ι₂` along the algHom `χ`, transports the kernel, and counts it with
  `natCard_ker_pointMapOfPushforward_eq_finrankAlong` (ported). Follow the pin's order.
- **`type u` vs `type 0`.** The `…of_baseChange_algHom` file uses `Type u` throughout and its
  `kerTransport_s17` is universe-polymorphic (`.{u_kt}`); the `…exists_…` file uses `Type`.
  Keep the pin's universe spelling per declaration — this is a real binder difference, not
  noise (the checker sees it).
- **A `def … : Prop` is never dropped on the tool's word** (see P-2 §6).
- **The seam is D-4's.** `KwD5BetweenCurvesHoloLift` (748), `…FFSeamBaseChange`,
  `…KerTransportAlongEmbed`, `pointEnd'_eq_of_seam` must already be in
  `KernelCyclicTransfer.lean`; import them. If they are missing, stop and report.
- **`IsogenyEndDatum/Engine.lean` is importable here** (`restrictAlong_eq_infinitePlace`,
  `pointEnd'_eq_of_seam`, `normFormulaAlong_of_elliptic`). Do **not** import
  `WeierstrassCurve/GenusOnePlaceGateCentred.lean` or `WeierstrassCurve/Place/RRSpace.lean`:
  `RRSpace`'s `scoped instance instInfinitePlace` collides at the name level with
  `Engine`'s `instInfinitePlace`. The gate classes come from `GenusOnePlaceGate.lean`.
  See P-2 §3.1 and `CARRY-FORWARD.md`.

## 5. Bound and stop conditions

Stop and report: an unported prerequisite outside §2 that is not D-1/D-4; a statement that
does not transcribe to `v4.34.0`; a universe/binder difference you cannot keep; any pull
toward the S row.

## 6. Build discipline (binding)

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop;
> `lake build <module>` when done; **one** `lake build` per wave, `flock`ed on
> `.lake/flt_build.lock`, bounded (`timeout 60`/`90`/`300`), timed. Never raise
> `maxHeartbeats`. Iterate in bounded blocks.

This is the heaviest module of the column and it imports the `LevelField`/`WeightOne` and
`IsogenyEndDatum/Engine` oleans. **Time the first `lake env lean` on a stub before writing**
and report it. The pin raises `maxHeartbeats` to 25,600,000; the port's frozen cap is
4,000,000 — if a declaration blows it, restructure (explicit instances, `have` chain) and
report which one.

## 7. Verification

- `lake env lean` clean; `lake build FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange`.
- Append the module to `PORT_FILES` (last). Append the two wrappers and the two `S_` files to
  `SOURCES` (last, wrapper before its `S_` file) — unless D-1/D-4 already did.
- `python3 spec/check_flt_statements.py` → 0 mismatched / 0 missing. Reconcile the delta
  against §2 and **report the duplicate-line saving**: the two `S_` files are 10,695 raw
  lines; the module should be about 2,300 new lines. Give both numbers.
- A `spec/` zone with both headlines at a concrete `R₀, E₀, E₀'` from ported material, or a
  hypothesis-form test if the concrete instances need unported hypotheses; deleting the
  module must make it fail.
- `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- Whole-tree `flock`ed `lake build`; jobs + seconds. `grep -c` of every drop, in the log.
