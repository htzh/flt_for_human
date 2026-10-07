# P-2e work order — the kernel base change, one home (D-5)

**Status: landed 2026-10-06.** Set D-5 of [WORKORDER-P2-basechange.md](WORKORDER-P2-basechange.md).
New-file-only except for one **small promotion set** (§2.0). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Depends on D-1
(`BaseChange.lean`, at its stripped names), D-2, D-3 and D-4 (`KernelCyclicTransfer.lean`).
Method: [../../porting-playbook.md](../../porting-playbook.md) §2.4, §3.1–§3.2, §3.5, §3.7, §4.

> **Amended 2026-10-06, after D-4 landed.** Two facts found by D-4 change this set:
>
> 1. **A missing promotion.** The seam `def KwD5BetweenCurvesHoloLift` is byte-identical in
>    all five pin copies (verified by `sha256`; the 748/151/83/25 spans are `p2m_*` span
>    artefacts), and its body mentions `PeriodPair.kw_toPointHom` — which the port has in
>    **no** form (`grep -c` = 0 for `kw_toPointHom`, `kw_toPointHom_apply`,
>    `kw_ker_toPointHom`, `kw_toPointAddEquiv`, `kw_toPointAddEquiv_mk`; the 9-line
>    `apply_eq_apply_of_continuous_of_mapsTo_lattice` is its other unported leaf). This is
>    **not** in the parent plan's 15 promotions. Port it first (§2.0) or the seam cannot be
>    declared. Registered in [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md).
> 2. **A name owned elsewhere.** `ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved` is
>    declared in two pin files with **different statements**; the name in the port belongs
>    to `Isogeny/NatCard.lean:785` (the `KwD5PointMapOfPushforwardKerCard` form), which is in
>    this set's cone. **Do not declare that name**; use the imported
>    `WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong`
>    (`IsogenyEndDatum/Vocabulary.lean`), which is the conj/S-row/silo form's content.
>
> Whole-row figures are unchanged: the two pin files are 5,357 / 5,338 lines and share
> **163 of their 176 declarations (4,926 removable lines)**; the pair's own new content is
> ~2,293 lines once, plus the seam. `port_advise` on the pair: `once 5659 / inport 2552 /
> decls 163`.

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

## 1.5 The prerequisite promotion set (do this first)

The seam `KwD5BetweenCurvesHoloLift`'s body mentions `PeriodPair.kw_toPointHom`, which the
pin declares **`private`** and re-exports with `p2m_export`:

```
S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean:909
  private def _root_.PeriodPair.kw_toPointHom : ℂ →+ (L.weierstrassCurve.toAffine).Point
:914  p2m_export "PeriodPair" "kw_toPointHom"
:915  private theorem _root_.PeriodPair.kw_toPointHom_apply (z : ℂ) :
        L.kw_toPointHom z = L.toPoint L.kw_discriminantNeZero z := rfl
```

It is a **promotion**, so it is written once, publicly, at the prefix-stripped pin name and
the checker verifies it through `stripped_source` (a `RENAMED` row). Port, in this order,
into `FLTForHuman/Elliptic/PeriodPair/Uniformization.lean` (public) — the seam here and the
S row's `exists_differentiable_toPoint_comp_…` both consume them:

| pin name | port name | pin site |
|---|---|---|
| `kw_toPointHom` (def, 6) | `PeriodPair.toPointHom` | `S_PeriodPair_exists_differentiable_toPoint_comp_…`:909 |
| `kw_toPointHom_apply` (5) | `PeriodPair.toPointHom_apply` | :915 (`rfl`) |
| `kw_ker_toPointHom` (10) | `PeriodPair.ker_toPointHom` | :919 |
| `kw_toPointAddEquiv` (5) | `PeriodPair.toPointAddEquiv` | :929 |
| `kw_toPointAddEquiv_mk` (4) | `PeriodPair.toPointAddEquiv_mk` | :935 |
| `apply_eq_apply_of_continuous_of_mapsTo_lattice` (9) | *keep the pin name* | :676 (in D-1's `BaseChange`? check; it is a `PeriodPair` helper) |

`kw_toPointAddEquiv` is the `ℂ ⧸ L.lattice.toAddSubgroup ≃+ E` packaging of P-SET-1's
`isUniformization_toPoint`; it can be built from the ported three conjuncts rather than
re-proved. `apply_eq_apply_of_continuous_of_mapsTo_lattice` has no `kw_` prefix — it is a
pin-`private` helper too, so promote it at its pin name (no strip) if a `RENAMED` row is not
wanted, or strip nothing because there is nothing to strip.

**SOURCES.** Add `P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
(last) so the checker can see these pin-private statements; append last so no earlier
last-name match can flip.

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
- **The seam is this set's.** `KwD5BetweenCurvesHoloLift` (11 lines; byte-identical in all
  five pin copies — the 748/151/83/25 spans are `p2m_*` artefacts), `…FFSeamBaseChange`,
  `…KerTransportAlongEmbed` are declared **here**, once, after the `§1.5` promotion set;
  `pointEnd'_eq_of_seam` is imported from `Engine.lean`. `KernelCyclicTransfer.lean` (D-4)
  deliberately does not declare `KwD5BetweenCurvesHoloLift`, so this module is its home and
  the S row will import it from here.
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

## 8. Close-out (landed 2026-10-06)

`FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean` (new, 1,377 lines: 1,340 Lean +
37-line header; **34 public / 0 private** — 32 checker-visible, the two
`scoped instance`s invisible to the parser) plus `spec/KernelBaseChangeConsumer.lean` (new,
159 lines, 5 zones, exit 0 in 1 m 14 s) and +50 lines in
`Elliptic/PeriodPair/Uniformization.lean` for the §1.5 promotion set.

- **Dedup, stated both ways**: the two pin files are **10,695 raw lines** and the module is
  **1,377**. `port_advise` scores 238 declarations (≈7,252 lines) as substitutions and 163
  names shared by both silos (≈4,926 removable lines); the module is the "once" side. The
  work order's "~2,300 once" counted ~950 lines of pin prelude copies that D-5's own content
  does not use and the port already owns — importing them is the dedup, not a gap.
- **Step 1**: six promotions into `Uniformization.lean`, all `RENAMED` —
  `PeriodPair.{toPointHom, toPointHom_apply, ker_toPointHom, toPointAddEquiv,
  toPointAddEquiv_mk}` plus `discriminantNeZero`, one more than §1.5's table because
  `toPointHom_apply`'s statement mentions it. `apply_eq_apply_of_continuous_of_mapsTo_lattice`
  was not promoted (no D-5 consumer). The S-row seam `S_` file was appended to `SOURCES`.
- **Checker**: `5999 (313 promoted, 61 renamed), 0/0, 36 own, 6035 checked` → `6005 (313, 67),
  0 missing, 6041` after Step 1 → **`6037 identical (313 promoted, 67 renamed), 0
  mismatched, 0 missing, 36 own, 6073 checked`**. +6 (promotions, all `renamed`) +32 (the
  module, all `identical`); nothing else moved.
- **One checker change**: the `kw_` erasure now fires after a `.` too
  (`(?<![\w'ₐ-ₜ])kw_`), without which a method-style reference to a promoted helper
  (`L.kw_toPointHom` vs `L.toPointHom`) is unmatchable — 5 `missing` otherwise. Monotone;
  no pre-existing row moved. Recorded in the playbook §4.
- **Hard rule honoured**: `ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved` is not
  declared in either form; both call sites use the imported
  `natCard_ker_pointMapOfPushforward_eq_finrankAlong`.
- **`KwD5BetweenCurvesHoloLift`**: all five pin copies byte-identical (`sha256`); the
  declared body differs from the pin text in exactly the two `kw_toPointHom` →
  `toPointHom` tokens.
- **Builds**: first stub check 1 m 47 s; module `lake env lean` 5 m 08 s clean; `flock`ed
  module `lake build` 5 m 25 s (7 m 08 user / 39 s sys, 9037 jobs); whole tree **9316 jobs,
  green, 11.4 s** cached. `#print axioms` on both headlines:
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, no heartbeat bump, no universe
  specialisation.
