# Row S — the seam/index row: blueprint and reconnaissance

**Status: reconnaissance and the set cut done 2026-10-06; the per-set work orders are written as
each predecessor lands (§3.4). S-1's is drafted.** Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. This is the blueprint for row
S of [TOPIC-V5-periodpair-uniformization.md](TOPIC-V5-periodpair-uniformization.md), whose §6 is
the row's first reading; it replaces that reading with measurements. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.1–§2.4. Numbers reproduce per §6.

**Why now.** TOPIC-V5 §6 item 3 says the `D5` seam must be enumerated before S is scoped. It
now is: D-4/D-5 landed three of the row's ten `KwD5BetweenCurves*` classes and the row owns the
other seven (§3). Row S does **not** depend on D-6 — only the S/D capstone does — so the two
are planned independently; the capstone is the one node that consumes both.

## 1. The row, measured

The ten nodes on the capstone's path, with the citation graph's premise counts (unported in
parentheses), all from `frontier.py`:

| node | pin lines | premises (unported) | role |
|---|---:|---|---|
| `PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint` | 2,673 | 17 (0) | the ℂ-analytic seam; the `KwD5BetweenCurves{HoloLift,CocountableHoloLift,LocallyHoloLift,CocountableAffineHoloCoords, …Weak}` family |
| `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient` | 2,021 | 18 (2) | lattice/index arithmetic; `KwD5BetweenCurves{IndexDual,KerQuotEquivBC,PointHomSublatticeCyclic}`, the `kw_surgehgf4_hID_*` block |
| `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker` | 978 | 2 (0) | the same subject, cardinality form |
| `PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` | 848 | **0** | leaf; primitive-coset reps and `jLattice` |
| `ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero` | 367 | 3 (0) | the `E₄³ − E₆²` argument |
| `ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero` | 85 | 2 (2) | the coset form |
| `ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic` | 25 | 3 (2) | the seam into `jLattice` |
| `Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one` | 88 | **0** | leaf; `SL₂(ℤ)` diagonalisation |
| `Field.nonempty_ringHom_complex_of_countable` | 45 | **0** | leaf |
| `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` | 17 | 1 (0) | leaf; listed with the J row in TOPIC-V5 §1 but **unported** |

Off this path but demanded by the D-S cone: `IsAddCyclic.of_squarefree_natCard` (14, leaf,
`IsAddCyclic.` is one node / 14 lines in the cone's unported demand).

**Ten files, 7,147 raw lines, 282 distinct declaration groups.** Six of the ten nodes are
*fully premised today* (the 2,673; the 978; the 848; the 367; the 88; the 45; the 17); the rest
are a forward-import DAG inside the row, which is what §3.7 wants. Nothing in the row is
blocked on D-6.

The four smallest leaves — the `SL₂(ℤ)` diagonalisation (88), `Field.nonempty_ringHom_complex_of_countable`
(45), the `E₄³ − E₆²` smul form (367) and `exists_variableChange_…` (17) — are ready now and
size a first set on their own.

## 2. The budget, and where the tool is wrong

`port_advise --targets <the ten files>` / `port_plan`:

```
raw S_ lines (47-node slice)          7,147
  − duplicate copies                   −1,593
  − boilerplate                          −252
  = distinct declaration groups (282)   5,302
  − already in the port (vetted)       −1,195
  NET NEW (the tool's figure)           4,107
substitutions: 148 trusted / 19 suspect
```

Independent check, at source level: the **union of the ten files' substantive lines is 3,189**
of the 7,147 raw, i.e. roughly **45% of the row's text is shipped more than once** — the same
silo structure as D-6. Per file, verbatim overlap with the other nine ranges from 5%
(`…E4_cube_div_discriminant_smul…`) to **78%** (`…natCard_ker`), and with the *already-ported*
pin files up to 50% (the 2,673-line file, whose prelude D-5's silos share).

So the tool's dedup figure and its `already in the port` figure are both **distorted here**,
in opposite directions:

- twelve substitution entries carry the `p2m_*` span artefact (`KwD5BetweenCurvesHoloLift` at
  748 / 151 / 83 lines — the definition is 11 lines and byte-identical in all five pin copies,
  P-2e §Amended), which inflates the “removable” column;
- the statement test cannot see a renamed engine, so real reuse is under-counted.

**Do not price S from 4,107.** Re-measure the dedup on normalized bodies (§2.4) before the set
orders; the shape of the answer is already visible in `port_plan`'s blocks: the two big
`PeriodPair` files share a 1,794-line once-block (46 declarations, 875 of it already in the
port), three files share a 269-line block (6 declarations), and two share a 580-line block
(29 declarations).

### The row's three numbers (§2.1), measured independently

Counting *content* the §2.1 way — raw minus `import`/`attribute`/`set_option`/`p2m_*`/`open`/
`namespace`/`end`/`section`/`variable`/`universe`/`local notation`/`scoped`/comments/blanks:

| | nodes | raw | content |
|---|---:|---:|---:|
| on the capstone's path | 10 | 7,147 | **4,337** |
| off it, in the cone (`IsAddCyclic.of_squarefree_natCard`) | 1 | 14 | 14 |

Per file, content ranges from 1,490 (the 2,673-line seam) down to 9 (the 17-line
`variableChange` leaf); the four small leaves are 70, 53, 32 and 10 content lines, so S-4 is a
small set by any measure.

Two more measurements, both independent of the tool's span arithmetic:

- **the row's once-only text** — the union of the ten files' substantive lines (≥12 chars) is
  **3,189**; i.e. ≈45% of the row's text is shipped more than once, the same silo structure as
  D-6. Per file, verbatim overlap with the other nine ranges from 5%
  (`…E4_cube_div_discriminant_smul…`) to **78%** (`…natCard_ker`), and with the *already-ported*
  pin files up to 50% (the 2,673-line file, whose prelude D-5's silos share).
- **statement-identical to the port** — 148 substitutions, ≈2,477 lines by span; excluding the
  19 the tool itself flags (`def … : Prop` type-only matches) leaves **≈1,924**. The truth sits
  between: some flagged entries are artefacts (`KwD5BetweenCurvesHoloLift` reported at 151 and
  83 lines against `PeriodPair.DiscriminantNeZero` — the definition is 11 lines and
  byte-identical in all five pin copies, P-2e §Amended) while others are genuine matches the
  tool got by type (`IndexDual` is real new content, and the flag is right; `HoloLift` is
  landed and the flag is wrong).

**So the row's price is ≈1,700–2,400 new content lines**, not 4,107 — and each set's order
should carry its own subtraction rather than inheriting either figure. The two tool columns
are distorted here *in opposite directions*: the `p2m_*` span artefact inflates the removable
column, and the name/statement-anchored test cannot see a renamed port declaration, so it
deflates the reuse column.

## 2.1 S-1, audited mathlib-first (§2.2) and priced

S-1 is the row's one genuinely hard fork and the 2,673-line figure is mostly not it. The
file's 133 declarations break down as:

- **`:51–960`, ≈90 declarations** — the place dictionary (`CoordinateRing.*`, `IsFinitePlace.*`,
  `placeOfEquation*`, `InfinitePlace.*`, `placeOfPoint_*`) and the `PeriodPair` prelude
  (`kw_discriminantNeZero`, `kw_isUniformization`, `kw_toPoint_add`, `sub_fract_mem_lattice`,
  `apply_eq_apply_of_differentiable_of_forall_periodic`, `gate_scale_mul`, `kw_countable_lattice`,
  `kw_toPointHom*`). **In the port** — `Place/Dictionary.lean`, `Elliptic/PeriodPair/{Basic,
  Lattice,Discriminant,Uniformization}.lean` — **import**.
- **`:1190–1523`** — place algebra (`ord_div`, `mk_mem_XYIdeal_iff`, `ord_placeOfEquation_pos_iff`,
  `yGen`, `ord_sub_evalAt_pos`, `placeOfPoint_placeOfPointEquiv_symm`) plus
  `Δ_ne_zero_of_isElliptic` and `placeOfPointEquiv`. Mostly **in the port**; the tail
  (`placeOfPointEquiv`, `kw_surjective_toPointHom`, ≈85) is not.
- **`:1524–2657`, the seam** — `KwD5BetweenCurvesLocallyHoloLift` and the chain
  `hH2_betweenCurvesHoloLift_of_locallyHolo` → `hH2c_…of_cocountable` →
  `KwD5BetweenCurvesCocountableHoloLift` → `hH2d_…of_affineHoloCoords` →
  `KwD5BetweenCurvesCocountableAffineHoloCoords` → `hH2e_…of_weak` →
  `KwD5BetweenCurvesCocountableAffineHoloCoordsWeak` → `hH2f_*` → `kw_surgehgf4_hH2f_betweenCurvesHoloLift`
  (203 lines), with `kw_differentiableOn_eval_wp` / `…_evalEval_wp`,
  `kw_countable_toPointHom_preimage`, the `kw_fdn2_qephod_hend7_geomMorphBC*` block and
  `mmr73_cs_*`. **This is S-1's content.** `solution` (`:2658`) is a ~15-line call into the chain.
- **The covering-map layer** (`:1112–1189`): `kw_isDiscrete_lattice`,
  `kw_isCoveringMap_mk_lattice`,
  `kw_differentiable_of_locally_differentiable_lift_through_mk`,
  `kw_toPointHom_eq_toPointAddEquiv_mk`. **New**, and absent from the port under either spelling
  (checked with the `kw_` stripped as well — the first check against the pin's names was
  meaningless, the port strips the prefix on promotion).

`port_advise` on the file: **78 substitutions, ≈1,203 lines** (the big ones land in
`Place/Dictionary.lean` 316, `PeriodPair/Basic.lean` 201, `Engine.lean` 189,
`PlaceCalculus.lean` 112, `Uniformization.lean` 105, `FunctionFieldQuadratic.lean` 86,
`NatCard.lean` 69, `Lattice.lean` 65). Note `mmr73_cs_evalAt_eq_of_ord_sub_pos` (87) is
**already ported** into `IsogenyEndDatum/Engine.lean` — part of the seam's own machinery — and
`KwD5BetweenCurvesHoloLift` is landed in `KernelBaseChange.lean` (the tool reports it against
`PeriodPair.DiscriminantNeZero` with a 151-line span, both artefacts).

**The mathlib answer.** `existsUnique_continuousMap_lifts` exists in mathlib
(`Topology/Homotopy/Lifting.lean`), as do `differentiableOn_weierstrassP` /
`analyticOnNhd_weierstrassP` (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). So the
lift is mathlib's lifting theorem, not a bespoke development — but mathlib has **no**
`IsCoveringMap.differentiableAt` and no covering-map differentiability lemma at all, so the
step from a continuous lift of `ℂ → ℂ/Λ` to a differentiable lift stays the pin's own argument
(`kw_differentiable_of_locally_differentiable_lift_through_mk`). Likewise the dictionary, the
℘-isomorphism and the `IsCoveringMap (ℂ → ℂ/Λ)` instance itself are the port's, not mathlib's.

**Priced**: ≈1,300–1,400 new raw lines (≈2,673 − 1,203 substitutions − scaffolding), of which
the seam chain and the covering-map layer are the whole cost; nothing in the audit reduces
S-1 to a handful of lines. It stays the largest set of the row and needs no scout — the route
is the pin's, and the two ingredients that could have killed it (the lifting theorem and the
℘-differentiability) are both present.

**Follow-up measurement: the covering-map layer is nearly free.** `:1112–1189` looked like the
set's one genuine unknown (its `IsCoveringMap (ℂ → ℂ/Λ)` instance). It is four short
declarations, and three are mathlib lookups: `kw_isDiscrete_lattice` is
`isDiscrete_iff_discreteTopology` on **mathlib's own** `DiscreteTopology L.lattice`
(`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:118`), `kw_isCoveringMap_mk_lattice` is
`(AddSubgroup.isAddQuotientCoveringMap_of_comm …).isCoveringMap`
(`Topology/Covering/AddCircle.lean:30`), and one is `rfl`; only
`kw_differentiable_of_locally_differentiable_lift_through_mk` (≈30 lines) is real work, and it
is `Metric.mem_nhds_iff` + `IsPreconnected.constant_of_mapsTo` + `DifferentiableOn.add`. So the
set's *risk* drops well below its price; the price is unchanged, because those lines were
never a large part of the 1,300. The same file also carries mathlib's
`IsZLattice ℝ L.lattice` (`:120`), which S-2 should use for its covolume/`relIndex` bridge
(§2.2).

## 2.2 S-2, reconnaissance (the lattice/index arithmetic)

Two files — `S_…_isAddCyclic_sublatticeQuotient` (2,021) and `S_…_natCard_ker` (978) — 2,999
raw, **content 1,854**, `port_advise` **68 substitutions ≈868 lines**, of which ≈222 are
`def … : Prop` type-only matches and `axiomAnchor` stubs (the three classes reported at 44 / 17
/ 15 lines and two `kw_surgehgf4_*_axiomAnchor`s at 31 / 16). Real reuse ≈646 lines, and it is
**almost entirely the two files' shared prelude** (`:51–800` and `:51–420`: the place
dictionary, the `PeriodPair` scale block, `toPointHom`/`ker_toPointHom`). **Net ≈1,200** — the
same order as S-1, and it is one subject: the arithmetic of the pin's ℤ-lattice index.

Its own content, by region:

- `:922–1101` — `MilneI72IntersectionData`, `divNHom`, `latticeDivQuot`,
  `latticeQuotTorsionEquiv`, `card_torsionBy_latticeQuotient` (53): the torsion of a lattice
  quotient and its cardinality.
- `:1103–1272` — the three classes (`IndexDual` 47, `PointHomSublatticeCyclic` 17,
  `KerQuotEquivBC` 15), `kw_zlatticeQuotientTorsionCountBridge_axiomAnchor`,
  `kwLatticeCoeAddEquiv`, `kwLatticeToAddSubgroup{Free,Finite}`,
  `kw_card_torsionBy_zlatticeQuotient{,_finrank_real}` (39). `IndexDual` is called from both
  nodes, so it is the pair's shared surface.
- `:1273–1580` — the `hscd`/`hID_*` block: `kerIndexHom` and its `_apply`/`_surjective`/`_ker`,
  `scale_subset`, `forwardIndex_eq_card_ker`, `card_smul_subset`, `dualUnit`/`_val`,
  `dual_subset`, `sublatticeIndex_congr_snd`, `scaleIndexHom`, `sublatticeIndex_scale_nat`,
  `dualIndex_eq`. This is the set's core.

**The two files duplicate that core, which is why S-2 is one module.** The 978-line node's
outline is the same shape at a smaller scale: `:17–312` the shared prelude (ported), `:147–260`
the torsion-count block (`divNHom`, `latticeDivQuot`, `latticeQuotTorsionEquiv`,
`card_torsionBy_latticeQuotient`), `:451–540` the `kwLattice*`/`kw_card_torsionBy_*` bridge,
`:541–592` the `KwD5BetweenCurvesIndexDual` class, `:639–964` **the same `hID_*` block by name**
(`kerIndexHom`, `dualUnit`, `dual_subset`, `sublatticeIndex_scale_nat`, `dualIndex_eq`, and its
own `…betweenCurvesIndexDual_proved`), then `:965` the `solution`. So the `hID_*` block ships
twice (265 + 325 lines) and `card_torsionBy_latticeQuotient` twice (`:260` and `:1050`); writing
them once is the set's dedup, and it is the reason the 978-line node's only unported premise is
the 2,021-line node itself. With mathlib supplying the determinant-index and `ModN` steps
(audited above), S-2 stays ≈1,000–1,200 despite its 2,999 raw lines.
- `:1581+` — the `kqe_*` block (`map_fst`, `map_snd`, `map_eq`).

**mathlib first — two findings.** The port's
`Elliptic/PeriodPair/Basic.lean:171,174` already holds `sublatticeIndex` and
`sublatticeQuotient` **publicly** (P-SET-1), but **not** `card_torsionBy_latticeQuotient`,
`latticeQuotTorsionEquiv` or `SublatticeIndex`. And mathlib **does** have the `ZLattice` API:
`ZLattice.covolume`, `covolume_div_covolume_eq_relIndex` (`Algebra/Module/ZLattice/Covolume.lean:148,170`),
`covolume_eq_det_mul_measureReal`, plus `ZSpan.fundamentalDomain` / `IsAddFundamentalDomain`
(`Algebra/Module/ZLattice/Basic.lean`) — **and `PeriodPair` already carries
`IsZLattice ℝ L.lattice`** (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:120`), so the
port's `L.lattice` is an `IsZLattice` from the start. The pin's
`kw_card_torsionBy_zlatticeQuotient_finrank_real`
("the torsion count of a ℤ-lattice quotient is the real finrank") is a `relIndex`/covolume
computation in that vocabulary — likely a short derivation, not new mathematics. **Audit that
block against `ZLattice` before pricing it**; it is the one place in S-2 where a mathlib call
might replace a transcription.

**Audited, not just flagged.** The four mathlib names the pin's covolume block rests on all
exist in `v4.34`, so the block is a derivation rather than a transcription:
`ZLattice.module_free` / `ZLattice.module_finite`
(`Algebra/Module/ZLattice/Basic.lean:509,485`) turn the pin's
`kwLatticeToAddSubgroupFree`/`Finite` into one-liners; `ZLattice.rank` (`:522`,
`finrank ℤ L = finrank K E`) does the same for `kw_card_torsionBy_zlatticeQuotient_finrank_real`;
and `ModN.natCard_eq` (`LinearAlgebra/FreeModule/ModN.lean:106`,
`Nat.card (ModN G n) = n ^ Module.finrank ℤ G`) is the last step of the 53-line
`card_torsionBy_latticeQuotient`. With `IsZLattice ℝ L.lattice` already instantiated by
mathlib, every `[IsZLattice ℝ L]` lemma applies to `L.lattice` directly, and the pin's
`hID_*` index arithmetic sits on `AddSubgroup.relIndex` (`GroupTheory/Index.lean:64+`) with the
covolume formula `ZLattice.covolume_div_covolume_eq_relIndex` available to identify index and
covolume. **Price S-2 at ≈1,000–1,200**, not 1,200 flat: roughly 150 of the 1,200 content lines
are this block.

**Order.** S-2's work order must be written after S-1 lands and is reviewed: the 2,021-line
node's only unported premises are the 2,673 (S-1) and the 978 (S-2's own), so S-2 imports S-1's
headline and the hand-off has to name real declarations.

## 2.3 S-3 and S-4, reconnaissance

**S-3** — `exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` (848 raw, **521 content**,
68 declarations, a leaf with **0 premises**). `port_advise`: 18 substitutions ≈165 lines,
essentially all of the `:129–250` prelude (`scale_lattice`, `scaleLatticeEquiv`, `G_scale`,
`g₂_scale`, …, `linearIndependent_tau_one`, `ofTau_latticeEquivProd_symm_apply`,
`im_div_ne_zero`, `span_neg_fst`). Its own content, by region:

- `:253–447` — **ℤ²-lattice combinatorics**: `natGen`, `zmultiples_natAbs`,
  `zmultiples_natGen`, `natGen_cast_mem`, `index_eq_natGen`, `dvd_of_mem_natGen`, `latticeOf`,
  `mem_latticeOf_iff`, `ker_fst_eq_range_inr`, `index_eq_comap_inr_mul_map_fst`, `aOf`, `dOf`,
  `index_eq_dOf_mul_aOf`, `zero_dOf_mem`, `dOf_dvd_of_zero_mem`, `exists_over_aOf`, `bOf`,
  `aOf_bOf_mem`, `bOf_nonneg`, `bOf_lt`, `latticeOf_canonical_eq` (≈195 lines). New, and it is
  not the ported `ModularCurve/Defs/PrimCosetReps.lean` (that is the coset-representative
  subject); nor is it shared with S-2, which uses `sublatticeIndex`/`sublatticeQuotient` and
  none of these names.
- `:448–600` — `kw_scale_lattice_toAddSubgroup`, `kwSublatticeIndex_scale`,
  `kw_exists_scale_ofTau_lattice_eq`, `kw_phiTau*`, `kw_HZZ*`, `kw_sublattice_eq_span`,
  `kw_hnfPoint*` (≈150).
- `:601–671` — `kw_surgehgf4_hu5c_not_isAddCyclic_zmod_prod` (19) and
  `kw_surgehgf4_hu5c_gcd_eq_one_of_isAddCyclic` (52): `IsAddCyclic` of a product of cyclic
  groups forces the orders coprime. **Corrected after audit**: an earlier draft of this note
  flagged this pair as "the most mathlib-replaceable part of the set"; it is not.
  `hu5c_not_isAddCyclic_zmod_prod` is a direct `addOrderOf`/`Nat.card` argument and
  `hu5c_gcd_eq_one_of_isAddCyclic` is a derivation over the pin's own `aOf`/`bOf`/`dOf`
  invariants; mathlib has `IsAddCyclic` and its basics (`GroupTheory/SpecificGroups/Cyclic/Basic.lean`)
  but no product-cyclicity or HNF-coprimality criterion. Expect to write both.

**mathlib first — the ℤ² block's foundations are mathlib's, but its invariants are the
pin's.** Every primitive the `:253–447` block is built from is a mathlib call:
`Int.subgroup_cyclic` and `Int.index_zmultiples` (so `natGen` is "the generator of a subgroup of
`ℤ`" and `index_eq_natGen` is `K.index = |generator|`), `AddSubgroup.mem_closure_pair`
(`mem_latticeOf_iff`), `AddSubgroup.mem_prod` (`ker_fst_eq_range_inr`), and `AddSubgroup.index`
itself. mathlib also has the determinant–index formula in general form —
`AddSubgroup.index_eq_natAbs_det` and `AddSubgroup.relIndex_eq_natAbs_det` /
`relIndex_eq_abs_det` (`LinearAlgebra/FreeModule/Finite/CardQuotient.lean:98,106,114`) — so the
`index_eq_comap_inr_mul_map_fst`/`index_eq_dOf_mul_aOf` route may be re-expressed through it
rather than re-proved for `ℤ × ℤ`. What is **not** in mathlib is the pin's set of *named*
invariants (`natGen`, `latticeOf`, `aOf`, `dOf`, `bOf`, `latticeOf_canonical_eq`), which the
`hu5c` criterion and the rest of the set consume by name; those are written as they stand.
- `:672–807` — `KwSublatticeQuotientZZTransport` (a `Prop`, 33) and the `qtzz_*` block proving
  it (≈105). Read the bodies: the class is not droppable on a tool's word (P-2 §6).
- `:808` — `solution`, the headline.

**S-4** — the `E₄³ − E₆²` / `jLattice` modular-polynomial tail: the 367-line
`eval_E4_cube_div_discriminant_smul_eq_zero` (content 298; 10 substituted lines, so almost all
new, but it is a *modular-forms q-expansion computation* — `qExpansion_finset_prod`,
`qExpansion_finset_sum_smul`, `pow_mul_div_pow`, the `An`/`coeAddHom` bookkeeping — so its cost
is work over the ported `ModularForm`/`EisensteinSeries`/`CuspForm` layer, not new analysis),
the 85-line coset form (`jt`, `sl_mem`, `jt_smul`, `upperTriangularGL*`), and the 25-line
`eval_jLattice_eq_zero_of_isAddCyclic` (10 content lines, one declaration).

**Audited.** Its *heavy* inputs are all **in the port**: `ModularForm.exists_degeneracy_Gamma0`
(`ModularForms/Level/Degeneracy.lean`), `heckeDiagMatrix` and `coe_heckeDiagMatrix_smul`
(`ModularForms/HeckeQExpansion.lean`), `ModularCurve.primCosetReps`
(`ModularCurve/Defs/PrimCosetReps.lean`), `upperTriangularGL`
(`ModularForms/Gamma1Vanishing.lean`). What is **not** in the port is the pin's generic
q-expansion bookkeeping by name (`qExpansion_finset_prod`, `qExpansion_finset_sum_smul`,
`pow_mul_div_pow`, `prod_ite_pow`, `card_univ_mul`, `coeAddHom`) nor the two level-one forms the
degeneracy step consumes (`e4cube1` = `E₄³`, `delta1` = `Δ`, with their `coe_*` lemmas). Those
two have port counterparts under **different names and a different spelling** — `eCubeSubESq`
in `ModularForms/DiscPow.lean`, and the `E₄`/`Δ` layer in `ModularForms/JInvariant.lean` — which
is why `port_advise` reports only 10 substituted lines for the file: the same
renamed-declaration blind spot as §2.1. **Audit the two forms and the q-expansion helpers by
statement before pricing S-4**; the price is in the finite-product bookkeeping either way.

The three remaining nodes are leaves that share no story with each other or with the above —
`Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one` (88 raw / 70 content,
`exists_coprime_mul_add` + `main`), `Field.nonempty_ringHom_complex_of_countable` (45 / 32,
one declaration), `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` (17 / 9, one
declaration) — plus the off-path `IsAddCyclic.of_squarefree_natCard` (14). They are §0.2's
"below the subagent threshold" case and go in the manager's own set (§4).

## 3. The seam: three landed, seven new

D-4/D-5 chose the seam's home and landed `ModularCurve.KwD5BetweenCurvesHoloLift`,
`…FFSeamBaseChange` and `…KerTransportAlongEmbed` in
`WeierstrassCurve/Isogeny/KernelBaseChange.lean`. The row calls seven more, none of which
exists anywhere in the port (`grep -rl` over `lean/FLTForHuman/` is empty for each):

| class | called from | pin decl |
|---|---|---:|
| `KwD5BetweenCurvesCocountableHoloLift` | 2,673 (6×) | 12 |
| `KwD5BetweenCurvesLocallyHoloLift` | 2,673 (3×) | 11 |
| `KwD5BetweenCurvesCocountableAffineHoloCoords` | 2,673 (4×) | 14 |
| `KwD5BetweenCurvesCocountableAffineHoloCoordsWeak` | 2,673 (4×) | 13 |
| `KwD5BetweenCurvesIndexDual` | 2,021 (4×), 978 (2×) | 47 |
| `KwD5BetweenCurvesKerQuotEquivBC` | 2,021 (3×) | 15 |
| `KwD5BetweenCurvesPointHomSublatticeCyclic` | 2,021 (2×) | 17 |

Four of the seven are the ℂ-analytic family (S-1's subject); three are the lattice/index family
(S-2's). Each is a `def … : Prop`, so per P-2 §6 **none may be dropped on a tool's word** —
`grep -c` the body of each, and decide restatement-versus-new after reading the bodies, not
from the declaration count. The row also calls `PeriodPair.kw_toPointHom` heavily (35× in the
2,673-line node alone) — that one is **already promoted** by P-2e §1.5 into
`Elliptic/PeriodPair/Uniformization.lean`, so it is an import.

Two consequences for the plan:

1. **The seam is two disjoint families, not one shared block.** The four ℂ-analytic classes
   are called only from the 2,673-line node; the three lattice/index classes only from the
   2,021 and 978 nodes (the block data confirms it: the `IndexDual` block's file set is
   `{2,021; 978}`). What S-1 and S-2 *do* share is the pin's **prelude** — and that is already
   ported and imported. So there is no separate shared home to write before the sets, and the
   class definitions go with the set that proves them.
2. **They are a reduction chain, not a library.** The four ℂ-analytic ones are successive
   weakenings of one statement, each with its own reduction lemma and each load-bearing:
   `LocallyHoloLift` (∀ `z₀`, a local differentiable lift `G` with
   `L'.toPointHom (G z) = pmop (L.toPointHom z)`), then `CocountableHoloLift` (the same off a
   countable `S`), then `CocountableAffineHoloCoords` (differentiable coordinates `X, Y` with
   `Y z ≠ 0` and `pmop (L.toPointHom z) = Point.some (X z) (Y z) h`), then
   `…Weak` (the same without the `Y z ≠ 0` conjunct), with
   `hH2e_…of_weak → hH2d_…of_affineHoloCoords → hH2c_…of_cocountable → hH2_…of_locallyHolo`
   and finally `kw_surgehgf4_hH2f_betweenCurvesHoloLift` proving the D-5-landed
   `KwD5BetweenCurvesHoloLift`. Every one is a `def … : Prop`, so P-2 §6's rule applies
   without exception: none may be dropped on a tool's word. Expect to write the whole chain
   in one set — it is one proof.

`exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` (848) and the `E₄³ − E₆²` pair may
also be largely **already paid for**: TOPIC-V5 §5 records that the port holds
`ModularCurve/Defs/PrimCosetReps.lean` and `ModularCurve/Gamma0Index.lean` (the `primCosetReps`
side) and the whole ported `ModularForm`/`EisensteinSeries`/`CuspForm` analytic layer, which
the `E₄³ − E₆²` route touches. Audit by statement before pricing either.

## 4. The set cut (proposed, tentative)

By mathematical fork, not by size (§3.4). One subagent per set, reviewed before the next:

| set | subject | nodes | raw | net |
|---|---|---|---:|---:|
| **S-1** | the ℂ-analytic seam, with its four reduction classes | the 2,673 | 2,673 | ≈1,300–1,400 |
| **S-2** | the lattice/index arithmetic, with its three classes | the 2,021 + the 978 | 2,999 | ≈1,000–1,200 |
| **S-3** | the primitive-coset / `jLattice` column | the 848 | 848 | ≈480 |
| **S-4** | the `E₄³ − E₆²` / `jLattice` modular-polynomial tail | the 367, 85, 25 | 477 | ≈360 |
| **SC** | the capstone **plus the three leaves** — the manager's wire test | the 415, 88, 45, 17 (+ the 14) | 579 | ≈250 |

**Module layout and namespaces (provisional; each set's order fixes its own).** §3.2 asks for the
destination to come from the pin's own namespace and sibling vocabulary, so:

- S-1 — `FLTForHuman/Elliptic/PeriodPair/HoloLift.lean`, the four classes in `ModularCurve` and
  the headline in `PeriodPair` (the pin's own split). Fixed by its order.
- S-2 and S-3 — also `Elliptic/PeriodPair/`, since both headlines are `PeriodPair.*` and the
  seam classes are `ModularCurve.KwD5BetweenCurves*`; `Lattice.lean` already holds the
  lattice/scale prelude, so these are siblings of it rather than additions to it. S-3's ℤ²
  invariants (`natGen`, `latticeOf`, `aOf`, `dOf`, `bOf`) are *generic* algebra over
  `AddSubgroup (ℤ × ℤ)`, so its order must decide whether they get their own generic module
  (§5: "a generic cross-theory count [gets] its own top-level area rather than a theory's
  `Defs/`") or sit beside the `PeriodPair` transport that consumes them.
- S-4 — the port already holds the pin's `E₄³ − E₆²` power series next to their siblings
  (`ModularForms/DiscPow.lean`) and the modular-polynomial modules
  (`ModularCurve/ModularPolynomial{Assembly,Irreducible,Properties,Uniqueness}.lean`), so the
  three `ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_*` / `eval_jLattice_*`
  nodes belong in a sibling of the latter, in namespace `ModularCurve.ModularPolynomialData`.
- SC — the capstone is `WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_…`, and it
  is the only consumer of the whole row; its module is the manager's and belongs beside the
  `ModularPolynomial` modules it concludes about.
- The collision fix (§4's SC prerequisite) is *not* a module: route (A) edits
  `WeierstrassCurve/IsogenyEndDatum/Engine.lean` and its users in place.

Order: **S-1 → S-2 → S-3 → S-4 → SC**. S-2 depends on S-1 (the 2,021-line node's unported
premises are exactly the 2,673 and the 978), so that order is forced; S-3 depends on neither,
and S-4 on S-3 only through the coset form's citation of the 848. S-3 and S-4 may therefore be
reordered after S-1 if a review changes the picture. SC consumes both D-6 and the whole row,
so it is written last and by the manager (§0.2, §3.4: the capstone is the review).

**The three leaves ride with SC, not with a subagent.** §0.2's threshold — "below roughly 1,000
written lines the overhead and the review are not worth it" — leaves each of them (70, 32, 9,
14 content lines) far below a set, and they share no story with each other; SC needs all of
them anyway. This is the one place the cut deliberately mixes subjects, and it does so in the
manager's own file where §3.4's "one story per subagent" does not apply.

**SC has a prerequisite that is not a port: the gate-instance collision.** Its proof descends
to `K₀` (D-6) and then must *produce* the `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem`
instances for `(E₀.baseChange (AlgebraicClosure K₀)).toAffine` and `E₀'`'s — it does it with
`exists_genusOnePlaceGate_isCentred_and_abelTheorem`, which lives in
`GenusOnePlaceGateCentred.lean` and drags `Place/RRSpace.lean`. The same proof also needs D-6's
headline, and `TwoCurveDescent.lean:55–56` imports `KernelBaseChange.lean`, which imports
`Engine.lean`. `RRSpace`'s `scoped instance instInfinitePlace` and `Engine`'s collide at the
name level, so no environment holds both and **SC cannot be written as it stands**. This is
the third set the collision blocks and the first one on a critical path; the two routes (rename
the port's own `Engine` instance, or re-home the producer's two missing dictionary lemmas off
`RRSpace`) are worked out in
[../../CARRY-FORWARD.md](../../CARRY-FORWARD.md) under the co-import collision, and it is now
**resolved by policy**: mark the port's own `Engine.instInfinitePlace` `private` (a `private`
name is mangled, so it cannot clash, and instance search still finds it), falling back to a
rename only if a consumer cannot — see the playbook's new bullets on the `private` fix and on
`private`/local instances as a build tool. Route (B), re-homing the producer off `RRSpace`, is
**not** the one-line import drop it looks like: the producer is stated through
`GeometricPlace.lean`'s `geomPlaceOfPoint*` family, all of which are conditional on the
`[InfinitePlace W]` instance that `RRSpace.lean:444` supplies. It should be priced with
`build_ladder.py --edit` and applied when no set is mid-check — it edits a module every D-4/D-5
module imports. **D-6 is unaffected** — it never produces a gate instance.

**There is no S-0.** The first draft of this cut put the seven seam classes in a shared set of
their own; §3 shows they are two disjoint families, each proved by the set that uses it, and
the only genuinely shared layer (the prelude) is already ported. §3.7's "shared blocks first"
therefore has nothing to order.

The `net` column is the file's content minus its statement-identical-to-port lines, measured in
§2.1–§2.3; it is the number the set's own order must re-check, not a budget to inherit.

## 5. Open questions before the set orders

1. **Does mathlib shorten S-1?** **Answered — §2.1.** The lifting theorem
   (`existsUnique_continuousMap_lifts`) and the ℘-differentiability are mathlib's; the
   covering-map layer and the seam chain are not, and mathlib has no covering-map
   differentiability lemma. S-1 stays ≈1,300–1,400 new raw lines and needs no scout.
2. **Are the seven classes restatements of each other?** Four are `Cocountable*`/`Locally*`
   variants; `grep -c` their bodies and record which are distinct mathematics.
3. **The seam's home.** **Answered — §3.** Each family's classes are proved by the set that
   uses them, in that set's own new leaf module (S-1's four, S-2's three), declared public at
   the pin's `ModularCurve.KwD5BetweenCurves*` names. There is no separate seam module and no
   pre-wave home decision. The binding constraint on both modules is unchanged: never import
   `GenusOnePlaceGateCentred.lean`, never `Place/RRSpace.lean`.
4. **Is the 848-line node already paid for?** **Answered — no.** `port_advise` on S-3 + S-4
   reports 1,475 raw lines, 18 substitutions ≈165 lines, net-new 1,172. The 848-line node's
   first ~250 lines are the ported lattice/scale prelude (`scale_lattice`,
   `scaleLatticeEquiv`, `G_scale`, `g₂_scale`, …, `linearIndependent_tau_one`,
   `ofTau_latticeEquivProd_symm_apply`, `im_div_ne_zero`, `span_neg_fst`), and the rest —
   `natGen`, `zmultiples_*`, `latticeOf`, `mem_latticeOf_iff`, `ker_fst_eq_range_inr`,
   `index_eq_comap_inr_mul_map_fst`, `aOf`, `dOf`, `bOf`, `index_eq_dOf_mul_aOf` — is **new**
   ℤ²-lattice index arithmetic. It is not the ported `ModularCurve/Defs/PrimCosetReps.lean`
   (that is the coset-representative subject), and it is **not** shared with S-2: the pin's
   2,021-line node uses `sublatticeIndex`/`sublatticeQuotient` and none of these names. So S-3
   is a self-contained ≈600-line set of elementary lattice combinatorics, and no cross-set
   dedup exists between S-2 and S-3.
5. **Re-measure the dedup** on normalized bodies (§2), and give the row its three numbers
   (nodes / raw / content) before the first set order.

## 6. Reproduce

```bash
cd tools/deps
python3 port_advise.py --targets build/rowS_targets.txt --json build/rowS_advise.json
python3 port_plan.py  --json build/rowS_advise.json --json-out build/rowS_plan.json

# the seam gap (expect the three landed, seven empty)
for n in KwD5BetweenCurvesHoloLift KwD5BetweenCurvesCocountableHoloLift \
  KwD5BetweenCurvesLocallyHoloLift KwD5BetweenCurvesCocountableAffineHoloCoords \
  KwD5BetweenCurvesCocountableAffineHoloCoordsWeak KwD5BetweenCurvesIndexDual \
  KwD5BetweenCurvesKerQuotEquivBC KwD5BetweenCurvesPointHomSublatticeCyclic; do
  printf '%-50s %s\n' "$n" "$(grep -rl "def $n" --include=*.lean ../lean/FLTForHuman/)"
done

# the capstone's unported closure (expect 12 nodes / 11,291 lines)
python3 - <<'PY'
import frontier
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
q = 'WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward'
cl = [n for n in fr.closure(pay.pid(q)) if n not in front]
print(len(cl), sum(pay.lines(n) for n in cl))
PY
```

`build/rowS_targets.txt` is the ten-file list (`tools/deps/build/` is untracked); regenerate
it from the table in §1.
