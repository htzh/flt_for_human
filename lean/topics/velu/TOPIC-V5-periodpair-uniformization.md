# V5 (scoping) — the `PeriodPair` uniformization slice

**Status: port decision taken; the U, J and D rows landed 2026-10-06. P-SET-1 (the dictionary,
`discriminant_ne_zero`, `isUniformization_toPoint`), P-SET-2 (the `j`-line) and P-2 (the whole
base-change/descent column, D-1…D-5) are in the port; the remaining rows are S (seam/index)
and the `rationalHomSet`/torsion columns.** This document answers one question — *how big
is the slice that gates the last Phase D node, and is the work actually that large?* —
and records the math-first scout (§6) and the prune pass (§2.1) that must precede any
port. It is not a work order; nothing here has been dispatched. Triggered by
[TOPIC-V4-isogeny-kernel-rigidity.md](TOPIC-V4-isogeny-kernel-rigidity.md) §9 ("the one
remaining Phase D item"), whose prerequisite is **not** in the Deligne–Serre cone and
not in this column. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib
`v4.34.0`. Measurements from `tools/deps/port_advise.py`, `port_plan.py`,
`frontier.py`, `prune.py` (§8).

**Answer in one line.** It is genuinely as large as it looks — the subject is **18 nodes
/ 12,265 pin lines**, all unported, and the two hard classical theorems (complex
uniformization, surjectivity of `j`) plus a 2,673-line analytic seam are *on* the path,
not inlined prelude. The scout (§6) shows the uniformization core is the one piece
mathlib lacks outright and is Mathlib-only, so it opens the port as set P-SET-1. The
prune pass (§2.1) shows something stronger: the subject is **not** a subtree of
`aeval_j_diag_eq_zero_of_finrankAlong_eq`. Every target in the root cone demands all 18
nodes; both the Mazur chain and the step-4/D-S cones reach `isUniformization_toPoint`
without that node; and supplying the node saves 4 nodes / 4,681 lines. This is a shared
subject to port, not a tail of one lemma.

## 1. The trigger, and what it actually needs

`WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`:
for an elliptic `W/K` (`K` algebraically closed, char 0), `N` squarefree, a
`ModularPolynomialData N` and an isogeny datum of degree `N`,
`aeval W.j (Φ(X)) = 0`. Its `S_` file is 647 lines; the proof is a **reduction to ℂ**:

1. descend to a *countable* intermediate field `K₀` and base-change the datum
   (`exists_intermediateField_countable_map_eq_and_finrankAlong_eq`, 2,684 lines);
2. push the datum from `AlgebraicClosure K₀` to ℂ
   (`exists_algHom_functionField_baseChange_finrankAlong_eq`, 1,336);
3. replace the curve by `L.weierstrassCurve` for a lattice `L`
   (`exists_variableChange_smul_weierstrassCurve_eq`, **17 lines** — a six-line proof
   that *essentially uses* `PeriodPair.jLattice_surjective`, so the 1,054-line
   surjectivity theorem hangs off it);
4. do the lattice/isogeny-index arithmetic
   (`exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`,
   2,021 — whose own closure pulls in `isUniformization_toPoint` 1,493,
   `exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint` 2,673 and
   `…_natCard_ker` 978);
5. finish with the modular-polynomial identity
   (`eval_jLattice_eq_zero_of_isAddCyclic`, 25 lines, closure 2,140).

Measured closure:

```
gate's own S_ file                                      647
ucl (unported closure)              17 nodes / 15,179 lines
call-closure of the six called nodes 16 nodes / 15,068 lines
```

The `ucl` and the call-closure agree to within 111 lines, and the tool's small
"off-path" bucket is itself unreliable here (`nonempty_functionField_algEquiv_of_variableChange`,
744 lines, is in fact called at `S_` line 627). **Treat 15,179 as the working figure.**
Unlike V2 and V3, there is no large inlined prelude to discount. Note what that number
is: the gate's *closure*, not its *marginal* demand — most of the subject behind it is
needed by other consumers anyway (§2.1).

**Where it sits.** Exactly two pin theorems consume it —
`IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j` and
`…_of_transcendental_j` — and the two consumers route differently. The first gives the
shortest citation path to the root: `aeval_j_diag … →
separable_map_eval2_of_not_isIntegral_of_isAlgClosed →
modularPolynomial_rootMultiplicity_jQuotVelu_eq_one → moduliPointExists_jQuotVelu_of_mult_two →
mazurStepThree_not_inZeroComponentAt → FreyPackage.frey_no_cofixed_large → Mazur_Frey →
fermatLastTheoremFor_of_five_le`. The second carries the node into the Deligne–Serre
cone (`frontier.closure` of `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`)
and into the cone of step 4's source `S_WeierstrassCurve_modularity_of_semistableModel.lean`,
through the weight-one input (`weightOneNewformExists_levelAtThree_not_cube_dvd` →
`hasIntegralStructure_two` → … → `ord_jBar_dvd_three` →
`mem_of_isRoot_map_j_of_transcendental`). The "Mazur gate" heading of
[TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md) §2.2 names that shortest path; it does not
name an exclusive owner.

**The gate is not the door to the uniformization.** Reading the source DAG by the
shortest route shadows the real structure, and the prune pass of §2.1 corrects it: the
gate's whole *marginal* demand is **4 nodes / 4,681 lines** — itself, the
countable-descent node, the base-change node and `IsAddCyclic.of_squarefree_natCard` —
while the 18 `PeriodPair` nodes / 12,265 lines are demanded by every target anyway, and
each side reaches `PeriodPair.isUniformization_toPoint` without the gate (Mazur step 3
in 7 hops; the D-S capstone in 14). The uniformization is a **shared subject**, not a
subtree of the gate. It is also *not urgent*: every consumer is unported, so nothing
half-built is blocked.

## 2. The gap structure and the budget

### 2.1 The gap structure (prune pass)

`prune.py` reads a node as *prunable* once the removed set `R` is replaced iff every
root path to it passes through `R` — the criterion that sees the connections a shortest
route hides:

| removed | prunable [the saving] | rewire obligations |
|---|---:|---:|
| `aeval_j_diag_eq_zero_of_finrankAlong_eq` | 4 nodes / 4,681 lines | 2 nodes / 119 |
| the subject, `PeriodPair.*` | 18 nodes / 12,265 lines | 24 nodes / 24,656 |

Both sides already reach the uniformization without the gate. Mazur step 3, 7 hops:
`mazurStepThree_not_inZeroComponentAt` → `moduliPointExists_jQuotVelu_of_mult_two` →
`modularPolynomial_eval_jInt_jQuotVelu_eq_zero` →
`isRoot_map_j_veluQuotient_j_of_addOrderOf_eq` →
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward` →
`isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj` → `isUniformization_toPoint`.
The D-S capstone, 14 hops: `…weightTwo_hecke_eigen` →
`CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` → … →
`CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq` →
`PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq` →
`isUniformization_toPoint`. `isUniformization_toPoint` has 11 consumers, 7 outside the
gate's subtree; `discriminant_ne_zero` has 15, 8 outside.

The subject's own order — 18 nodes, all `PeriodPair.*`:

* **`discriminant_ne_zero` (542)** — the hub, 9 in-subject consumers;
* **`isUniformization_toPoint` (1,493)** — the second hub, 6;
* the `j`-line: `jLattice_ofTau` (210), `jLattice_surjective` (1,054),
  `exists_variableChange_smul_weierstrassCurve_eq` (17);
* the isogeny/index arithmetic: `exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`
  (2,673), `exists_scale_lattice_…_natCard_ker` (978), `…_isAddCyclic_sublatticeQuotient`
  (2,021), `exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` (848);
* the `rationalHomSet` column: `exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul`
  (682), `exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet` (477);
* the torsion column: `weierstrassP_torsion_modularForm_slash_tendsto_atImInfty` (558),
  `exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff` (319);
* the leaves: `lattice_eq_of_g2_eq_of_g3_eq` (234), `g2_ofTau_and_g3_ofTau` (47),
  `scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero` (47), `weierstrassP_scale` (22).

The field-descent nodes the gate does own (`exists_intermediateField_countable…`,
`exists_algHom_functionField_baseChange…`) are not `PeriodPair` at all; they are the
subject's generic neighbours.

### 2.2 The budget

The `PeriodPair` family is 18 wrappers / 18 `S_` files, 12,265 pin lines, 801
declarations. `port_plan` on the whole glob:

```
raw S_ lines (18 wrappers)                    12,265
  − duplicate copies (shared preludes)        −2,337
  − boilerplate                                 −520
  = distinct declaration groups (566)          9,408
  − already in the port (vetted)                −885
  = NET NEW MATH LINES                         8,523
```

`port_advise` finds 110 substitutions (≈1,768 lines) — but that test is
**name-anchored** (V3 §2.3, V4 §4.2), so it is a lower bound, and the real reuse is
probably much larger (§5).

**Context.** The subject is 18 nodes / 12,265 pin lines, all unported — small against the
port's remaining demand (28,716 nodes / 11.55 M raw lines), but *shared*: 24 retained
nodes cite into it and both cones need all 18.

## 3. The mathematics, in four blocks

The name "uniformization ladder" undersells it: the closure is four different
developments.

**(A) The dictionary and the uniformization itself (~2,900 lines).**
`Definitions/Def_PeriodPair_Uniformization.lean` (144 lines, 20 declarations) defines
`weierstrassCurve L` from the lattice invariants `g₂, g₃`, the ℘-map
`toPoint : ℂ → E`, `IsUniformization`, `jLattice = 1728·g₂³/(g₂³ − 27g₃²)`,
`JSurjective`, `ofTau`, `scale`, `sublatticeIndex`, `sublatticeQuotient`. On top of it:
`isUniformization_toPoint` (1,493 — that `ℂ/Λ ≅ E(ℂ)` through the ℘-map is a group
isomorphism: the classical uniformization/Abel theorem) and `jLattice_surjective`
(1,054 — that every complex `j` is realised by a lattice, proved through the
`E₄³ − E₆²` arithmetic and q-expansions: `kw_riemannZeta_six`, `kw_G_ofTau_eq`,
`kw_g₃_ofTau`, `discriminant_ne_zero` 542, `jLattice_ofTau` 210). **These two are the
mathematically expensive items and both are essential.**

**(B) The analytic seam (~2,700 lines).**
`exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint` (2,673): given a
finite separable `ι` between the function fields of two `L.weierstrassCurve`s, there is
a differentiable `F : ℂ → ℂ` with `F 0 ∈ L'.lattice` and
`L'.toPoint (F z) = pointMapOfPushforward ι … (L.toPoint z)`. Its `S_` file carries the
`KwD5BetweenCurves*` family — holomorphic lifts (`KwD5BetweenCurvesHoloLift`,
`…CocountableHoloLift`, `…IndexDual`, `…KerQuotEquivBC`) — i.e. the analytic
compatibility between the complex uniformization and the algebraic pushforward. This
is the single largest node in the slice and the least "classical-textbook" of them.

**(C) The lattice/isogeny-index arithmetic (~4,000 lines).**
`sublatticeIndex`/`sublatticeQuotient`, `card_torsionBy_latticeQuotient`,
`kw_surgehgf4_hID_dualIndex_eq`, `ker_toPointHom`, `toPointHom`,
`exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` (848),
`eval_E4_cube_div_discriminant_{smul,coset}_eq_zero` (367 + 85),
`Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one` (88). Mostly
transcription over the pin's own `ℤ`-lattice API.

**(D) Field descent and base change (~4,760 lines) — not `PeriodPair` at all.**
`exists_intermediateField_countable_map_eq_and_finrankAlong_eq` (2,684),
`exists_algHom_functionField_baseChange_finrankAlong_eq` (1,336),
`nonempty_functionField_algEquiv_of_variableChange` (744). These are generic
`WeierstrassCurve`/`AlgebraicCurve` statements about countability, intermediate fields,
`baseChange` and `finrankAlong`. They are the *largest single item* in the closure and
have nothing to do with ℂ-uniformization; they may well be reusable by other frontier
work.

## 4. What mathlib already has

mathlib `v4.34.0`'s `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`
supplies `PeriodPair` itself, `lattice`, `mem_lattice`,
`mul_ω₁_add_mul_ω₂_mem_lattice`, `ω₁_div_two_notMem_lattice`, `weierstrassP`, `℘'`,
`differentiableOn_weierstrassP`, `analyticOnNhd_weierstrassP`, `order_weierstrassP`.

It has **no** `toPoint`, `IsUniformization`, `jLattice`, `JSurjective`,
`sublatticeIndex`, `weierstrassCurve` or `scale` — those are exactly the pin's 144-line
`Def_PeriodPair_Uniformization`. So the *dictionary* is cheap to land; the theorems
over it are not.

## 5. Reuse and duplication hazards

The port already holds a surprising amount of adjacent material, and none of it is
visible to the name-anchored substitution test:

- `ModularForms/WeightOne/Defs/PeriodPair.lean` (98 lines) — `periodPairOfTau`,
  `smulPeriodPair`, the `℘`-homogeneity under scaling. Written by the WeightOne
  rectification precisely to stop this prelude being copied per consumer.
- `ModularForms/WeightOne/LevelOneHauptmodul.lean` — real ℘-analysis:
  `weierstrassP_eq_tsum_tsum`, `hasSum_weierstrassP_prod`, `summable_weierstrassP_row`,
  and a `PeriodPair` scaling law.
- `ModularForms/WeightOne/Defs/PTorsion.lean` — `weierstrassP_torsion`.
- `ModularCurve/Defs/PrimCosetReps.lean`, `ModularCurve/Gamma0Index.lean` — the
  `primCosetReps` side.
- Plus the whole ported `ModularForm`/`EisensteinSeries`/`CuspForm` analytic layer,
  which the `KwD5BetweenCurves*` block and the `E4³ − E6²` route both touch.

The Deligne–Serre scout's warning applies verbatim: the port's cautionary tale is the
**WeightOne rectification** (7,242 removable lines in 12 modules) caused by
transcribing this cone package-by-package, and this slice "overlaps that material
(`CuspForm`, `ModularForm`, `EisensteinSeries`, `PeriodPair`), so the same failure mode
is available"
([../../../studies/deligne-serre-weight-one-scout.md](../../../studies/deligne-serre-weight-one-scout.md)
§5). Any plan must run `port_advise` with a **statement** check (not just a name
lookup) over the WeightOne/E-S modules before pricing a single declaration.

## 6. The math-first scout

The scout has run on the pin's `S_` files. Its findings:

**The core is concrete ℂ-analysis, not uniformization theory.**
`isUniformization_toPoint`, `discriminant_ne_zero` and `jLattice_surjective` import
`Mathlib`, the 144-line `Def_PeriodPair_Uniformization` and each other — nothing else.
The group isomorphism `ℂ/Λ ≅ E(ℂ)` is proved by ℘-analysis on mathlib's `PeriodPair`:
surjectivity and the kernel from the order of ℘ (`kw_toPoint_surjective`,
`kw_toPoint_eq_zero_iff`), the addition theorem from a Liouville lemma for elliptic
functions (`kw_elliptic_Liouville_zero`) plus removable singularities and a
generic-perturbation argument (`kw_toPoint_add`), with the chord-tangent law supplied by
`Affine.addX`/`addY`/`slope`. mathlib v4.34 has **no** Riemann-surface theory, no
Riemann existence or mapping, and no uniformization theorem, and the pin builds none.
The only topology anywhere in the slice is in the seam node, which proves
`IsCoveringMap (ℂ → ℂ/Λ)` and applies the covering-space lifting theorem
(`existsUnique_continuousMap_lifts`) — mathlib's covering-map API, not Riemann surfaces.

**The reusable half is already in the port.** mathlib supplies the ℘ primitive — 96
declarations: the `weierstrassPExcept`/series API, order, meromorphy, the ODE
`derivWeierstrassP_sq` — exactly the infrastructure the pin's 1,493 lines elaborate. The
port supplies `WeightOne/Defs/PeriodPair.lean` (the pin's `ofTau`/`scale`/homogeneity
prelude, verbatim) and the modular-forms layer `JqAnalyticModel.lean`/`Hauptmodul.lean`
(`E₄`, `Δ`, `jq`, `E4_cube_div_discriminant_smul`, the q-expansion principle).

**The gate's 17-node closure, grouped by role** (the subject's own branch order is
§2.1):

- **U — uniformization (144 + 1,493 pin lines).** The dictionary plus
  `isUniformization_toPoint`. Needs Mathlib only; reuses mathlib's ℘ API.
- **J — the `j`-line (542 + 210 + 1,054).** `discriminant_ne_zero`, `jLattice_ofTau`,
  `jLattice_surjective`. Needs Mathlib only; reuses the ported `E₄`/`Δ`/`j` layer.
- **S — seam and index (≈6,900).** `exists_differentiable_toPoint_comp_…` (2,673), the
  two `exists_scale_lattice_…` (2,021 / 978),
  `exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` (848), the small
  `eval_E4_cube_div_discriminant_*` (367 / 85),
  `SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one` (88),
  `eval_jLattice_eq_zero_of_isAddCyclic` (25), `IsAddCyclic.of_squarefree_natCard` (14).
  Needs the ported place dictionary.
- **D — descent (2,684 + 1,336 + 744).** The three `WeierstrassCurve.*` base-change
  nodes; generic field theory, not `PeriodPair`.

**The uniformization core is conditional, so it does not need the `j`-line row.**
`isUniformization_toPoint` takes `h : L.DiscriminantNeZero` as an argument, and the pin's
three components are all parametric in `h`; only its internal packaging calls the theorem
`discriminant_ne_zero`. A port can prove the conjunction from `h` directly, so the
uniformization is self-contained analysis and the `E₄³ − E₆²` computation stays in its own
node — still inside P-SET-1, because the consumers need the unconditional discriminant.

**What the U work order still has to settle.**

1. **Shortening against v4.34.** The pin builds its own `kw_addCoreE`/`kw_addBridge*`
   scaffolding around ℘; check whether mathlib's
   `weierstrassPExcept`/`weierstrassPSeries` API replaces part of it — the one place
   the transcribed count can fall.
2. **Public surface.** The `S_` files are silos; produce the wrapper names the checker
   needs for U, as V3/V4 did.
3. **The `D5` seam.** Before S is scoped, enumerate which `KwD5BetweenCurves*` lemmas
   the 2,021-line node calls; the ported place dictionary may already carry part of the
   transport.
4. **The moduli-place alternative cannot kill the subject** (§2.1). The pin carries a
   *moduli-place* layer — `Def_ModularCurve_ModuliPoint.lean` (162;
   `Gamma0Pair`/`ModuliPoint`), `Def_ModularCurve_ModuliPointMap.lean` (159),
   `Def_ModularCurve_ModuliPlace.lean` (681; `IsModuliPlaceOf`, `moduliPlaceOfPoint`,
   `moduliPlace`) — describing what it means for a place of the modular function field
   to *be* the moduli point of a curve with level structure, over a general field and
   with no `℘`; 41 `moduliPlace`/`ModuliPoint` nodes / 17,260 unported lines are already
   demanded by the FLT root. If `aeval_j_diag_eq_zero_of_finrankAlong_eq` can be
   re-derived by specialization through `moduliPlace` instead of by descending to ℂ, the
   saving is the gate's own marginal — **4 nodes / 4,681 lines** — not the subject: the
   other 13 gate-closure nodes and the 9 further `PeriodPair` nodes stay demanded through
   24 other consumers. It remains the pin's proof-shape question, and the mismatch should
   be priced first: `ModuliPoint N K` is a point of order *exactly* `N` (a Γ₀(N) level
   structure), whereas `aeval_j_diag` starts from an `IsogenyEndDatum` of degree `N` whose
   `N` comes from a negative-discriminant binary quadratic form. See
   [../../../math/024-uniformization-versus-modular-functions.md](../../../math/024-uniformization-versus-modular-functions.md)
   §8.4.

The scout's output is a corrected estimate and a go/no-go, not a work order. Playbook
§2.6: a scout that shows the pin's proof transcribes unchanged converts "new
mathematics" into "transcription"; one that shows a route is missing kills it outright.

## 7. Options, and the recommendation

- **(a) The whole subject, as its own effort.** 18 nodes / 12,265 raw lines, ≈8.5k net
  new after dedup (§2.2), six branches. Precedent size: the Deligne–Serre effort was
  15,200 written lines over 54 targets and nine sets — so this is one medium effort,
  not a tail.
- **(b) A minimized path.** Only what the two cones need — but §2.1 shows they need all
  18, so this collapses into (a). Neither the moduli-place route nor a C′-style supply
  of the gate removes the subject.
- **(c) Park it.** It is ~0.1% of the port's remaining lines and blocks nothing
  half-built — but it is a *shared* prerequisite with 24 rewire obligations, so parking
  is now a scheduling choice, not a scoping one.
- **(d) Open with the two hubs.** P-SET-1 = the dictionary + `discriminant_ne_zero` +
  `isUniformization_toPoint`; then the `j`-line; then the isogeny/index branch once the
  place dictionary is in place; the `rationalHomSet` and torsion columns last.

**Recommendation: (a), opened by (d).** Port the subject; set the first work order as
P-SET-1, the uniformization core:

| node | pin lines | why it is first |
|---|---:|---|
| `Def_PeriodPair_Uniformization` | 144 | the dictionary; mathlib has no `toPoint`, `IsUniformization`, `jLattice`, `JSurjective`, `sublatticeIndex` |
| `PeriodPair.discriminant_ne_zero` | 542 | the subject's hub — 9 in-subject consumers; reuses the ported `E₄`/`Δ` layer |
| `PeriodPair.isUniformization_toPoint` | 1,493 | `ℂ/Λ ≅ E(ℂ)`; the one piece mathlib lacks outright |

They are the only `PeriodPair` nodes with no unported prerequisite and the two that
unblock everything else, and P-SET-1 is new-file-only (playbook §3.5), so it cascades
nowhere. The `isUniformization_toPoint` statement takes `h : L.DiscriminantNeZero`, so it
can be proved parametrically and does not *depend* on the middle row; that row is in the
set because the consumers need the unconditional discriminant anyway, and it is cheap.
Carry §6 items 1–2 as the set's stop conditions, and leave the `D5` and moduli-place
questions (§6 items 3–4) to the branch scoping they belong to.

**Ownership.** If it is done, it should be planned *with* the Eichler–Shimura and
WeightOne efforts — the scout puts `PeriodPair` at 9 nodes / 9,836 shared-uniformisation
lines in the E-S driver's closure, and the port's adjacent material is theirs. Filing
it as a Velu/Phase-D tail would repeat the package-by-package mistake the WeightOne
rectification already paid for.

## 8. Reproduce

```bash
cd tools/deps
python3 port_advise.py --target 'P2M/Sol/S_PeriodPair_*' --json build/v5_pp_advise.json
python3 port_plan.py  --json build/v5_pp_advise.json --json-out build/v5_pp_plan.json

python3 port_advise.py --nodes \
  WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq \
  --json build/v5_advise.json

# §2.1, the gap structure: the gate's marginal against the subject's
python3 prune.py --scenario none --remove aeval_j_diag     # 4 nodes / 4,681 lines
python3 prune.py --scenario none --remove 'PeriodPair.'     # 18 nodes / 12,265; 24 obligations

# the ucl of the gating node, and the per-called-node attribution
python3 - <<'PY'
import frontier
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
q = 'WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq'
i = pay.pid(q)
un = [n for n in fr.closure(i) if n not in front and n != i]
print(sum(pay.lines(n) for n in un), pay.lines(i), q)
for n in sorted(un, key=lambda n: -pay.lines(n)):
    print('   ', pay.lines(n), pay.qual(n))
PY
```

The 2026-10-06 runs are in `tools/deps/build/v5_{pp_advise,pp_plan,advise}.{txt,json}`
(untracked). Re-pin before re-measuring.
