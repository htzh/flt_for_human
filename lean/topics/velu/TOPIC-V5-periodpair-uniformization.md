# V5 (scoping) — the `PeriodPair` uniformization slice

**Status: scouting complete, 2026-10-06. No work order, no set, no agent.** This document
answers one question — *how big is the slice that gates the last Phase D node, and is
the work actually that large?* — and records the math-first scout (§6) that must precede
any port. It is not a work order; nothing here has been dispatched. Triggered by
[TOPIC-V4-isogeny-kernel-rigidity.md](TOPIC-V4-isogeny-kernel-rigidity.md) §9 ("the one
remaining Phase D item"), whose prerequisite is **not** in the Deligne–Serre cone and
not in this column. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib
`v4.34.0`. Measurements from `tools/deps/port_advise.py`, `port_plan.py`,
`frontier.py` (§8).

**Answer in one line.** It is genuinely as large as it looks — the gating node's
unported closure is **17 nodes / 15,179 pin lines**, and the two hard classical
theorems (complex uniformization, surjectivity of `j`) plus a 2,673-line analytic seam
are *on* the path, not inlined prelude. The scout (§6) then shows the uniformization core
is the one piece mathlib lacks outright, is Mathlib-only, and can open the slice as set
U (§7(d)).

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
Unlike V2 and V3, there is no large inlined prelude to discount.

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
`mem_of_isRoot_map_j_of_transcendental`). That is the cone of the unported D-S capstone,
not of the shipped `DeligneSerre.*` slice; the gate is shared between the Mazur chain
and that capstone, and the "Mazur gate" heading of
[TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md) §2.2 records its shortest path, not an
exclusive owner. It is also *not urgent*: every one of those consumers is unported, so
it blocks no half-finished work.

## 2. The slice at full width

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

**Context.** The port's unported frontier is **760 nodes / 372,383 pin lines**. This
slice is therefore ~4% of what remains, and ~2% of it (15,179 lines on-path) is what
the single node needs.

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

**The 17-node closure factors into four sets.**

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

**U is conditional, so it does not need J.** `isUniformization_toPoint` takes
`h : L.DiscriminantNeZero` as an argument, and the pin's three components are all
parametric in `h`; only its internal packaging calls the theorem `discriminant_ne_zero`.
A port can prove the conjunction from `h` directly, so the uniformization is
self-contained analysis and the `E₄³ − E₆²` computation stays inside J.

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
4. **The moduli-place alternative** (still the only thing that can kill §7(a)). The pin
   carries an ≈1,000-line *moduli-place* layer — `Def_ModularCurve_ModuliPoint.lean`
   (162; `Gamma0Pair`/`ModuliPoint`), `Def_ModularCurve_ModuliPointMap.lean` (159),
   `Def_ModularCurve_ModuliPlace.lean` (681; `IsModuliPlaceOf`, `moduliPlaceOfPoint`,
   `moduliPlace`) — describing what it means for a place of the modular function field
   to *be* the moduli point of a curve with level structure, over a general field and
   with no `℘`. If `aeval_j_diag_eq_zero_of_finrankAlong_eq` can be re-derived by
   specialization through `moduliPlace` instead of by descending to ℂ, the 15,179-line
   closure drops to ≈1 k of definitions plus one comparison theorem. Price the mismatch
   first: `ModuliPoint N K` is a point of order *exactly* `N` (a Γ₀(N) level structure),
   whereas `aeval_j_diag` starts from an `IsogenyEndDatum` of degree `N` whose `N` comes
   from a negative-discriminant binary quadratic form. See
   [../../../math/024-uniformization-versus-modular-functions.md](../../../math/024-uniformization-versus-modular-functions.md)
   §8.4.

The scout's output is a corrected estimate and a go/no-go, not a work order. Playbook
§2.6: a scout that shows the pin's proof transcribes unchanged converts "new
mathematics" into "transcription"; one that shows a route is missing kills it outright.

## 7. Options, and the recommendation

- **(a) Full slice as its own effort.** 18 nodes, ~8.5k net-new lines, four sets of
  which one (D) is not `PeriodPair`. Precedent size: the Deligne–Serre effort was
  15,200 written lines over 54 targets and nine sets — so this is one medium effort,
  not a tail.
- **(b) A minimized path.** Take only the closure of the gating node (15,179 lines) —
  sets U, J and S — once the remaining scout items in §6 land. Likely saving: the
  4,764 lines of D, plus whatever the moduli-place route (if it exists) removes from S.
- **(c) Park it.** It is ~4% of the remaining frontier and blocks nothing that is
  half-built.
- **(d) Open with set U, then J.** Two new-file sets with no unported prerequisite: U
  is the uniformization theorem and J the `j`-line, both Mathlib-only, and J reuses the
  ported modular-forms layer. S stays parked behind the place dictionary; D goes to
  whichever effort needs its base-change first.

**Recommendation: (d).** The scout in §6 separates the genuinely new mathematics from
the transcription. U is the only piece mathlib lacks outright; it is conditional on `h`
and so pulls in neither the modular-forms nor the place layer, and it is the map every
other set consumes; J is cheap next to it. Enter the slice through U, not through the
15,179-line boundary figure: scope U as its own new-file set with the §6 items 1–2 as
its stop conditions, and leave the `D5` and moduli-place questions (§6 items 3–4) to the
S scoping they belong to.

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
