# SET-AF105 — a plan, not a cut (prepared while SET-AF104 lands)

**Status: PLANNING NOTE (2026-11-26).** Nothing here is a commitment: the cut is decided after
SET-AF104 closes (E is still in hand) and the shelf is re-read on the landed tree, per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) §0. What it
carries is the read that the next scoping pass starts from, the candidate stories with their measured
silo / premises / definition layer, and the one definition-layer item that is the manager's before any
order can be written.

## 0. The read — post-SET-AF104 (A–D landed, E's scaffold on disk)

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af105_pre.json
```

| figure | before AF104 | after SET-AF104 (all six) | delta |
|---|---:|---:|---:|
| `needed [F terminal]` | 325 / 176,086 | **314 / 170,417** | −11 nodes / −5,669 lines |
| ready rows | 29 / 9,804 | **22 / 6,379** | −7 rows |
| leaves | 18 / 15,127 | 18 / 15,127 | — |
| withheld (FR-0044) | 4 / 831 | 4 / 831 | — |

The `needed` delta is **exactly AF104's cut** (−11 rows, −5,669 lines), which is the check that every
row of the set left the cone. The ready block moved −7 / −3,425 because four rows *became* ready:
**`AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion`
(1,381) — order C's consumer**,
`AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType`
(435) and `AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact` (88) — order
B's and A's consumers — and
`ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC` (340),
order E's consumer once E lands. The leaves block is untouched again: AF104 took no leaves, and the
leaves are still `M4aTorus.completedRayL_fe` (12,126) plus 17 rows / 3,001.

**These are the post-SET-AF104 figures, all six modules landed** — re-read after E's module built and
*identical* to the A–D read (314 / 170,417, ready 22 / 6,379), because E's three rows already read as
ported while its scaffold was only a `sorry`-bodied headline on disk (the scoping doc's caveat), so
they were inside the −11 / −5,669 from the start. Nothing is left to correct.

One measured detail about the correction list, worth carrying: the 21 `--unport` false ported markers
move `needed` by **exactly one node / 75 lines** — the uncorrected read is 313 / 170,342 — and that one
node is `ModularCurve.ModularPolynomialData.eq_all`, the MD-005 row. So on this shelf the correction is
not cosmetic but it is narrow, and quoting an uncorrected figure understates the cone by 75 lines.

## 1. The shelf's head is still consumers of the last two sets

| silo | prem | lev | row | what it is |
|---:|---:|---:|---|---|
| 1,381 | 19 | 2 | `AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion` | **AF104C's consumer**: the shell recursion turns the unfolded `s`-part integral into an Euler *product* |
| 951 | 8 | 1 | `ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` | the peaked-auxiliary integrality of the `slash` `q`-expansion coefficients |
| 604 | 3 | 1 | `AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction` | the `P¹` degree formula from a reduction |
| 495 | 3 | 1 | `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | the semisimple-representation criterion (AF103 §5's deferral) |
| 435 | 12 | 2 | `AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType` | **AF104B's consumer**: a level-spherical `rightConv` eigenvector |
| 407 | 3 | 2 | `ModularCurve.StarBank.hassePolyDescent` | the Hasse-derivative polynomial descent |
| 370 | 6 | 6 | `ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem` | the complex place dictionary's point identification (deferred twice) |
| 340 | 15 | 3 | `ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_…` | **AF104E's consumer**: integrality from a regular differential |
| 318 | 10 | 4 | `ModularCurve.card_quotient_gamma0_le_dedekindPsi` | the Γ₀ index vs `dedekindPsi` bound |
| 300 | 3 | 4 | `AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring` | a retraction of the regular-prolongation map |
| 221 | 1 | 1 | `AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic` | the adjoin criterion for a regular prolongation |
| 101 + 22 + 22 + 13 | 1 | — | the four `TateCurve` ready rows | `sOne_eq_tsum_xfun`, `pointX/pointY_zpow_mul`, `defectCoeff_zero` |
| 88 | 2 | 4 | `AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact` | **AF104A/B's consumer**: the cut projector |
| 75 | 2 | 8 | `ModularCurve.ModularPolynomialData.eq_all` | the modular-polynomial data (the MD-005 row) |
| 75 | 1 | 2 | `ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one` | Krull dimension vs transcendence degree |
| 59 | 2 | 5 | `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` | the place map at good reduction |
| 42 | 2 | 1 | `ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem` | a residue-nonvanishing polynomial |
| 36 | 2 | 3 | `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | the FR-0299 row |
| 24 | 1 | 6 | `ModularCurve.rep_tateModule_jOne_comm` | the Tate-module representation commutes |

## 2. Candidate stories

Grouped by subject, each with the silo / premises / definition layer measured from the pin graph
(`lean/tmp/af105/recon.json`), and the home a cut would give it.

**S1 — the Euler product (AF104C's payoff), 1,381 silo, 19 premises.** The `hasProd` identity: for a
Hecke eigenfunction pair `x, y` with the recursion hypothesis `_hP`, the quotient integral
`quotientIntegral` is the `s`-part integral times a product over the places outside `S`. Definition
layer: **7 pin `Def_` modules, one of them is the set's manager item, and it is confirmed missing** —
`Def_AutomorphicForm_HeckeEigenfunction` (120 pin lines: `rightTranslationEmbed`,
`uniformizerIdele`, `levelRT`, `IsHeckeEigenfunctionOf`, `agreesAwayFromFinite_of_level_eq`,
`isHeckeEigenfunctionOf_zero_inhabitant`) is **not in the port**: `rg IsHeckeEigenfunctionOf` over
`lean/FLTForHuman` returns nothing, the port has `isHeckeCosetEigenfunctionAt` only as a fragment of a
long theorem *name* in `Adelic/RightConvStructurePreservation.lean` (no such declaration), and the pin's
`S_` file names `IsHeckeEigenfunctionOf`/`rightTranslationEmbed`/`uniformizerIdele`/`levelRT`/
`agreesAwayFromFinite` **20 times**. So S1 is a **definition-layer-first** story: the port needs that
120-line `Definitions` module (home: `AutomorphicForm/Adelic/HeckeEigenfunction.lean`, or folded into
`RightConvStructurePreservation` if the notion is the same one generalised), ported by the manager
before any S1 order is written. This is the FR-0049 trap exactly — the row reads ready because its
statement's vocabulary is not a graph premise.
Home: `AutomorphicForm/Adelic/RankinSelbergEulerProduct.lean` (flat `Adelic/` rankin-selberg family).

**S2 — the cuspidal constituent's level-spherical eigenvectors, 523 silo, 12 + 2 premises.**
`exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType` (435) together with
`exists_idempotent_cutProjector_of_isCompact` (88): the two rows AF104's projector/density work exists
to feed. Both are consumers of `Cusp/{SpectrumDensity,ArchTypeProjector}.lean`, so they must sit above
those homes. Home: `Cusp/LevelSphericalEigenvector.lean` (or the `Cusp/Constituent*` family).

**S3 — places and regular prolongations over a constant field extension, 1,184 silo.**
`ord_placeInfty_eq_…_of_reduction` (604) + `exists_regularProlongation_retraction_…` (300) +
`RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic` (221) +
`exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` (59). The `AlgebraicCurve` story the last
three sets kept pushing forward, and the one SET-AF103 §5 named as "a `RegularProlongation` set should
take it whole". Def layer: `AlgebraicCurve_RegularProlongation` (ported), `RatFunc*`, `DivisorClassGroup`.

**S4 — the complex place dictionary and `X₁` integrality, 710 silo.**
`ComplexPlaceDictionaryOf.exists_pt_eq_of_mem` (370, deferred by AF103 and AF104) +
`isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_…` (340, AF104E's consumer). The
dictionary's own remainder plus the integrality criterion — one subject (identifying the points of the
complex place dictionary, and recognising integrality from a differential).

**S5 — the Galois-representation semisimplicity criterion, 615 silo.**
`GaloisRep.exists_isSemisimpleRepresentation_…` (495) plus the two `ValuationSubring` leaves AF103
deferred to a `GaloisRep`-layer order (`IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83,
`charP_residueField_of_liesOverPrime` 37) — their vocabulary `A.LiesOverPrime ℓ` lives in
`GaloisRep/Defs/`, which is exactly why they were not taken in a `FieldTheory` module.

**S6 — the modular polynomial and the `Γ₀` index, 860 silo.**
`StarBank.hassePolyDescent` (407) + `card_quotient_gamma0_le_dedekindPsi` (318) +
`ModularPolynomialData.eq_all` (75) + `exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36) +
`rep_tateModule_jOne_comm` (24). Two sub-subjects (the Hasse-descent/modular-polynomial data, and the
`Γ₀`-index vs `dedekindPsi` count with its `q`-expansion companion); a cut would split it by subject
rather than keep it as one order.

**S7 — the peaked-auxiliary integrality, 951 silo** — one row, its own module: a `ModularForm` story
(`ModularForms/{FrickeReciprocity,IsArithmeticQExpansion,LevelOneSlash}.lean` are its premises), and
like S1 a set of its own.

**Leaves worth a later set** (not this one): `TateCurve.point_mul_eq_add_of_norm_{le,eq}_one`
(471 + 247 — the Tate curve's points law, with its deferred definition layer), the `NumberField.*`
ten rows (1,600), `WeierstrassCurve.{stepCurve_stepSubgroup_two_eq}` + `…veluQuotient…` (425), and
`M4aTorus.completedRayL_fe` (12,126, an analytic class-field-theory subject).

## 3. A candidate cut (to be re-measured, not to be taken as the plan)

Three stories that are *consumers of the last two sets* and one that is a subject in its own right,
≈ 4,400 silo — deliberately under AF104's 5,669 because two of its orders are single rows with a large
premise count and a definition-layer question:

| order | story | rows | silo | module |
|---|---|---:|---:|---|
| A | the Euler product | 1 | 1,381 | `AutomorphicForm/Adelic/RankinSelbergEulerProduct.lean` (new) |
| B | level-spherical eigenvectors and the cut projector | 2 | 523 | `AutomorphicForm/Adelic/Cusp/LevelSphericalEigenvector.lean` (new) |
| C | places and regular prolongations | 4 | 1,184 | `AlgebraicCurve/RegularProlongation/Reduction.lean` (new) |
| D | the Galois semisimplicity criterion | 3 | 615 | `GaloisRep/SemisimpleCriterion.lean` + the two `LiesOverPrime` rows in place |
| E | the complex place dictionary and `X₁` integrality | 2 | 710 | `ModularCurve/ComplexPlaceDictionaryPoint.lean` (new) + `X1/IntegralityDifferential.lean` |
| **total** | | **12** | **4,413** | |

S6 and S7 stay on the shelf: S6 splits by subject (two orders of ~400 each, not worth a dispatch on
their own) and S7 is one 951-line row whose premise set is the whole modular-forms integrality
machinery — the same shape as AF104C, so it wants its own order and its own wall time, not a shared
set.

## 4. What must be done before the cut is real

1. **E lands and the shelf is re-read** (§0's corrected figures).
2. **S1's definition-layer question answered** (§2): substitution or a `Def_AutomorphicForm_
   HeckeEigenfunction` port. If it is a module, it is the manager's, and it precedes every S1 order.
3. **`port_advise --with-defs` on each story**, since this shelf's head is rows whose statement
   vocabulary comes from `Definitions/Def_*` modules rather than from graph premises (FR-0049).
4. **The two "deferred twice" rows** (`ComplexPlaceDictionaryOf.exists_pt_eq_of_mem`, the `_pkg`-heavy
   `StarBank` row) get their own pricing pass — a row that has been deferred twice is usually deferred
   for a reason that shows up in its first 20 pin lines, not in its silo.
