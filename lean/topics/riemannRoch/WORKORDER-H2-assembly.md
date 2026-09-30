# Work order — H2: assembly, the Weil canonical divisor, and the `H¹` identification

**Status: DISPATCHED (2026-09-29).** H1a and H1b are reviewed green (checker
2823/0/0). Boilerplate and build/verification clauses are `WORKORDER-H1a-index.md`
§4–§5; only the differences are stated here. Plan: `PLAN.md` §2.

## 0. Scope

The thin layer that turns the engine into the API the 104 forward-cone nodes
consume: the curve-level wrappers, the `H¹` identification, and Riemann–Roch with
the cohomological genus.

**Targets** (all from PORTING-RR §1):
| target | pin source |
|---|---|
| `indexOfSpecialty_eq_finrank_H1` | `S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean` (126 ln) |
| `exists_genus_riemannIndex_of_isCurveOver` | `S_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean` (60) |
| `weilDifferentialRankOne_of_isCurveOver` | `S_AlgebraicCurve_weilDifferentialRankOne_of_isCurveOver.lean` (56) |
| `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists` | `S_AlgebraicCurve_weilDualityAdelic_….lean` (55) |
| `exists_weilCanonical_riemannRoch` | `S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean` (288) |
| `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists` | `S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_….lean` (33) |

Union prelude to home here: 21 names / 366 lines (`rr_homes.txt` §H2). The
load-bearing ones are the two-carrier bridge: `adeleSpaceEquivRepartitions`,
`adeleSpace_eq_restrictScalars_repartitions`, `mem_adeleSpace_iff_mem_repartitions`,
`mem_repartitionsOf_iff_coe_mem_adeleBdd`, `mem_repartitions_of_mem_adeleBdd`,
`boundedFamilies`, `mem_principalRepartitions_iff_coe_mem_globalSub` (the
`indexOfSpecialty` adelic carrier ↔ `H1` repartition carrier), plus the effective-
divisor lemmas `ell_add_eq_of_ord_eq`, `degree_pos_of_nonneg_of_ne_zero`,
`degree_lt_of_lt`, `degree_eq_zero_of_ord_eq`, `inv_mem_lSpace`, `self_mem_lSpace_neg`,
`mem_omegaSpace_sup`, `adeleBdd_sup_le`, `weilDifferentialRankOne_of_stichtenothGenusExists`,
`indexOfSpecialty_eq_ell_sub_of_rankOne_max`.

**Explicitly not this set:** H1a/H1b, H3's differentials. Definitions come from Set
D; `FunctionFieldRiemannRoch`/`WeilDualityAdelic`/`WeilDuality` come from Set D's
`Defs/RiemannRochRows.lean`.

## 1. Deliverable

`FLTForHuman/AlgebraicCurve/RiemannRoch/Assembly.lean`

- namespace `AlgebraicCurve`; imports Set D (`Defs.{RiemannRochRows,AdelicIndex,Repartitions,CanonicalDivisor,IsCurveOver,PoleDivisorPackage}`) and `Genus.{Index,Stichtenoth}`.
- `main` (135 lines, in the `weilCanonical` file) is the proof body of
  `exists_weilCanonical_riemannRoch` — keep it `private`, not public.
- `exists_genus_riemannIndex_of_stichtenothGenusExists_port` ≡ the H1a target of
  the same name (collapse; do not duplicate); `exists_linearEquiv_…_zero'` is H3's.

## 2. Route and risk

- The `indexOfSpecialty_eq_finrank_H1` proof is the two-carrier bridge: it is the
  one place the adelic quotient and the repartition quotient must be compared. Do
  not restate either carrier; prove the equivalences at the pin's names. If a
  needed identification is missing, stop and report rather than adding a carrier.
- `exists_weilCanonical_riemannRoch` is RR with `genusFF`; it consumes
  `indexOfSpecialty_eq_finrank_H1` and `weilDifferentialRankOne_of_isCurveOver`.
- **Missing curve-level wrapper (landed here).** The pin's
  `stichtenothGenusExists_of_isCurveOver`
  (`S_…_exists_genus_riemannIndex_of_isCurveOver.lean:25`,
  `stichtenothGenusExists_of_isCurveOver_port`) was left unlanded by H1a/H1b and
  `exists_genus_riemannIndex_of_isCurveOver` needs it. Land it as a
  port-named `private` helper (its name is invented, so it is outside the checked
  surface) and record it in the friction log.
- **Infrastructure heads-up from H1b.** The port has no public
  `Place.sum_ramificationIndex_mul_inertiaDeg`/`SumRamificationInertia`; H1b's
  bridging instance is `private` to `Genus/Stichtenoth.lean` and not exported. If a
  target here needs it for a tower extension, re-provide a local `private` instance
  or stop and report — do not edit the frozen `Stichtenoth.lean`.
- `exists_genus_riemannIndex_of_stichtenothGenusExists_port` ≡ the H1a target
  `exists_genus_riemannIndex_of_stichtenothGenusExists` (collapsed; do not
  duplicate); `exists_linearEquiv_…_zero'` is H3's.

## 3. Verification

Checker `SOURCES` += the six pin `S_…` files (after their `Theorems/Thm_*`
wrappers) and `PORT_FILES` += `FLTForHuman/AlgebraicCurve/RiemannRoch/Assembly.lean`.
`#print axioms` on all six headlines. Build/file-done clause as H1a §4.

## Appendix

`tools/deps/build/rr_homes.txt` §H2 (21 rows).
