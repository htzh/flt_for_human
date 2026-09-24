# SET-M3 — the Laurent glue and relative degree, and the roof (m7, m9)

**Status (2026-09-23): finalized against the landed SET-M2 modules; ready to
run.** SET-M2 passed review (checker **1,198 identical, 0 mismatched, 0 missing**,
`lake build` 4,100 jobs green, consumer Zones A–E/G at 0 errors/0 warnings); the
review is `../logs/mc-port.md` §Review of SET-M2. This is the run brief for the
**third** coding set of the `ModularCurve` Hecke-layer effort
([PORTING-MC.md](../PORTING-MC.md)). It authorizes exactly two topics:

| order | work order | object | pin | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-m7-laurent-relfinrank.md](TOPIC-m7-laurent-relfinrank.md) | the Laurent/`coeffEmb` glue and the two relative-degree theorems (M4) | 10 nodes, 1,402 raw / 1,061 content | 700–950 | m1 (two nodes delivered early), m2, m6 |
| 2 | [TOPIC-m9-roof-degree.md](TOPIC-m9-roof-degree.md) | the roof generation and the diagonal degree (M6) | 2 nodes, 1,181 raw / 859 content | 550–750 | m7 |

m7 runs first: m9's `finrankAlong_towerSubstBar_comp_heckeAlphaBar` consumes
m7's `relfinrank_qExpand_full`/`relfinrank_laurentBaseChange`, and
`heckeRoof_adjoin_range_union_eq_top` consumes m7's `coeffEmb_jqN` and
`laurentBaseChange_modularFunctionField` plus m6's `isIntegral_jqNModC_mul`.

**Why these two together.** They are the last assembly before the operator inputs:
m9's roof is one of the two hypotheses `heckeExchangeAt_of_WEX` takes, and its
diagonal degree is the other. Both are mostly *assembly over the ported
`TS`/slot prelude* — the pin repeats a ~370-raw-line prelude at the head of each
of these files and of m7's `relfinrank_qExpand_full`, and the port already
publishes every piece of it (`Defs/TS.lean`, `Defs/PhiAtSlot.lean`,
`PhiSlotRoots.lean`, `Defs/Cyclotomic.lean`, `Defs/Twist.lean`). The set's
deliverable is the **reduction to the genuinely new blocks**:
`finrank_adjoin_jq_of_subset_range_qExpand{,_of_mem}` (m7), `relfinrank_eq`'s
`TransportDev` block (m7), `mem_range_towerInclBar_iff`/`laurentBaseChange_adjoin_pair`
+ the roof argument (m9), and `fieldRange_heckeBetaBar`/`finrankAlong_heckeBetaBar`/
`finrankAlong_towerSubstBar_roof` (m9).

## 0. What SET-M1/SET-M2 hand over (to be confirmed at review)

- m1's `Defs/{HeckeOperator,DegeneracyTower,HeckeTotal,HeckeModule,ArithmeticGalois}.lean`
  — including the public `laurentBaseChange_mono` and
  `qExpand_mem_laurentBaseChange` (two M4 nodes delivered early).
- m2's `Defs/{GeometricBaseChange,QAdicPlace,CuspidalClass,AtkinLehner,ModularUnit,JqCoeff}.lean`.
- m6's `Degree/PhiData.lean`, `Degree/PhiDegree.lean`.
- m4/m5's analytic and cusp modules for `heckeRoof`'s `data'` argument.
- Baseline: `lake build` green, checker 0 mismatched / 0 missing.

## 1. Source of truth, build discipline, conventions

As [SET-M1](SET-M1.md) §§1–3, with the standing additions: **do not edit** the
paused Hecke face, the FFG/Φ modules, AC's modules, or the existing
`Defs/{Laurent,Jq,Fields,...}.lean`; prove a missing generic helper `private` and
record it as a promotion candidate. Append wrappers to `SOURCES` and modules to
`PORT_FILES`; checker target 0 mismatched / 0 missing; no commits.

## 2. Shared conventions specific to this set

- **The prelude is imported, never written.** Before adding any declaration, run
  `grep -rn '<name>' lean/FLTForHuman/` for the corresponding ported name
  (`TS`, `conj`, `phiAtSeed*`, `roots_prime_at_slot*`, `cycUnit`, `qTwistEquiv`,
  `qTwist_iota_of_pow_eq_one`, `iota_jq`, `iota_jqN`, `conj_zero_eq`,
  `conj_succ_eq`, `coeffEmb_qExpand`, `coeffMap_qExpand`, `coeffMap_TS`). Record
  the count.
- **AC's `finrankAlong` API is missing its arithmetic.** The pin defines
  `finrankAlong_comp`, `finrankAlong_id` and
  `finrankAlong_eq_relfinrank_fieldRange` privately inside m9's file; the port
  has only `AlgebraicCurve.finrankAlong` itself. Prove the three `private` in
  m9 and record them as promotion candidates for AC's
  `Defs/Correspondence.lean`.
- **The roof's `data'` is m6's.** `heckeRoof_adjoin_range_union_eq_top` takes
  `(data' : ModularPolynomialData ℓ')` as an argument; it is not proved here.
  Keep the wrapper's binders verbatim.

## 3. Definition of done (per topic and for the set)

As [SET-M1](SET-M1.md) §4. Consumer zones: **Zone F `[roof]`** for m9
(`heckeRoof_adjoin_range_union_eq_top` on the `N = 1` square) and a Zone for m7
(`relfinrank_qExpand_full` at `ℓ = 2`, `N = 1`) in
`spec/ModularCurveHeckeConsumer.lean`.

## 4. What to report back

1. The per-topic table: modules, port lines, public decls, build, checker
   before/after.
2. **The prelude drop, measured**: `grep -c` of each ported prelude name in the
   two topics' files (should be imports only), and the `raw − prelude` line count
   of each of the five pin files.
3. m7's two real blocks (`finrank_adjoin_jq_of_subset_range_qExpand{,_of_mem}`,
   `relfinrank_eq`'s `TransportDev`) and where they bit.
4. m9's roof argument and diagonal-degree argument, and the three `private` AC
   `finrankAlong` helpers.
5. Any statement that would not match its wrapper (quoted, not weakened).
6. The SET-M4 hand-off: which declarations m10–m12 import.
