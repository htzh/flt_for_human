# SET-M4 — integrality, principal divisors, and the exchange reduction (m10–m12)

**Status (2026-09-23): finalized against the landed SET-M1–SET-M3 modules; ready
to run.** SET-M3 passed review (checker **1,210 identical, 0 mismatched, 0
missing**, `lake build` 4,103 jobs green, consumer Zones A–I at 0 errors/0
warnings); the review is `../logs/mc-port.md` §Review of SET-M3. This is the run
brief for the **fourth** coding set of the `ModularCurve` Hecke-layer effort
([PORTING-MC.md](../PORTING-MC.md)). It authorizes exactly three topics:

| order | work order | object | pin | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-m10-integrality.md](TOPIC-m10-integrality.md) | tower integrality/finiteness and the Hecke integrality predicates (M10) | 13 nodes, 447 raw / 301 content | 350–500 | m6, m7 |
| 2 | [TOPIC-m11-principal-divisors.md](TOPIC-m11-principal-divisors.md) | `HasPrincipalDivisors` for the modular function fields (M11) | 2 nodes, 82 raw / 38 content | 40–90 | m6, m7, AC |
| 3 | [TOPIC-m12-exchange-reduction.md](TOPIC-m12-exchange-reduction.md) | the divisor/`Pic0` exchange reduction (M2) | 4 nodes, 111 raw / 68 content | 200–300 | m1, m9, m10 |

After this set, **every input of `heckeExchangeAt_of_WEX` and
`heckeOperatorsCommuteBar` is a ported theorem**, and the reserved capstone
([TOPIC-m13-capstone.md](TOPIC-m13-capstone.md)) is pure assembly over
`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`
(ported) and the exchange reduction.

## 0. What the earlier sets hand over

m1's Hecke vocabulary; m6's Φ datum family; m7's `relfinrank_qExpand_full`/
`relfinrank_laurentBaseChange`; m9's roof and diagonal degree; m3/m4's analytic
inclusion lemmas; AC's `Divisor`/`Pic0` correspondence API and the ported
`pullbackAlong_pushforwardAlong_eq_...`.

## 1. Source of truth, build discipline, conventions

As [SET-M1](SET-M1.md) §§1–3 and [SET-M3](SET-M3.md) §2. In particular: do not
edit AC's modules; the pin's private supply lemmas are reproduced `private` and
recorded as promotion candidates; append wrappers to `SOURCES` and modules to
`PORT_FILES`; checker 0 mismatched / 0 missing; no commits.

## 2. Definition of done (per topic and for the set)

As [SET-M1](SET-M1.md) §4. Consumer zones: **Zone G `[inputs]`** (m10/m11:
discharge `HeckeInputsAlong` for a concrete level) and **Zone H `[reduction]`**
(m12: the three reductions composed).

## 3. What to report back

1. The per-topic table: modules, port lines, public decls, build, checker
   before/after.
2. **m10's `FiniteAlong` route**: the `gens`/`gens_finite`/`isIntegral_gens`
   machinery and how `isIntegral_jqNModC_mul`/`eval_jqNModC_of_mul_eq_zero` feed
   it; the `_of_prime` derivations from `exists_modularPolynomialData_evalSymm`.
3. **m11**: how far `hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull`
   collapsed onto AC's `hasPrincipalDivisors_of_transcendental`/
   `hasPrincipalDivisors_adjoin_of_transcendental`; the exact hypotheses used.
4. **m12**: the `HeckeInputsAlong` case split (junk branch), the
   `heckeOperatorAlong_eq`/`Pic0.correspondence_correspondence_comm` step, and
   the `correspondence_congr` step at the end.
5. Any statement that would not match its wrapper (quoted, not weakened).
6. The capstone hand-off: the exact `HeckeExchangeAt` binders and the
   `HasPrincipalDivisors` instances the capstone must supply.
