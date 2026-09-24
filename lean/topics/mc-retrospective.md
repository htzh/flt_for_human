# The `ModularCurve` Hecke-layer effort — closing review

**Status (2026-09-23): the effort is complete.** This is the retrospective on the
port that closed the remaining 82-node cone of
`ModularCurve.heckeOperatorsCommuteBar` — the `math/009` divisor-correspondence
Hecke face — and wrote the theorem's capstone. It reviews the decisions, the
mathematical clarity, the redundancies cut, what was *not* cut, and the second
run of the **sets-dispatched-to-agents-with-a-human-capstone** experiment. The
retired blueprint is [PORTING-MC.md](PORTING-MC.md); the measured costs are
[../logs/mc-port.md](../logs/mc-port.md); the mathematics is
[../../math/009-hecke-jacobian-commute.md](../../math/009-hecke-jacobian-commute.md).

FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 1. What was delivered

**The whole remaining cone**, from the coverage report's
[82 nodes / 10,569 raw / 7,579 content](../../studies/hecke-commute-bar-coverage.md)
to **remaining 0 / 0 / 0**, plus the 13 definition modules the cone imports and
the capstone.

| check | result |
|---|---|
| `lake build` | **4,107 jobs, 0 warnings, no `sorry`** in `FLTForHuman/` |
| `spec/check_flt_statements.py` | **1,237 identical (67 promoted), 0 mismatched, 0 missing**, 14 exemptions (1,251 port declarations) |
| coverage (the §7 recipe of the report) | **remaining 0 nodes, 0 raw, 0 content** |
| `spec/ModularCurveHeckeConsumer.lean` | **0 errors, 0 warnings**, Zones A–K |
| `#print axioms ModularCurve.heckeOperatorsCommuteBar` | `[propext, Classical.choice, Quot.sound]` |
| commits | none — the working tree is the hand-off |
| size | 26 new modules (14 SET-M1 + 7 SET-M2 + 3 SET-M3 + 3 SET-M4 − overlaps) |

The modules, in dependency order:

| topic | modules | role |
|---|---|---|
| m1 | `Defs/{HeckeOperator,DegeneracyTower,HeckeTotal,HeckeModule,ArithmeticGalois}` | the Hecke correspondences, the degeneracy tower and `HeckeExchangeAt`, the total operator, `JZero` |
| m2 | `Defs/{GeometricBaseChange,QAdicPlace,CuspidalClass,AtkinLehner,ModularUnit,JqCoeff}` | the base-change model, the cusps and the `q`-adic place, the modular unit |
| m3 | `Analytic/{QParamUnique,ModularUnitQExpansion,Gamma0Cosets}` | the modular-unit `q`-expansion |
| m4 | `Analytic/{Gamma0InvariantCore,FrickeInvariance}` | the shared Γ₀-invariant core and the Fricke/inclusion headlines |
| m6 | `Degree/{PhiData,PhiDegree}` | the Φ datum family and its degree tail |
| m5 | `Analytic/{CuspBookkeeping,FrickeAut,CuspDichotomy}` | the `RatFunc` cusp model, the dichotomy, the Fricke automorphisms, the folded prime degree |
| m7 | `Degree/{LaurentGlue,Relfinrank}` | the Laurent/`coeffEmb` glue and the two relative-degree theorems |
| m9 | `Degree/Roof` | the roof generation and the diagonal degree |
| m10 | `HeckeInputs/Integrality` | tower integrality/finiteness and the Hecke integrality predicates |
| m11 | `PrincipalDivisors/ModularCurveBar` | `HasPrincipalDivisors` for the modular function fields |
| m12 | `HeckeExchange/Reduction` | the divisor/`Pic0` exchange reduction |
| **m13** | `Capstone` | **`ModularCurve.heckeOperatorsCommuteBar`** |

**Every input of `math/009`'s exchange reduction is now a ported theorem**: the
Weil exchange and `separableAlong_of_charZero` (AC), the function-field generation
(FFG), the modular polynomial family (Φ_p), the roof generation and diagonal
degree, the integrality/finiteness, `HasPrincipalDivisors` for the modular
function field, and the exchange reduction — with the capstone applying them.

## 2. The decisions that shaped it

| decision | why | outcome |
|---|---|---|
| **Sets split on the mathematical fork** | context is the binding constraint; route cost dominates line count | SET-M1 took the vocabulary + the first analytic layer; SET-M2 the Fricke/inclusion core, Φ data and cusp tail; SET-M3 the degree/roof; SET-M4 the operator inputs |
| **One subagent per set, review between sets** | the next set's orders must name the modules that actually exist | every set's hand-off names real declarations; one real binder mismatch was caught at review (`exists_isFrickeAut_of_modularPolynomialData`) |
| **The capstone reserved for the reviewer** | writing it is the final wire test, not ceremony | it compiled **first try in 13 s**, so every upstream interface is intact |
| **The vocabulary split into two definition topics (m1/m2)** | the 13 pin definition modules are the whole interface; a wrong shape redoes everything | `HeckeExchangeAt` ended byte-identical to the pin; `geomAut`'s tensor model held to the end |
| **Statements from the `Theorems/` wrappers, diffed mechanically** | a wrong statement is maximally expensive | 1,237 verified; the one mismatch was a missing explicit binder, fixed |
| **Dedup by measurement, not inspection** | "redundant" is a claim about the graph | the four prelude cuts below are all `diff`/`grep -c`-measured |
| **The `m5b` re-scope when a topic blocked** | one blocked topic should not stall the effort | the blocked `CuspDichotomy` was re-scoped, re-dispatched and solved in two rounds |
| **No `maxHeartbeats` ever raised** | the pin's own bumps are not needed | both pin `maxHeartbeats`/`synthInstance.maxHeartbeats` sites were avoided by restructuring |

## 3. Math clarity achieved

**The remaining mathematics is four statements, not 7.6k content lines.**

- the **`RatFunc` cusp model** — `ℚ̄(X₀(ℓ))` as `RatFunc 𝕂` with a finite, separable
  degree-`(ℓ+1)` cover, then a place count giving the two-cusp dichotomy
  (`Analytic/CuspDichotomy.lean`, written once for both the dichotomy and the
  folded prime degree);
- the **Γ₀-invariant core** — an `Γ₀(N)`-invariant `q`-expansion lies in the
  modular function field, is integral over `ℚ[jq]`, and transforms by Fricke
  (`Analytic/Gamma0InvariantCore.lean` + `FrickeInvariance.lean`);
- the **Fricke automorphism** — the modular polynomial datum gives the
  `q ↦ q^ℓ` automorphism (`Analytic/FrickeAut.lean`);
- the **roof and diagonal degree** — the two legs generate the top field, and the
  diagonal degree is `ℓ` (`Degree/Roof.lean`).

Everything else is concretisation and assembly: the definitions, the Φ datum
family (mostly one-liners over the ported Φ_p effort), the integrality
bookkeeping, and the exchange reduction. The port's contribution to clarity is to
have said so once each, in modules named for the mathematical role, instead of
inside the pin's 800-line files.

**The two-route structure is visible in the tree.** `Degree/PhiData.lean` +
`Degree/PhiDegree.lean` (the arithmetic/datum route) and `Analytic/*` (the
analytic route) meet at `Analytic/CuspDichotomy.lean` and `Degree/Roof.lean`;
`HeckeInputs/Integrality.lean` is the operator's interface to both. A reader can
see that the layer is `Defs/` plus four independent theories plus the reduction.

## 4. Redundancies cut, measured

| redundancy | pin | port |
|---|---|---|
| the M8 Fricke/inclusion prelude | **3 copies**, 651 content lines each; the first two differ by 12 lines | **once** (`Analytic/Gamma0InvariantCore.lean`), with the ported `RealL` block imported |
| the `RatFunc` cusp model | **2 copies**, first 160 content lines identical | **once** (`Analytic/CuspDichotomy.lean`), `difflib` one block of size 160 |
| the modular-unit `q`-expansion prelude | **4 copies**, 165 raw lines byte-identical | **once** (`Analytic/ModularUnitQExpansion.lean`) |
| the `TS`/`conj`/`phiAtSeed`/slot prelude | **3 copies** at the head of the degree/roof files | **never written** — already public in `Defs/TS.lean`, `Defs/PhiAtSlot.lean`, `PhiSlotRoots.lean`, `Defs/Cyclotomic.lean`, `Defs/Twist.lean` |
| the Hecke-operator private supply lemmas | 4, private, in 2 files | 2 deduped to ported public lemmas, 2 written **public once** (they are wrapper targets) |
| the Φ datum family | 14 nodes | **5 one-liners** over the ported Φ_p effort; the `eval_jqNModC_*` block is a ~30-line transcription |
| `hasPrincipalDivisors_*` | 82 raw / 38 content | **81 port lines, one AC theorem** (`hasPrincipalDivisors_adjoin_of_transcendental`) |
| `p2m_*`/`attribute` scaffolding | ≈2,990 of 10,569 raw lines (28%) | never written |

The budget predicted ≈4,870 deduplicated content lines and ≈5.8k–7.6k written
lines; the measured module total is in that band, and the four prelude cuts are
the reason the effort was tractable.

## 5. What was deliberately not cut

- **The pin's analytic argument structure** (the eta-product/Taylor route, the
  `HasFPowerSeriesOnBall` uniqueness) — transcribed where mathlib has no
  replacement; the route audit preceded any restatement.
- **The out-of-cone API of the definition modules** — `eisensteinNumerator`, the
  rational `cuspZero`/`cuspZeroFull`, `cuspidalClass`, the transposes, the
  `ArithmeticGalois` `≃ₐ`-action. Ported or deferred with counts; they are the
  modular Hecke/Galois-rep and Riemann–Roch layers' API.
- **The deferred `PicAction`/`JZero.torsionGaloisRep`** (0 cone occurrences); they
  need the `SMul (SemilinearAut K F) (Pic0 K F)` the AC port dropped, and the
  anonymous `SMul (F ≃ₐ[K] F) (Place K F)` was restored in `AtkinLehner.lean`.
- **The three generic AC `finrankAlong` helpers** — `private` in
  `Degree/Roof.lean`, recommended for promotion to
  `AlgebraicCurve/Defs/Correspondence.lean` (AC is a closed effort; not done).

## 6. Predictions vs measurements, and the two blow-ups

**The coverage report's predictions held, mostly.** The m11 collapse cost 81 port
lines against the pin's 82 raw / 38 content; the Φ one-liners held; the prelude
cuts are measured. `T10`-style finiteness stayed out of scope as decided.

**The two real costs were kernel-reduction blow-ups, not mathematics**, and both
were fixed structurally:

1. **`CuspDichotomy`'s `Subtype.val` defeq** — a `(kernel) deterministic timeout`
   on a `rfl`-looking coercion lemma. Isolation probes showed the cost is any
   kernel defeq between two concrete `IntermediateField.adjoin` carriers, not the
   proof term. Fixed with a generic `private ifRE (S T) (h := S = T) : ↥S ≃+* ↥T`
   whose coercion lemma is `rfl` at the abstract carriers: **3 m 09 s → 16 s**.
2. **`TransportDev`'s instance-search timeouts** — fixed by explicit
   `Algebra.IsIntegral.of_finite`/`Module.Free.of_divisionRing` locals.

Both are now in [porting-playbook.md](../porting-playbook.md) §3.11, together
with the **CPU-time discriminator** (high user CPU + timeout ⇒ real blow-up,
bisect; ~0 CPU ⇒ lock contention, re-run when idle). **No `maxHeartbeats`,
`maxRecDepth` or `synthInstance.maxHeartbeats` was raised anywhere**, and the pin's
own bumps were avoided: the pin's `relfinrank_qExpand_full` and
`finrankAlong_towerSubstBar_comp_heckeAlphaBar` build under the port's global
4,000,000 in ~15 s.

**The build-discipline lesson, learned the hard way.** The first work orders
loosened the playbook's 60/120 s bounds to 240/300/900 s, and one reading of the
blocked module was a 4 m 34 s wall-time stall that was **lock contention with
another agent's build, not Lean work**. The discipline is now uniformly
**60/90/180 s, expect ≤ 30 s, past ~60 s is a blow-up to bisect**, in the playbook
and every order.

## 7. The process experiment

Running the port as four sets — SET-M1 (m1–m3), SET-M2 (m4, m6, m5), SET-M3
(m7, m9), SET-M4 (m10–m12), each a single coding agent, with the manager
reviewing between sets and writing the capstone — was the second run of the
[AC effort's](ac-retrospective.md) experiment. It worked, and the reasons are
worth recording:

- **The review gate caught real defects.** The manager fixed a binder mismatch
  (`exists_isFrickeAut_of_modularPolynomialData`), completed missing README rows
  and consumer zones, and registered the m5 declarations the interrupted agent
  left behind.
- **Re-scoping is part of managing.** When `CuspDichotomy` blocked, the manager
  diagnosed it (including reading the stopped agent's session history), kept the
  tree green by setting the file aside, wrote a focused `TOPIC-m5b`, and
  re-dispatched; the fresh agent solved it in two rounds.
- **The capstone is a genuine review instrument.** It consumed m9–m12 and
  compiled first try.
- **The manager's own probes de-risked topics before dispatch.** m6's five
  one-liners and the `eval_jqNModC_*` route were verified by `Scratch` probes
  before SET-M2 ran, and m3's `qParam_coeff_unique` mathlib API was pre-checked.

## 8. Residual items

1. **The paused automorphic Hecke face** (`PORTING-Hecke.md` SET 5: T10's
   re-scoped infrastructure, then Γ₁/Nebentypus/Γ_H/Atkin–Lehner tiers) — a
   different face, unaffected by this effort.
2. **The three AC `finrankAlong` promotion candidates** — promote to
   `AlgebraicCurve/Defs/Correspondence.lean`.
3. **The deferred `ArithmeticGalois` `PicAction`/`torsionGaloisRep`** and the
   restored anonymous `Place`-`SMul` — decide the AC home.
4. **The two generic supply lemmas** live in `Defs/HeckeOperator.lean` rather than
   `Defs/Laurent.lean` (the workspace rule forbade editing the latter at the
   time); FFG is now editable, so they can move.
5. **The friction log** — the v4.34 entries and the two blow-up fixes at the tail
   of [../logs/mc-port.md](../logs/mc-port.md) §Friction; the playbook calls it the
   highest-value artifact because it is not derivable from the code.

## 9. Pointers

- [PORTING-MC.md](PORTING-MC.md) — the retired blueprint.
- [../logs/mc-port.md](../logs/mc-port.md) — the measured record, per set, with
  the three reviews and the capstone close.
- [SET-M1.md](hecke/SET-M1.md)–[SET-M4.md](hecke/SET-M4.md) and
  [hecke/](hecke/) — the run briefs and the work orders, including the `m5b`
  re-scope.
- [porting-playbook.md](../porting-playbook.md) — the reusable method, now with
  the two blow-up failure modes and the CPU-time discriminator.
- [ac-retrospective.md](ac-retrospective.md) — the previous effort's parallel
  review.
- [../../studies/hecke-commute-bar-coverage.md](../../studies/hecke-commute-bar-coverage.md)
  — the measured gap this effort closed.
- [../spec/ModularCurveHeckeConsumer.lean](../spec/ModularCurveHeckeConsumer.lean)
  — the definition of done, Zones A–K, ending at the unconditional target.
