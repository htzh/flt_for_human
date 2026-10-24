# The forward modular equation for odd Vélu quotients — one node, 87 lines, all premises in

**Landed 2026-10-23, one-node set.** `frontier.py --ds --ready --nexus --fanin-min 7`
put this node at the head of its 40-candidate shelf: it is the only unported *nexus*
node in its own demand, and the demand is the node itself — `needed 1 node / 87
lines`. Every one of its seven premises is ported, so this was a transcription and a
verification, not a scouting problem.

## 1. The node

| item | value |
|---|---|
| name | `ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq` |
| pin `S_` file | `P2M/Sol/S_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean` (87 lines) |
| statement authority | `Theorems/Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean` (24 lines) |
| declarations | 1 — no helpers, no private prelude |
| port cone | 97 nodes / 64,984 raw `S_` lines, 96 of them in the frontier |
| demand | 1 node / 87 lines, all at hops 1 |
| fan-in | cites 7; cited by 3 (1 in the D-S cone, 3 project-wide) |

## 2. The mathematics

For `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)`, an elliptic `W/𝕂`, a point `Q` with
`addOrderOf Q = 2n+1`, and the odd Vélu quotient `W/⟨Q⟩ = W.veluQuotient
(W.oddOrderSummingSet Q n)` (assumed elliptic), the theorem says

$$j(W/\langle Q\rangle)\ \text{is a root of}\ \ \Phi_{2n+1}\bigl(j(W),\, Y\bigr),$$

where `Φ` is any `ModularPolynomialData (2n+1)`: monic in `Y`, of `Y`-degree
`ψ(2n+1)`, and satisfying `Φ(j(q), j(q^{2n+1})) = 0` in `ℚ((q))`.

This is the **forward half of the moduli interpretation** of the modular polynomial.
The classical construction defines `Φ_N` through the `q`-expansion; the theorem
carries that definition to an arbitrary curve: a curve cyclically `N`-isogenous to
`E` has `j`-invariant a root of the fibre `Φ_N(j(E), ·)`. It does not use
transcendence, and it is the direction that makes the converse ("every root is a
quotient `j`") and the counting direction ("the `ψ(N)` roots are distinct") possible.

Note what `oddOrderSummingSet Q n` is: for odd order `2n+1` the nonzero multiples of
`Q` pair as `{kQ, -kQ}`, so `S = {(kQ).coordsOrZero : 1 ≤ k ≤ n}` takes one
representative from each of the `n` pairs and sends the point at infinity to
`(0, 0)`. The Vélu formulas then use the sums of `veluT` and `veluU` over `S`
(`a₄' = a₄ - 5ΣT`, `a₆' = a₆ - b₂ΣT - 7ΣU`), and `hΔ` is what makes the result
elliptic again.

## 3. The proof

One instantiation of
`WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`
(`ModularCurve/ModularPolynomialEvalJ.lean`) — the general theorem that a cyclic
kernel of order `N` over an algebraically closed characteristic-`0` field forces
`Φ_N(j(E), j(E')) = 0` — which needs:

1. an integral finite `ι : E'.FunctionField →ₐ[K] E.FunctionField` carrying the norm
   formula — here `ι` is
   `WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples`
   (`WeierstrassCurve/Velu/PointMapOddOrder.lean`), the embedding of the quotient's
   function field whose pushforward point map has kernel `ℤQ` and degree `2n+1`;
2. `IsAddCyclic` of that kernel and its cardinality `N` — both read off
   `ker = AddSubgroup.zmultiples Q` and `addOrderOf Q = 2n+1`;
3. the genus-one place gate (`GenusOnePlaceGate`, centred, Abel's theorem) on both
   curves, from `CoordinateRing.isDedekindDomain` and
   `hasPrincipalDivisors_functionField`.

So the 87 lines are exactly the instance plumbing: `IsAlgClosed` from
`HahnSeries.isAlgClosed_rat`, `CharZero` from `HahnSeries.C_injective`, the two gates,
separability of `ι`, `NormFormulaAlong` from `AlgebraicCurve.normFormulaAlong`, then
the capstone. Nothing in the proof is new mathematics; that is the point of the
`--ready`/nexus reading.

The seven premises are all in the port, at these homes (the table used to sit in
the module header; the header now keeps only the statement and a pointer here):

| premise | port home |
|---|---|
| `WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward` | `ModularCurve/ModularPolynomialEvalJ.lean` |
| `WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples` | `WeierstrassCurve/Velu/PointMapOddOrder.lean` |
| `WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem` | `WeierstrassCurve/GenusOnePlaceGateCentred.lean` |
| `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain` | `WeierstrassCurve/Place/CoordinateRingDedekind.lean` |
| `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField` | `WeierstrassCurve/PrincipalDivisors.lean` |
| `HahnSeries.isAlgClosed_rat` | `RingTheory/HahnSeries/IsAlgClosed.lean` |
| `AlgebraicCurve.normFormulaAlong` | `AlgebraicCurve/WeilExchange/Transport.lean` |

## 4. Result

| item | value |
|---|---|
| module | `FLTForHuman/ModularCurve/ModularPolynomialVelu.lean`, 111 lines (header 29, one declaration) |
| build | `flock .lake/flt_build.lock lake build FLTForHuman.ModularCurve.ModularPolynomialVelu` — 4,477 jobs, module **4.3 s**, **0 warnings from the module** |
| olean | `.lake/build/lib/lean/FLTForHuman/ModularCurve/ModularPolynomialVelu.olean`, 253,504 B |
| checker | `spec/check_port.py` — **1 ok, 0 mismatch, 0 missing, 0 own, 0 kw** against `aa2d8b3` |
| axioms | `[propext, Classical.choice, Quot.sound]` |

**Adaptations.** The `CharZero 𝕂` step is respelled: the pin's `RingHom.charZero_iff`
on `HahnSeries.C` is now `charZero_of_injective_ringHom` with
`HahnSeries.C_injective` (the rename only; `if_*`/`dif_*` renames do not occur in this
file). The pin's `attribute [-instance]`/`[-simp]` block and its heartbeat bumps
are not transcribed — none of their names is in this module's cone, and the port's
global cap is 4,000,000. Three of the pin's instance lines are dropped because
synthesis already supplies them: the two `.toAffine` re-registrations of
`IsElliptic` (`toAffine` is an abbrev) and the explicit `NeZero (2 * n + 1)` (found
from `n + 1`); the gate instances `letI := g`, `haveI := hgc`, `haveI := hga` (and
`g'`) stay, since the final typeclass search needs them. No statement changed.

**Warnings.** The module emits none. The 17 `haveI`-vs-`have` hits the style linter
would otherwise print are false positives — every one introduces an instance local
(`IsAlgClosed`, `CharZero`, the Dedekind/principal-divisor and gate instances) that
typeclass search consumes later — so they are suppressed with a comment, the same
way the other pin-transcribed modules with instance walls do it. The `165` warning
lines in a `LEAN_NUM_THREADS=4 lake build` log are all **replayed from dependency
modules** (40 `DualEndData`, 26 `Velu/RestrictAlong`, 15 `Velu/Shift`, 14
`ModularPolynomialIrreducible`, 14 `P1/TraceEngine`, …); none carries this file's
name. They are the pre-existing deprecation/`simp`-arg warnings of the cold tree,
not this node's.

## 5. The theory it is half of

The forward node is the `⇒` of a set equality: over `𝕂` with `j(W)` transcendental
and `N` odd, the roots of `Φ_N(j(W), Y)` are exactly the `j(W/H)` for the cyclic
order-`N` subgroups `H`. The converse (`mem_of_isRoot_map_j_of_transcendental_of_odd`,
145 lines, whose internal set equality gives the pin's public corollary `r ∈ L`),
the rigidity ladder it shares with the forward node, and the two support columns
are scoped as one set in
[../topics/modularCurve/TOPIC-modular-equation-transcendental-j.md](../topics/modularCurve/TOPIC-modular-equation-transcendental-j.md).
The short version of the measurement:

* the three-node rigidity ladder (`isUnit_leadingCoeff_diag` 14,
  `exists_forall_pointEnd_eq_zsmul_of_transcendental_j` 62,
  `zmultiples_eq_of_veluQuotient_j_eq_of_transcendental` 80) is shared by both
  halves — **156 lines**;
* the product capstone (`fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`,
  97) adds only that on top of this node;
* the converse adds `mem_of_…` (145) + membership (`j_mem_of_a_mem` 32,
  `veluQuotient_j_mem_of_mem` 91) + count (22) on top of this node and the ladder;
* **543 new lines over 8 nodes** is the whole theory, against 1,675 raw in the two
  frontier readings — because the port's
  `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`
  (`WeierstrassCurve/Velu/Discriminant.lean`, from the product formula
  `discriminant_prod_veluU_pow`) is strictly stronger than the pin's node and
  removes the pin's 1,045-line ψ₂²/discriminant block (100 + 781 + 164).

The five-node 340-line wave is the product half's demand:

| node (all `ModularCurve.ModularPolynomialData.*` unless noted) | lines | demand |
|---|---:|---:|
| `isUnit_leadingCoeff_diag` | 14 | 1 / 14 |
| `WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j` | 62 | 2 / 76 |
| `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental` | 80 | 3 / 156 |
| **this node** | 87 | **1 / 87** |
| `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental` | 97 | 5 / 340 |

From there the root-membership face
(`mem_of_isRoot_map_j_of_transcendental_of_odd` → `hasRamBound_{one,two,three}`)
and the product face (`fibrePoly_…` → `…_of_isAlgClosed` → level lowering) are the
two downstream readings of the same equality. The Mazur consumer
`modularPolynomial_eval_jInt_jQuotVelu_eq_zero` (6 nodes / 1,408, of which this node
is one) is the arithmetic specialization over `ℤ`/`ℚ̄`, a separate set.

## 6. Cold-tree note

`lean/.lake` was cold at the start: tree-wide, 13 modules had no olean and 18 were
stale (the batch documented in [build-time-issues.md](build-time-issues.md) §3/§3b;
`ModularPolynomialE4Cube` and `Isogeny/TwoCurveDescent`, both in this module's
closure, lost their oleans when a build was killed mid-replay). One background
`lake build` of the target under the pinned `v4.34.0` restored the closure and wrote
the olean; nothing was fetched. Do **not** run `lake update` in this tree: the
transitive deps are pinned to branches in `lake-manifest.json`, and a re-resolution
follows mathlib `main` to `v4.35.0`, which invalidates the whole `v4.34.0` olean tree.

Pin: `anthropics/fermats-last-theorem@aa2d8b3`. Statement and proof:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean>.

## 7. Ground pass for the theory (2026-10-23)

Preparing the homes for the eight remaining nodes of
[../topics/modularCurve/TOPIC-modular-equation-transcendental-j.md](../topics/modularCurve/TOPIC-modular-equation-transcendental-j.md)
meant touching legacy modules, so they were brought up to the handover standard
(the full table is the topic's §2.6):

* `ModularCurve/Defs/FibrePoly.lean` — the pin's three public `fibrePoly` facts
  (`monic_fibrePoly`, `natDegree_fibrePoly`, `card_roots_fibrePoly_of_monic`) were
  promoted here from the `private` copies in `Degree/PhiData.lean` (deleted there),
  the module gained `spec-pin:` for the pin's definition file, the `ReduceModBivar`
  block and the three theorem wrappers, and it left `spec/old_check_stmts.py`'s
  `PORT_FILES`. `dedup.py` 0 clusters, `move_dead.py` 0 declarations, 0 warnings.
  Checker: **10 ok / 0 mismatch / 0 missing / 0 own**.
* `WeierstrassCurve/Velu/PointMapOddOrder.lean` — `spec-pin:` for its two theorem
  wrappers, out of `PORT_FILES`, and the five `dif_pos`/`dif_neg` deprecations
  renamed to `dite_eq_left`/`dite_eq_right`. Checker: **2 ok / 0 mismatch**, and the
  module no longer emits warnings (it was the source of five replayed ones).
* `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` — the one machine token in a
  private name dropped (`cmm5_dp_natCard_ker_comp` → `natCard_ker_comp`); already
  wired and warning-free.
* `ModularCurve/Degree/PhiData.lean` — the three `private` fibrePoly copies deleted
  (dedup), and one dead theorem deleted:
  `nonempty_modularPolynomialData_mul_of_coprime`, which is dead in the pin too (it
  is defined in two `S_` files and used nowhere). Checker stays 10 ok.

Whole wired set after the pass: **4,941 ok, 0 mismatch, 0 missing, 19 own, 0 kw** over
213 modules; `lake build FLTForHuman.ModularCurve.ModularPolynomialVelu` green
(4,477 jobs), with none of the five touched modules emitting a warning.
