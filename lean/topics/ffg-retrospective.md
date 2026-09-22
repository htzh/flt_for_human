# The `functionFieldGeneration` effort — closing review

**Status (2026-09-22): the effort is complete.** This is the retrospective on the
`ModularCurve.functionFieldGeneration` port, written after T20 made the theorem
unconditional. It reviews three things the effort was judged on — the decisions,
the mathematical clarity, and the redundancies cut — and records what was *not*
cut and why. The retired blueprint is
[PORTING-FFG.md](PORTING-FFG.md); the measured cost log is
[../logs/ffg-port.md](../logs/ffg-port.md); the mathematics is
[math/010](../../math/010-function-field-generation.md).

## 1. What was delivered

`ModularCurve.functionFieldGeneration : ∀ N, N ≠ 0 → FunctionFieldGeneration N`,
unconditional and `sorry`-free: for every `d ∣ N`, `j(q ^ d)` lies in
`ℚ(j(q), j(q ^ N))`.

| check | result |
|---|---|
| `lake build` | green, 3874 jobs, **0 warnings**, no `sorry` in `FLTForHuman/` |
| `#print axioms functionFieldGeneration` | `[propext, Classical.choice, Quot.sound]` |
| statement checker vs pin `aa2d8b3` | **304 identical, 0 mismatched, 0 missing** (16 promoted) |
| consumer `spec/ModularCurveConsumer.lean` | **0 errors**; Zone A's capstone is the theorem |
| out-of-cone ≥5-indegree tier (§2.1) | **100%** |

The FFG modules, in dependency order (final sizes):

| module | role | lines |
|---|---|---|
| `FunctionFieldGeneration/Target.lean` | the statement, and `M = 1` | 45 |
| `FunctionFieldGeneration/Collapse.lean` | `FunctionFieldGeneration N ↔ F_N^full = F_N` | 50 |
| `Defs/PhiAtSlot.lean` + `PhiSlotRoots.lean` | T14: the slot vocabulary, written once | 237 + 153 |
| `FunctionFieldGeneration/Spine.lean` | `Tight`/`Gen`/`Hall`, `hall_all`, conditional capstone | 403 |
| `FunctionFieldGeneration/Descent.lean` | T15: descent, one-prime `Gen` | 252 |
| `FunctionFieldGeneration/DegreeStep.lean` | T16: the `p+1` / `p` degrees | 455 |
| `FunctionFieldGeneration/Nonmembership.lean` | T17: tower + two-prime separation | 844 |
| `FunctionFieldGeneration/Generation.lean` | T18: one generator per prime power | 309 |
| `FunctionFieldGeneration/SlotProduct.lean` | T19: the slot product + prime non-membership | 1502 |
| `FunctionFieldGeneration/Capstone.lean` | T20: `inputs`, the theorem, corollaries, tail | 283 |
| `FieldTheory/CommonRoot.lean` | the three abstract engines | 347 |

The remainder behind the Φ_p input cost **≈3.8k new port lines** (T14–T20), against
§7.8's final ≈4.8k–5.0k estimate and the 11,312-line structural pin sum.

## 2. The decisions that shaped it

| decision | why | outcome |
|---|---|---|
| **Definitions first, then the theorem (the "gain test")** | a definitions-only Layer 0 is cheap, verifiable and reusable; the theorem's cost was gated by the unported Φ_p cone | Layer 0 was 1 module-round where 20 were budgeted; the cone later became the *only* analytic bridge |
| **A conditional capstone before the proof** | `functionFieldGeneration_of (h : Inputs)` is a proved artifact with no `sorryAx`; the theorem's distance becomes an explicit seven-field debt | the debt was visible and monotonically fell: 10 → 7 → 5 → 4 → 3 → 2 → 0 |
| **Statements verbatim, checked mechanically** | the pin is the authority; a wrong *statement* is maximally expensive, a wrong *proof* cheap | 304 statements diffed; `inputs`/`hall_all`/`gen_prime` are the only port-authored declarations, each recorded |
| **Module = mathematical role, not FLT's `Def_`/`Thm_`/`S_` split** | FLT's 144-file taxonomy obscures the mathematics; the port's file list should read as the proof | the 17-node remainder became 6 topic modules with headers naming subject, pin provenance and assumptions |
| **One topic at a time, each with a work order** | route costs, not line counts, dominate; a work order forces the route decision before transcription | every topic's route risk was named first (see §6); the only unplanned adaptation was one mathlib signature |
| **Drop by occurrence count, not by inspection** | §1's rule; prose "redundant" is a claim about mathematics, not about the graph | the T18 squarefree block and the T19 duplicate were decided by `grep` + a Lean-checked substitution, not intuition |
| **Mathlib-first audits, per topic** | the port should not hand-roll what mathlib has, and a recorded *negative* saves a future search | three real reuse wins and six recorded negatives (§4) |
| **The consumer is the definition of done** | a green library can still fail to *compose* | the consumer caught two ill-typed Zone A examples the library could not |
| **Never `import Mathlib`; `spec/` outside the library** | keeps the library's green/no-`sorry`/seconds-warm build meaningful | 3874 jobs, all mathlib imports explicit |

## 3. Math clarity achieved

**The mathematics is three abstract lemmas, not 3.8k lines.** Tier 0 of the
remainder is `Polynomial.mem_range_of_unique_common_root`,
`mem_range_of_eval_eq_const` and `irreducible_of_transitive_ringAut`, all in
`FieldTheory/CommonRoot.lean:60,111,148`. Every hard step of T15–T19 is one of them
instantiated at a concrete polynomial list: descent is the first, the
non-memberships are the second, the degrees are the third. The port's contribution
to clarity is to have said so once, in one file, instead of discovering it three
times inside 2,000-line files. The rest of the remainder is concretization, and the
work orders now price it as such.

**The one analytic input is isolated.** Everything reduces to the classical root
description of `Φ_p` (`PhiGen.splits_prime_at_slot`, T13); after it, the proof is
field theory and a divisor-lattice induction. Reading the port in dependency order
shows the boundary exactly: `ModularForms/` (R1 and the cone) is the analysis;
`ModularCurve/` from T14 on is algebra.

**The slot vocabulary has one home.** T14 wrote the pin's ~370-line prelude once
(`Defs/PhiAtSlot.lean`, `PhiSlotRoots.lean`, plus promotions into `Defs/TS`,
`Defs/Twist`, `Defs/Jq`). In the pin, 38 files repeat all 41 declarations and 11
more repeat a parallel `jqModC` block; in the port, one module.

**The two fields and the collapse are separated.** `F_N = ℚ(j, j_N)` versus
`F_N^full = ℚ(j_d : d ∣ N)` are defined once, and `Collapse.lean` makes
`FunctionFieldGeneration N ↔ F_N^full = F_N` a theorem rather than a remark. The
whole effort is then visibly "show `Gen N` and `Tight N` for all `N`".

**The conditional/unconditional split is a clarity device, not a workaround.**
`Spine.lean` is the conditional artifact; `Capstone.lean` is one screen of
assembly. A reader can see that 90% of the mathematics is independent of the seven
hypotheses, which is precisely the structure math/010 §2 describes.

## 4. Redundancies cut, measured

| redundancy | pin | port |
|---|---|---|
| the slot prelude, repeated per file | ~370 lines × 12 remainder files | once (T14) |
| `jqN_mem_of_div_primes` (two-prime descent) | 3+ verbatim copies in the 17 nodes, 6 in the repo | once (T18) |
| four `dedekindPsi_*` re-proofs in T19's block | 64 lines | public `Defs/Jq.lean` lemmas; `dedekindPsi_mul_prime_*` promoted out of `Spine.lean` |
| the T19 `Gen p` detour | `functionFieldGeneration_of_squarefree p` (pin line 1638), dragging in a 615–850-line squarefree block | `gen_prime`: `Gen p` is definitional, ~12 lines (Lean-verified, T18) |
| the slot count (`slotAt_mul`) | 108-line CRT fibre argument + 18-line gcd helpers | closed form `slotAt n d = (d / gcd (n/d) d) * φ (gcd (n/d) d)` + mathlib `Nat.Coprime.divisors_mul` (T19, ≈110–150 lines) |
| `mem_range_of_eval_eq_const` | re-proved privately in T19's file | imported from `CommonRoot` (T19) |
| `w1_relfinrank_insert` | 45-line prime-insert instance | the port's generic 19-line lemma + a set identity (T16/T18) |
| mathlib-duplicated helpers | `RingEquiv.ofBijective` (`qTwistEquiv`, `coeffMapEquiv`), `exists_pow_eq_self_of_coprime`, `IsCyclotomicExtension.zeta`, `IsPrimitiveRoot.pow`/`injOn_pow` | replaced by mathlib calls |

The single largest cut is the **T18 squarefree block** (nodes 2–6, ≈615–850 own
lines): the route audit showed its only consumer outside itself was T19's `Gen p`
step, replaced by `gen_prime`. The second is the prelude.

**Recorded negatives** (searches that found nothing, kept so nobody repeats them):
mathlib has no `dedekindPsi`, no Γ₀ index formula, no `minpoly.map` /
`minpoly.map_eq_of_injective`, and no shorter route from `CommonRoot`'s engines to
`eq_of_isRoot_of_isLevel`. External prior art exists for `[SL₂(ℤ) : Γ₀(p^k)]`
(Birkbeck, Apache-2.0) but is prime-power-only and outside the pinned mathlib.

## 5. What was deliberately not cut

- **`rval_aux` (680 body lines, `hslot_root` alone 493).** The audit measured it at
  ~64% irreducible mathematics; the port budgeted it and took only ~50 lines of
  cleanup. Golfing it would have been a false economy.
- **The M-arbitrary non-membership.** The "powerful `M`" case (`d = 36` at
  `hall_all`) makes it load-bearing; the audit verified it is not reducible to
  T17's prime-set lemma in either direction.
- **`exists_phiIrreducible_of_finrank_eq`.** Route-checked for a short corollary;
  the pin's `IsFractionRing (Polynomial ℤ) ℚ⟮jq⟯` construction is genuinely
  needed, so it was transcribed (and closed on the second build).
- **The deferred T18 squarefree block.** It is not capstone work, but it is real
  public API with downstream consumers (`relfinrank_adjoin_primes`,
  `relfinrank_full_mul_prime`). Deferring it was a scope decision, recorded as
  such — not a claim that it is worthless.
- **Repo-wide prelude duplication.** 38 files carry the T14 prelude and 11 a
  parallel `jqModC` block; deduplicating the whole repository is a separate,
  larger effort than this one.

## 6. Predictions vs measurements

Two lessons, both recorded in [../logs/ffg-port.md](../logs/ffg-port.md) §6:

- **Cost is shape risk, not line count.** Layer 0 and Layer 0b each budgeted ~20
  rounds and took 1; T16 budgeted 500–650 and measured 605. Meanwhile T19's
  2,002-line file was the right size but its route (closed form, `gen_prime`) was
  the entire decision. A budget for this work should be set in *named shape risks*.
- **Recorded non-events are information.** The predicted rewrite-search gap did not
  occur once the coefficientwise `[simp]` lemmas were used as bridges. T20's
  predicted `Hall`-binder friction did not occur: `Hall` is an `abbrev`, and the
  `Inputs` literal is seven lines. The one adaptation that *did* appear was
  v4.34.0's `isIntegral_algebraMap_iff` now taking `FaithfulSMul` instead of an
  injectivity proof — a one-line substitution.

## 7. Residual items

1. **The T18 API tail** — `full_eq_adjoin_primes`, `dedekindPsi_of_squarefree`,
   `relfinrank_full_of_squarefree`, `finrank_adjoin_jqN_eq_of_squarefree`,
   `functionFieldGeneration_of_squarefree`, plus `relfinrank_adjoin_primes` and
   `relfinrank_full_mul_prime`. Fully scouted in
   [functionFieldGeneration/TOPIC-generation.md](functionFieldGeneration/TOPIC-generation.md) §2.
2. **Repo-wide prelude dedup** — the T14 pattern applied beyond the remainder.
3. **The friction log** — the twelve-plus `v4.34.0`/`v4.33.0` entries at the tail of
   `spec/ModularCurveConsumer.lean`; the playbook calls it the highest-value
   artifact because it is not derivable from the code.

## 8. Pointers

- [PORTING-FFG.md](PORTING-FFG.md) — the retired blueprint (planning record).
- [../logs/ffg-port.md](../logs/ffg-port.md) — measured costs, per topic §2g–§2m.
- [../porting-playbook.md](../porting-playbook.md) — the reusable method.
- [../../math/010-function-field-generation.md](../../math/010-function-field-generation.md)
  — the mathematics.
- [../spec/ModularCurveConsumer.lean](../spec/ModularCurveConsumer.lean) — the
  definition of done, and the friction log.
- Topic work orders in [functionFieldGeneration/](functionFieldGeneration/) —
  T14–T20 as planned, with the route decisions.
