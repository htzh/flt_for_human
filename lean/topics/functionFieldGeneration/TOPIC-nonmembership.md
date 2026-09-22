# Topic 17: the non-membership tower and the two-prime separation

**Status: work order, ready to open when T16 lands. One topic, one module, one
session.** T14 (the shared slot prelude), T15 (descent) and T16 (the degree step)
are assumed **done and committed before this topic opens** — the effort ports one
topic at a time, and there are no parallel porting sessions. Both of T17's
prerequisites are then public: the tower needs T14 and the Φ_p cone, and the
two-prime separation additionally needs T16's
`finrank_adjoin_jqN_prime_of_not_mem`.

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 120 lake build <module>`. Non-return at 60 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The project's global cap is already
>   `4000000` (`lakefile.lean`), which is *above* the pin's local
>   `set_option maxHeartbeats 3200000` at tower 715/961 — so **omit** those
>   `set_option`s; do not transcribe them and do not raise the global one. The
>   usual stall cause is a `FunLike`-quantified lemma instantiated at a bare
>   function type (`DFunLike.coe` unfolds without bound) — restate it over the
>   concrete function instead. T5's log §2.2 has the worked example, and §7.1
>   below is this topic's instance.

**Audience.** A fresh session taking T17 of the `functionFieldGeneration` effort.
Read, in this order:

1. [PORTING-FFG.md](../../PORTING-FFG.md) §7.8 (the topic order and the audited
   routes) and §1 (the design rules);
2. [math/010](../../../math/010-function-field-generation.md) §6a — the two
   non-membership statements and why the tower needs them;
3. [TOPIC-slot-machinery.md](TOPIC-slot-machinery.md) (T14),
   [TOPIC-descent.md](TOPIC-descent.md) (T15) and
   [TOPIC-degree-step.md](TOPIC-degree-step.md) (T16) — the three predecessors
   whose vocabulary and engine calls this topic reuses;
4. [logs/audit-jqN-nonmemory.md](../../logs/audit-jqN-nonmemory.md) — the audit
   that fixed this topic's boundary against T19's private lemma;
5. [porting-playbook.md](../../porting-playbook.md) §3.5–§3.7 (`FunLike`,
   `abbrev` transparency) and §7.3.

## 1. Goal, and why this topic

**Goal.** Port the non-membership half of the strong induction. Two statements,
one module (§4):

1. **`jqN_pow_not_mem_adjoin_full`** — the **prime-power tower**, and an `Inputs`
   field. For `jqN p ∉ F_M^full`,
   `` $`j(q^{p^{a+2}}) \notin \mathbb{Q}\bigl(F_M^{\mathrm{full}},\ j(q^p),\dots,j(q^{p^{a+1}})\bigr)`$ ``.
   The proof builds the tower of intermediate fields
   `` $`C_i = \mathbb{Q}(F_M^{\mathrm{full}}, j(q^{p^j}) : j \le i)`$ `` and, by
   strong induction on `` $`a`$ ``, a compatible family of `ℚ`-algebra homs
   `` $`\sigma_i : C_i \to K(\!(q)\!)`$ `` whose images lie in a shrinking
   `qExpand` range. The modular equation `` $`\Phi_p`$ `` has both
   `` $`j(q^{p^{a+2}})`$ `` and `` $`j(q^{p^a})`$ `` as roots of
   `` $`\Phi_p(j(q^{p^{a+1}}), \cdot)`$ ``; pushing it through `` $`\sigma`$ ``
   forces both to the *same* root, and `` $`\sigma`$ `` injective gives
   `` $`j(q^{p^{a+2}}) = j(q^{p^a})`$ ``, contradicted by the `` $`q^{-p^a}`$ ``
   coefficient (1 vs 0).
2. **`jqN_prime_not_mem_adjoin`** — the **two-prime separation**, and a public
   `Theorems/` API. `jqN r` is not in `` $`\mathbb{Q}(j, j(q^p) : p \in S)`$ ``
   for a finite set `` $`S`$ `` of primes with `` $`r \notin S`$ ``. The engine is
   `step_contradiction`: if `` $`j(q^r) = g(j(q^p))`$ ``, then `` $`g`$ `` has
   degree `` $`< p+1`$ `` and is constant on the `` $`p+1`$ `` roots of
   `` $`\Phi_p(j(q), \cdot)`$ `` (a T4 `CommonRoot` engine), so
   `` $`j(q^r) \in \mathbb{Q}(j)`$ ``, contradicting
   `` $`[\mathbb{Q}(j)(j(q^p)) : \mathbb{Q}(j)] = p+1`$ `` — **T16's first
   statement**. The Finset induction over `` $`S`$ `` is
   `jqN_prime_not_mem_adjoin_key`.

**Why now.** T17 is the second half of the `Tight` argument and follows T16 in the
serial order: T16 gave the degree of every adjoin step, T17 gives that the step is
*proper*, and together they bound the prime-power tower. It discharges one `Inputs`
field and completes the public non-membership API the downstream
`relfinrank_*` lemmas consume.

**Settled: this topic is not T19's private lemma, and neither reduces to the
other.** [audit-jqN-nonmemory.md](../../logs/audit-jqN-nonmemory.md) checked both
directions: T19's private M-arbitrary `jqN_prime_not_mem_adjoin` is a *different
statement* (single composite generator `jqN M`, base `ℚ⟮jq⟯`, divisor-wise `hall`)
and is load-bearing for **powerful** `` $`M`$ `` (`` $`d = 36`$ `` at `hall_all`);
T17's public Finset lemma is keyed to prime generators and cannot supply it.
Conversely nothing in the tower or the base uses T19. The port keeps both.

**Scope note — what each node buys.** The tower is an `Inputs` field: porting it
takes the capstone's debt down by one. The base is **not** on the capstone's path
— T19's private M-arbitrary lemma is what discharges `Inputs.jqN_prime_not_mem_full`
— it is public `Theorems/` API, consumed by `relfinrank_adjoin_primes`,
`relfinrank_full_mul_prime` and `jqN_sq_not_mem_adjoin`. Transcribe the tower
first, then the base; both land in the same module and neither blocks the other.
If the effort ever narrows to the unconditional headline alone, the base's ~224
lines are the one part of this topic that can be deferred. (The 2026-09-22 route
audit records that T19's private lemma needs the base only for `Gen p`, which is
near-definitional — see
[TOPIC-t17-t19-route-audit.md](TOPIC-t17-t19-route-audit.md) §1. That is a T19
scope question, not a T17 one; T17 ports the base as the plan states.)

## 2. The scouted inventory

Two pin files, no shared development between them; both port into
`Nonmembership.lean`.

| node | pin file | node span | own lines |
|---|---|---|---|
| `jqN_pow_not_mem_adjoin_full` | `S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` (995) | 400–985 | ≈517 |
| `jqN_prime_not_mem_adjoin` | `S_ModularCurve_jqN_prime_not_mem_adjoin.lean` (653) | 406–651 | ≈224 |

Both files open with T14's ~370-line prelude (lines 29–399 / 34–399), already
ported and **not** to be re-copied.

### 2.1 The tower: helpers and spans

| helper | pin | span | status |
|---|---|---|---|
| `aeval_intermediateField_eq_zero` | 400–407 | 8 | T14 — `Defs/PhiAtSlot.lean` |
| `phiAtSeed_eval_of_injective` | 408–413 | 6 | T14 — `Defs/PhiAtSlot.lean` |
| `phiAtSeed_eval_symm` | 414–422 | 9 | T14 — `Defs/PhiAtSlot.lean` |
| `jqN_congr` | 423–425 | 3 | T14 — `Defs/Jq.lean` |
| `phiAtSeed_jqN_eval_down` | 426–430 | 5 | T14 — `Defs/PhiAtSlot.lean` |
| `qExpand_qTwist_notMem_range_qExpand` | 431–442 | 12 | T14 — `Defs/PhiAtSlot.lean` |
| `nat_ne_of_mul` | 443–447 | 5 | **port** |
| `mem_range_qExpand_of_mul` | 449–456 | 8 | **port** |
| `range_qExpand_congr` | 458–465 | 8 | **port** |
| `chainField` | 467–471 | 5 | **port** |
| `mem_chainField` | 472–475 | 4 | **port** |
| `full_le_chainField` | 476–479 | 4 | **port** |
| `chainField_zero` | 480–492 | 13 | **port** |
| `chainField_mono` | 493–499 | 7 | **port** |
| `chainField_succ` | 500–523 | 24 | **port** |
| `chain_extend` | 524–703 | 180 | **port — hard half A** |
| `chain_endgame` | 717–959 | 243 | **port — hard half B** |
| `jqN_pow_not_mem_adjoin_full_key` | 963–971 | 9 | **port** |
| public wrapper | 979–985 | 7 | **port** |

Six helpers (~43 lines) are T14's and are deleted, not re-ported. The two
`set_option maxHeartbeats 3200000 in` at 715 and 961 are **omitted** — below the
port's global `4000000`.

### 2.2 The base: helpers and spans

| helper | pin | span | status |
|---|---|---|---|
| `qExpand_qTwist_notMem_range_qExpand` | 406–417 | 12 | T14 — `Defs/PhiAtSlot.lean` |
| `aeval_intermediateField_eq_zero` | 418–425 | 8 | T14 — `Defs/PhiAtSlot.lean` |
| `step_contradiction` | 426–576 | 151 | **port** |
| `jqN_prime_not_mem_adjoin_key` | 577–635 | 65 | **port** |
| public wrapper | 642–643 | 8 | **port** |

### 2.3 What each node uses

- **Tower.** `isRoot_prime_at_slot_iff`, `roots_prime_at_slot_roots_nodup`,
  `prod_form_ne_zero` (T14 — `PhiSlotRoots`); `PhiGen.splits_prime_at_slot` (T13);
  `exists_phiIrreducible_evalSymm` (T12); `TS_injective`/`TS_coeff_neg`/`TS_congr`
  (`Defs/TS`); `iota_jq`, `coeffEmb_qExpand`, `qExpand_coeff_mul`,
  `qExpand_coeff_of_not_dvd`, `qExpand_qExpand`, `qExpand_congr` (`Defs/Laurent`,
  `Defs/PhiAtSlot`); `cycUnit`/`cycUnit_spec` (`Defs/Cyclotomic`); `coeff_jq_neg_one`;
  `modularFunctionFieldFull`, `jqd_mem_full`, `jqN_one`; and mathlib's
  `algHomAdjoinIntegralEquiv`, `adjoin.powerBasis.exists_eq_aeval'`,
  `adjoin_induction`, `minpoly.dvd`/`two_le_natDegree_iff`, `Polynomial.roots.le_of_dvd`,
  `Multiset.nodup_of_le`, `Polynomial.Splits.of_dvd`, `Polynomial.mem_roots`.
- **Base.** `finrank_adjoin_jqN_prime_of_not_mem` (**T16**);
  `finrank_adjoin_jqN_eq_of_prime` (ported, `ModularPolynomialUniqueness.lean`);
  `phiAtSeed`/`_map`/`_monic`/`_natDegree`/`_jq_eval` (T14);
  `roots_prime_at_slot`/`_nodup`/`_roots_nodup`, `isRoot_prime_at_slot_iff` (T14);
  `exists_phiIrreducible_evalSymm` (T12); `aeval_intermediateField_eq_zero`,
  `qExpand_qTwist_notMem_range_qExpand` (T14); `TS_injective`, `iota_jqN`;
  and the T4 engine `mem_range_of_eval_eq_const`
  (`FLTForHuman/FieldTheory/CommonRoot.lean:111`).

## 3. The mathlib-first audit

Audited against the pinned `v4.34.0`. Like T16, this is a **glue topic with no new
engine**: the two engines are T4's `mem_range_of_eval_eq_const` (base) and the
minpoly/`algHomAdjoinIntegralEquiv` machinery T15/T16 already exercise (tower).

| pin piece | mathlib / port | verdict |
|---|---|---|
| `step_contradiction`'s core | `mem_range_of_eval_eq_const`, `CommonRoot.lean:111` (T4) | **import** |
| the tower's root transport | `isRoot_prime_at_slot_iff` + `splits_prime_at_slot` (T13/T14) | call |
| `chain_extend`'s extension | `IntermediateField.algHomAdjoinIntegralEquiv`, `adjoin.powerBasis`, `PowerBasis.exists_eq_aeval'`, `adjoin_induction` | call, no replacement |
| minpoly bookkeeping | `minpoly.dvd`, `minpoly.two_le_natDegree_iff`, `Polynomial.roots.le_of_dvd`, `Multiset.nodup_of_le`, `Polynomial.Splits.of_dvd`, `Polynomial.map_dvd` | call |
| `nat_ne_of_mul`, `mem_range_qExpand_of_mul`, `range_qExpand_congr` | none — five-line arithmetic/range glue | port |
| exponent arithmetic in `chain_endgame` | `Nat.sub`, `pow_succ`, `omega`, `ring`, `TS_injective` | port (the stall-prone part) |

**Headline.** No mathlib-absent lemma and no new import beyond what T14/T15/T16
already bring; the value of this audit is the recorded negatives, so the topic is
not re-searched later.

## 4. Module

One module, because the topic is one mathematical role — non-membership — and
both nodes share every import once T16 has landed:

| module | gains | imports |
|---|---|---|
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Nonmembership.lean` **(new)** | the tower: `nat_ne_of_mul`, `mem_range_qExpand_of_mul`, `range_qExpand_congr`, `chainField` + its five lemmas, `chain_extend`, `chain_endgame`, `jqN_pow_not_mem_adjoin_full_key`, public `jqN_pow_not_mem_adjoin_full`; and the base: `step_contradiction`, `jqN_prime_not_mem_adjoin_key`, public `jqN_prime_not_mem_adjoin` | `Defs/PhiAtSlot`, `Defs/TS`, `Defs/Laurent`, `Defs/Cyclotomic`, `Defs/Fields`, `Defs/Jq`, `ModularCurve/PhiSlotRoots`, `ModularCurve/PhiGenSplits`, `ModularCurve/ModularPolynomialProperties` (`exists_phiIrreducible_evalSymm`), `ModularCurve/ModularPolynomialUniqueness` (`finrank_adjoin_jqN_eq_of_prime`), `FunctionFieldGeneration/DegreeStep` (T16's `finrank_adjoin_jqN_prime_of_not_mem`), `FieldTheory/CommonRoot` (`mem_range_of_eval_eq_const`) |

`Nonmembership.lean` sits beside `Target`/`Collapse`/`Spine`/`Descent`/`DegreeStep`.
Declare the tower first, then the base, so a stall is isolated to one half. If the
tower proves unmanageable in place, split `chain_extend` and its two range helpers
into a private companion module and say so in the log — but do not pre-split.

## 5. Prerequisites — public, verified

Tower, all already public: `isRoot_prime_at_slot_iff`,
`roots_prime_at_slot(_nodup)(_roots_nodup)`, `prod_form_ne_zero` (`PhiSlotRoots`);
`PhiGen.splits_prime_at_slot` (`PhiGenSplits`); `exists_phiIrreducible_evalSymm`;
`TS` family (`Defs/TS`); `iota_jq`, `phiAtSeed` + its lemmas,
`qExpand_qTwist_notMem_range_qExpand`, `aeval_intermediateField_eq_zero`
(`Defs/PhiAtSlot`); `coeffEmb_qExpand` (`Defs/Laurent`); `cycUnit`/`cycUnit_spec`
(`Defs/Cyclotomic`); `modularFunctionFieldFull`/`jqd_mem_full` (`Defs/Fields`);
`coeff_jq_neg_one`, `jqN_one`, `jqN_congr` (`Defs/Jq`).

Base, additionally: `finrank_adjoin_jqN_prime_of_not_mem` (**T16's
`DegreeStep.lean`, public by the time this topic opens**),
`finrank_adjoin_jqN_eq_of_prime` (`ModularPolynomialUniqueness.lean`),
`mem_range_of_eval_eq_const` (`CommonRoot.lean`). Nothing needed is `private`;
verify the T16 declaration is public before writing the base, and if T16 shipped
it under a different name, re-point and record.

## 6. Verification

1. **`#print axioms`** clean on both public declarations.
2. **Statement checker.** Add to `SOURCES`
   `Them_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` and
   `Them_ModularCurve_jqN_prime_not_mem_adjoin.lean`; both are public wrappers, so
   they verify by direct name match. Report the before/after count (T16 leaves it
   after its three wrappers; T15 left **278**).
3. **`PORT_FILES`** gains `FunctionFieldGeneration/Nonmembership.lean`.
4. **The wire test — Zone O.** T15 took Zone M, T16 Zone N; this takes the next
   free zone in `spec/ModularCurveConsumer.lean`. The meaningful test is the
   `Inputs` composition, as in Zones M/N: build a partially discharged `Inputs`
   with `jqN_pow_not_mem_adjoin_full := ModularCurve.jqN_pow_not_mem_adjoin_full`
   alongside T16's `relfinrank_full_eq_mul`, so the debt visibly drops to three
   fields. Add the base's statement to the zone as a second (non-`Inputs`) entry.
5. **Build.** `lake build` green, 0 warnings, no `sorry`; library-wide `grep`.
6. **README** gains the module; **`PORTING-FFG.md` §7.8** marks T17 done and
   records the measured cost; `logs/ffg-port.md` gains T17's entry.

## 7. Budget and route risks

New pin content is **≈741 lines**: tower ≈517 (`chain_extend` 180 +
`chain_endgame` 243 + helpers/chainField ≈ 87 + wrapper 7) and base ≈224
(`step_contradiction` 151 + key 65 + wrapper 8). Six tower helpers (≈43) and two
base helpers (≈20) are T14's and are dropped, not ported. Expect **≈750–950 port
lines** in **one module** and **two goal rounds** — round 1 the tower, round 2 the
base. This is one session end to end; nothing waits on a parallel effort.

**Route risks, in the order they will bite.**

- **`chain_extend`'s `RingHom` literal (pin 657–702).** The map is built as an
  explicit structure `{ toFun := fun z => ψ ⟨z.1, hle z.2⟩, map_one' := … }`, and
  the `hle` coercion is an `adjoin_induction` from
  `adjoin ℚ (F ∪ {jqN (d*p)})` to `adjoin F {jqN (d*p)}`. This is the
  `FunLike`/transparency family of §1's catalogue and T5's log §2.2. Transcribe
  the shape; if `simp` cannot see through it, state the coercion as a named
  monomorphic bridge rather than fighting it.
- **The `Algebra F (LaurentSeries K) := σ.toAlgebra` instance (pin 552–553).**
  Same device T15 used; that closed on the first build, so copy the shape and do
  not re-derive.
- **`chain_endgame`'s exponent arithmetic (pin 906–959).** The `TS_injective`
  comparisons, `M * (p*p) = M`-style `ring`/`omega` goals, and the final
  `q^{-p^a}` coefficient clash are where the proof is longest and least
  structured. This is the topic's biggest single risk. The pin's local
  `maxHeartbeats 3200000` is **not** transcribed (the global cap is 4M); if the
  declaration still times out, quarantine and bisect, do not raise the cap.
- **`algHomAdjoinIntegralEquiv` / `powerBasis.exists_eq_aeval'` (pin 632–637,
  693–695).** The same API T15's descent and T16's pow-succ node use. If T15's
  `Descent.lean` already has the monomorphic restatement, import it; otherwise
  transcribe the pin's call.
- **`step_contradiction`'s engine instantiation (base 525–567).** The
  `mem_range_of_eval_eq_const` call shares its *engine* with T19's private lemma
  (pin `S_…jqN_prime_not_mem_full.lean:1926`) but not its root list: T17's is the
  `p+1` roots of `Φ_p(jq, ·)`, T19's the `ψ(M)` slots of `jqN M`. Import the
  engine once from `FieldTheory/CommonRoot.lean`; do not restate it, and note for
  T19 that T17 landed first. The `hkill` root-pinning below is the concrete part.
- **The `hkill` root-pinning (base 508–523).** It combines
  `isRoot_prime_at_slot_iff` with `qExpand_qTwist_notMem_range_qExpand`; the
  `hrpZ : ¬ ((r : ℤ) ∣ (p : ℤ))` cast is the fiddly line.

## 8. Definition of done (T17)

- [ ] `FunctionFieldGeneration/Nonmembership.lean` created, both public statements
      verbatim from their wrappers, tower declared before base;
- [ ] no T14 helper re-copied (the six tower / two base helpers are imported);
- [ ] `lake build` green, 0 warnings, no `sorry`;
- [ ] `#print axioms` clean on both public declarations;
- [ ] both wrappers in `SOURCES`, 0 mismatched, 0 missing; `PORT_FILES` updated;
- [ ] Zone O recorded and green, with the `Inputs` composition as its wire test
      and the debt drop recorded;
- [ ] README, `PORTING-FFG.md` §7.8 and `logs/ffg-port.md` updated;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The debt** — confirm `jqN_pow_not_mem_adjoin_full` is an `Inputs` field
   discharged, and that the structure was not touched.
2. **The order** — did the tower close before the base was started, and did any
   stall stay isolated to one half? Was the pre-split avoided?
3. **The routes** — did `chain_extend`'s `RingHom` literal close as-is? Did
   `chain_endgame` need the pin's heartbeat bump (it should not, with the 4M
   global cap)? Which declaration was the stall point?
4. **The shared engine** — confirm `mem_range_of_eval_eq_const` was imported from
   `CommonRoot.lean`, not restated, and note for T19 that T17 landed first.
5. **The cost** — rounds, declarations, lines, ratio against ~741, and the
   corrected T17 figure for §7.8.
6. **The API note** — if the base was deferred as non-capstone API, say so
   explicitly and record the consequence for `relfinrank_adjoin_primes` /
   `relfinrank_full_mul_prime` / `jqN_sq_not_mem_adjoin`.

## 10. Where this sits

T17 is the fourth `Inputs`-field topic. With it and T16, `Tight` has both its
degree and its non-membership, leaving T18 (generation and the squarefree degree)
and T19 (the slot product, which supplies the `htw`/`hsp` that T15 left as
arguments and discharges the two remaining fields). The dependency order, the T19
route win and the drop/keep decisions are
[PORTING-FFG.md](../../PORTING-FFG.md) §7.8.
