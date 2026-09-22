# Topic 18: one new generator per prime power

*(Originally scoped as "generation and the squarefree degree"; the squarefree
degree block is now a deferred optional API tail — §1.)*

**Status: work order, ready to open — scope settled (2026-09-22): node 1 only.**
T14–T17 are done, committed and green; the `Inputs` debt is **3**. T18's mandatory
scope is the single `Inputs` field `full_eq_adjoin_full_div_prime` (debt 3 → 2)
plus the shared `jqN_mem_of_div_primes`. The other five nodes are reclassified as
a **deferred optional API tail** (§1), and T19 adopts the Lean-verified `gen_prime`
substitution instead of `functionFieldGeneration_of_squarefree`.

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
> - **Never raise `maxHeartbeats`.** The project's global cap is `4000000`
>   (`lakefile.lean`); none of this topic's pin files raises it locally, so no
>   `set_option` is transcribed. The usual stall cause is a `FunLike`-quantified
>   lemma instantiated at a bare function type — restate it over the concrete
>   function instead (T5's log §2.2).

**Audience.** A fresh session taking T18. Read, in this order:

1. [PORTING-FFG.md](../PORTING-FFG.md) §7.8 and §1;
2. [math/010](../../../math/010-function-field-generation.md) §5–§6b — the
   generation walk and the squarefree degree count;
3. [TOPIC-descent.md](TOPIC-descent.md) (T15), [TOPIC-degree-step.md](TOPIC-degree-step.md)
   (T16) and [TOPIC-nonmembership.md](TOPIC-nonmembership.md) (T17) — the three
   inputs this topic composes;
4. [logs/audit-prelude-bridges.md](../../logs/audit-prelude-bridges.md) §(b)
   (`w1_relfinrank_insert`, `toAdjoin_eq_minpoly`) and
   [logs/audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md);
5. [porting-playbook.md](../../porting-playbook.md) §3.9, §3.11, §7.3.

## 1. Goal, and why this topic

**Goal (mandatory): one new generator per prime power.** Port
**`full_eq_adjoin_full_div_prime`** — for `` $`p \nmid M`$ ``,
`` $`F^{\mathrm{full}}_{Mp^{a+1}} = \mathbb{Q}\bigl(F^{\mathrm{full}}_{Mp^{a}},\ j(q^{p^{a+1}})\bigr)`$ ``.
**This is the `Inputs` field**: with it the debt is **3 → 2**. The engine is the
**two-prime descent** `jqN_mem_of_div_primes`: given `` $`j(q^{d/p})`$ `` and
`` $`j(q^{d/q})`$ `` both in a field, `` $`j(q^d)`$ `` is — the unique-common-root
argument run with `` $`\Phi_p`$ `` and `` $`\Phi_q`$ ``. Port the descent **once**
(both pin generation files carry a verbatim 133-line copy) and the strong induction
`w1_jqN_mem_adjoin_top_insert`.

**Deferred (optional API tail — not ported now).** The five remaining nodes of the
original six-node topic:

2. **`full_eq_adjoin_primes`** — `` $`F^{\mathrm{full}}_N = \mathbb{Q}(j, j(q^p) : p \mid N)`$ ``
   for squarefree `` $`N`$ ``.
3. **`dedekindPsi_of_squarefree`** — `` $`\psi(N) = \prod_{p \mid N}(p+1)`$ ``.
4. **`relfinrank_full_of_squarefree`** — `` $`[F^{\mathrm{full}}_N : \mathbb{Q}(j)] = \psi(N)`$ ``.
5. **`finrank_adjoin_jqN_eq_of_squarefree`** — `` $`[\mathbb{Q}(j)(j(q^N)) : \mathbb{Q}(j)] = \psi(N)`$ ``,
   the `IsLevel`/`eq_of_isRoot_of_isLevel` count.
6. **`functionFieldGeneration_of_squarefree`** — `` $`F_N = F^{\mathrm{full}}_N`$ ``.

**Decision and evidence (2026-09-22, re-derived after T17 landed).** Nodes 2–6 are
deferred because:

- **They have exactly one consumer outside themselves.** T19's file uses
  `functionFieldGeneration_of_squarefree` at
  `S_ModularCurve_jqN_prime_not_mem_full.lean:1638` (twin at
  `minpoly_jqN_map_eq_prod_slots.lean:1638`) to obtain `Gen p`; the file's import
  at line 10 is its only other mention. `finrank_adjoin_jqN_eq_of_squarefree` has
  **no** external consumer at all; `dedekindPsi_of_squarefree`,
  `relfinrank_full_of_squarefree` and `full_eq_adjoin_primes` are consumed only
  inside the cluster (the other grep hits are the parallel pin duplicate files,
  i.e. the same development).
- **The replacement is Lean-verified in the port's own vocabulary.**
  `gen_prime (p) : Gen p` and the `` $`d = p`$ `` branch of T19's `hallp`
  (`Tight p ∧ Gen p`) both elaborate against the landed T14–T17. The verification
  was first done on a throwaway scratch file (since removed — scratch files are not
  tracked), and `gen_prime` is now real code in `Defs/Fields.lean` beside the
  promoted `tight_one`/`gen_one`. `Gen p` is definitional: both sides are
  `` $`\mathbb{Q}(j, j(q^p))`$ ``. T19 replaces the pin's three lines at 1637–1639
  with `gen_prime p`; **its statements do not change**.
- **Nothing on the capstone or §2.1's five-node outbound tier needs the cluster.**
  math/010 §8 already flags the squarefree degree count as redundant mathematics:
  the general strong induction (`hall_all`, already proved in `Spine.lean`) covers
  every `` $`N`$ ``.
- **The substitution is cheap.** `gen_prime` (≈12 lines) into `Defs/Fields.lean`
  beside `gen_one`, plus promoting `tight_one`/`gen_one` out of `Spine.lean`
  (≈35 lines, both already proved). It replaces ≈600 pin lines and the topic's one
  hard proof (`eq_of_isRoot_of_isLevel`, 164 lines).

The one API cost is that `relfinrank_adjoin_primes` and
`relfinrank_full_mul_prime` — which have real downstream consumers
(`relfinrank_full_sq`, `heckeDivBar_cuspidalDivisor_of_prime`) — are not ported.
Neither is in §2.1's measured outbound tier, and either can be added later for
≈150 pin lines without the `IsLevel` work. §2 keeps the full inventory so a future
effort does not re-scout.

## 2. The scouted inventory

Six pin files. Both generation files carry a **verbatim duplicate** of
`jqN_mem_of_div_primes` (133 lines) at lines 397–529, as does T15's
`modularFunctionField_eq_full_of.lean`; the port has it nowhere yet, so T18 ports
it **once**, for node 1 (the deferred node 2 would have been its second consumer).
The three other files are independent developments.

The inventory covers the **deferred tail** as well, so a future effort does not
re-scout. The mandatory part is the first row plus the shared descent.

| node | pin file | node span | topic-own | scope |
|---|---|---|---|---|
| `full_eq_adjoin_full_div_prime` | `S_…_full_eq_adjoin_full_div_prime.lean` (624) | 601–620 | ≈88 | **mandatory** (`Inputs`) |
| `full_eq_adjoin_primes` | `S_…_full_eq_adjoin_primes.lean` (600) | 579–596 | ≈67 | deferred |
| `dedekindPsi_of_squarefree` | `S_…_dedekindPsi_of_squarefree.lean` (70) | 44–65 | ≈22 | deferred |
| `relfinrank_full_of_squarefree` | `S_…_relfinrank_full_of_squarefree.lean` (526) | 498–504 | ≈81 | deferred |
| `finrank_adjoin_jqN_eq_of_squarefree` | `S_…_finrank_adjoin_jqN_eq_of_squarefree.lean` (864) | 687–860 | ≈431 | deferred |
| `functionFieldGeneration_of_squarefree` | `S_…_functionFieldGeneration_of_squarefree.lean` (55) | 21–34 | ≈14 | deferred |

**Mandatory scope ≈221 pin lines**: `jqN_mem_of_div_primes` (133) +
`w1_jqN_mem_adjoin_top_insert` (68) + node 1 (20). **Deferred tail ≈615 pin
lines**: nodes 2–6 (≈615 after the drops in §2.1) plus optionally
`relfinrank_full_mul_prime` (18). The full six-node figure is ≈836, and §7.8's
own-column sum of ≈1,074 counts the descent **twice** and includes ≈48 lines of
dead helpers, so it is a pin-side upper bound, not the port estimate.

### 2.1 Helpers by file

| helper | pin | span | status |
|---|---|---|---|
| `jqN_mem_of_div_primes` | both generation files 397–529 | 133 | **port once** — the shared two-prime descent |
| `jqN_congr'` | full_div_prime 530–532 | 3 | **redundant** — `Defs/Jq.lean` `jqN_congr` |
| `w1_jqN_mem_adjoin_top_insert` | full_div_prime 533–600 | 68 | port |
| `w1_jqN_mem_adjoin_primeFactors` | primes 530–578 | 49 | port **(tail)** |
| `psi_prime_pow_aux` | dedekindPsi 15–38 | 24 | **drop (tail)** — dead for this node; the port's `dedekindPsi_prime_pow` (`Defs/Jq.lean:221`) is the public one |
| `dedekindPsi_prime_pow` | dedekindPsi 39–43 | 5 | **drop (tail)** — already public in the port |
| `w1_mem_adjoin_of_mem`/`w1_jq_mem`/`w1_jqN_mem`/`w1_adjoin_mono` | relfinrank 399–423 | 25 | port **(tail)** (4 short Finset/adjoin helpers) |
| `w1_relfinrank_insert` | relfinrank 424–468 | 45 | **reuse** the port's generic `Defs/Fields.lean` `w1_relfinrank_insert` (T16) — the pin's is the prime-insert instance; only the set-equality + degree call are new (≈20) |
| `relfinrank_adjoin_primes` | relfinrank 469–497 | 29 | port **(tail)** (it has a `Theorems/` wrapper and is consumed by `relfinrank_full_sq`) |
| `relfinrank_full_mul_prime` | relfinrank 505–522 | 18 | **optional API** — a `Theorems/` wrapper with one downstream consumer (`heckeDivBar_cuspidalDivisor_of_prime`); not in the 17 nodes |
| `IsLevel` + `isLevel_iota`/`isLevel_one` | finrank 406–416 | 11 | port |
| `exists_pow_eq_of_coprime` | finrank 417–425 | 9 | port via mathlib `exists_pow_eq_self_of_coprime` (≈5) |
| `prime_step_facts`/`level_exponent_eq` | finrank 426–440 | 15 | port |
| `isLevel_mul_of_isRoot` | finrank 441–483 | 43 | port |
| `eq_of_isRoot_of_isLevel` | finrank 484–647 | 164 | port — **hard half A** |
| `toAdjoin_eq_minpoly` | finrank 668–686 | 19 | port (the `phiAtSeed data jGen` form; the port's `ModularPolynomialUniqueness.lean` has the `data.toAdjoin` form privately — bridge or restate) |
| `phiIrreducible_of_squarefree` | functionFieldGeneration 35–50 | 16 | **drop** — no consumer anywhere in the pin, no `Theorems/` wrapper |
| `phiAtSeed_eval_of_injective`/`_symm`, `jqN_congr`, `phiAtSeed_jqN_eval_down` | finrank 648–667 | ≈18 | T14 — `Defs/PhiAtSlot.lean`, `Defs/Jq.lean` |

### 2.2 What each node uses

- **`full_eq_adjoin_full_div_prime`**: `w1_jqN_mem_adjoin_top_insert`;
  `modularFunctionFieldFull`, `jqd_mem_full`, `full_degeneracy_le` (`Defs/Fields`);
  Nat API `Nat.Coprime.pow_right`, `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`,
  `Nat.dvd_prime_pow`, `Nat.minFac*`, `Nat.div_dvd_of_dvd`.
- **`full_eq_adjoin_primes`**: `w1_jqN_mem_adjoin_primeFactors`,
  `Squarefree.squarefree_of_dvd`, `Nat.mem_primeFactors`,
  `Nat.exists_prime_and_dvd`, `Nat.prime_of_mem_primeFactors`.
- **`dedekindPsi_of_squarefree`**: `dedekindPsi_prime`,
  `dedekindPsi_mul_of_coprime`, `Nat.recOnPosPrimePosCoprime`,
  `Nat.primeFactors_mul`, `Finset.prod_union`, `Nat.squarefree_mul_iff`.
- **`relfinrank_full_of_squarefree`**: `full_eq_adjoin_primes`,
  `relfinrank_adjoin_primes` (which uses the port's generic
  `w1_relfinrank_insert`, T16's `finrank_adjoin_jqN_prime_of_not_mem`, and
  T17's `jqN_prime_not_mem_adjoin`), `dedekindPsi_of_squarefree`,
  `IntermediateField.relfinrank_mul_relfinrank`.
- **`finrank_adjoin_jqN_eq_of_squarefree`**: `full_eq_adjoin_primes`,
  `relfinrank_full_of_squarefree`, `dedekindPsi_of_squarefree`,
  `IntermediateField.extendScalars_adjoin`, `relfinrank_eq_finrank_of_le`,
  `mem_extendScalars`, `exists_phiIrreducible_evalSymm` (T12),
  `roots`/`IsLevel` API, `eq_of_isRoot_of_isLevel`, `toAdjoin_eq_minpoly`.
- **`functionFieldGeneration_of_squarefree`**: `functionFieldGeneration_iff_full_eq`
  (T2), `relfinrank_modularFunctionField` (`Defs/Fields`),
  `finrank_adjoin_jqN_eq_of_squarefree`, `relfinrank_full_of_squarefree`,
  `relfinrank_mul_relfinrank`, `relfinrank_eq_one_iff`.

## 3. The mathlib-first audit

Audited against the pinned `v4.34.0`. A **glue topic**: the engines are T4's
`mem_range_of_unique_common_root` (via `jqN_mem_of_div_primes`) and the
slot/minpoly API the earlier topics already exercise. No new engine and no
mathlib-absent lemma.

| pin piece | mathlib / port | verdict |
|---|---|---|
| `exists_pow_eq_of_coprime` | `exists_pow_eq_self_of_coprime` (`GroupTheory/OrderOfElement.lean:332`) + `orderOf_dvd_of_pow_eq_one` (`:273`) | **replace**, ≈9 → 5 |
| `w1_relfinrank_insert` | the port's generic `Defs/Fields.lean` `w1_relfinrank_insert` (T16) | **reuse**; only the prime-insert set identity is new |
| `toAdjoin_eq_minpoly` | `eq_of_monic_of_dvd_of_natDegree_le` + `adjoin.finrank` + `dedekindPsi_prime` | port (same proof as the port's private `toAdjoin` form) |
| the generation inductions | `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`, `Nat.dvd_prime_pow`, `Nat.minFac*`, `Nat.squarefree_mul_iff`, `Nat.primeFactors_mul`, `Finset.prod_union` | call |
| the degree count | `extendScalars_adjoin`, `relfinrank_eq_finrank_of_le`, `relfinrank_mul_relfinrank`, `relfinrank_eq_one_iff`, `IntermediateField.finrank_le_of_le_right` | call |
| `eq_of_isRoot_of_isLevel` | `IsPrimitiveRoot.eq_pow_of_pow_eq_one`/`dvd_of_pow_eq_one`, `TS_injective`, `isRoot_prime_at_slot_iff` | port — no shorter route |

**Headline.** Two small real wins (`exists_pow_eq_of_coprime`, the generic
`w1_relfinrank_insert`); everything else is transcription plus the two drops
(`psi_prime_pow_aux` and the local `dedekindPsi_prime_pow`, both dead here;
`phiIrreducible_of_squarefree`, consumerless).

## 4. Module

One module for the mandatory scope; the deferred tail, if ever ported, extends it
(or gets its own module — the seam is generation vs squarefree degree):

| module | gains | imports |
|---|---|---|
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Generation.lean` **(new)** | `jqN_mem_of_div_primes` (once), `w1_jqN_mem_adjoin_top_insert`, public `full_eq_adjoin_full_div_prime` | `Defs/PhiAtSlot`, `Defs/TS`, `Defs/Laurent`, `Defs/Fields`, `Defs/Jq`, `ModularCurve/PhiSlotRoots`, `ModularCurve/PhiGenSplits`, `ModularCurve/ModularPolynomialProperties`, `FieldTheory/CommonRoot` |

Declare the descent first, then the induction, then the node. (`Defs/Cyclotomic`,
`Defs/Jq`'s `cycUnit`/`cycUnit_spec`, and `exists_phiIrreducible_evalSymm` are what
the descent's `jqN_mem_of_div_primes` call needs; the rest of the import list is
T14's vocabulary.) The deferred tail's dependencies are in §2.2 and §3 for a
future session.

## 5. Prerequisites — public, verified

**Mandatory.** `modularFunctionFieldFull`, `jqd_mem_full`, `full_degeneracy_le`
(`Defs/Fields`); `phiAtSeed*` (`Defs/PhiAtSlot`); `roots_prime_at_slot*`,
`isRoot_prime_at_slot_iff` (`PhiSlotRoots`); `PhiGen.splits_prime_at_slot`
(`PhiGenSplits`); `exists_phiIrreducible_evalSymm` (`ModularPolynomialProperties`);
`cycUnit`/`cycUnit_spec` (`Defs/Cyclotomic`); `TS` family (`Defs/TS`),
`coeffEmb_qExpand` (`Defs/Laurent`); `jqN_congr`, `jqN_one`, `coeff_jq_neg_one`
(`Defs/Jq`); `Polynomial.mem_range_of_unique_common_root`
(`FieldTheory/CommonRoot`). Nothing needed is `private`.

**Tail, additionally** (only if nodes 2–6 are ever ported): `dedekindPsi_prime`,
`dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow` (`Defs/Jq`);
`relfinrank_modularFunctionField`, the generic `w1_relfinrank_insert`
(`Defs/Fields`, T16); `finrank_adjoin_jqN_prime_of_not_mem`,
`finrank_adjoin_jqN_eq_of_prime` (T16 / `ModularPolynomialUniqueness`);
`jqN_prime_not_mem_adjoin` (T17); `functionFieldGeneration_iff_full_eq`
(`Collapse`). All public.

## 6. Verification

1. **`#print axioms`** clean on `full_eq_adjoin_full_div_prime`, on `gen_prime`, and
   on any tail node that is ported.
2. **Statement checker.** Append `Theorems/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean`
   to `SOURCES` (plus the tail wrappers only if nodes 2–6 are ported). Report
   before/after; T17 left it at **290**.
3. **`PORT_FILES`** gains `FunctionFieldGeneration/Generation.lean`.
4. **The wire test — Zone P.** T17 took Zone O. Build a partially discharged
   `Inputs` with `full_eq_adjoin_full_div_prime :=
   ModularCurve.full_eq_adjoin_full_div_prime` alongside T15–T17's four fields, so
   the debt visibly drops to **two**. Add a `#check`/`example` that `gen_prime`
   gives `Gen p` at a concrete prime, since it is T19's substitution.
5. **The T19 prerequisite lands here.** Promote `tight_one`/`gen_one` out of
   `Spine.lean` into `Defs/Fields.lean` (they are `private` today, and T19's
   `hallp` needs the `d = 1` branch) and add `gen_prime` beside `gen_one`. This is
   what makes T19's replacement of the pin's line 1638 a two-line edit instead of
   a re-derivation.
6. **Build.** `lake build` green, 0 warnings, no `sorry`; library-wide `grep`.
7. **README** gains the module and `gen_prime`; **`PORTING-FFG.md` §7.8** marks T18
   done, records the measured cost, and records the §1 scope decision; T19's row
   gains the `gen_prime` note; `logs/ffg-port.md` gains T18's entry.

## 7. Budget and route risks

**Mandatory scope is ≈221 pin lines**: `jqN_mem_of_div_primes` (133) +
`w1_jqN_mem_adjoin_top_insert` (68) + node 1 (20), plus the `gen_prime` and
`tight_one`/`gen_one` promotions of §6 (≈50, already-proved lines moved). Expect
**≈250–320 port lines** in one module and **one goal round**.

**Deferred tail: ≈615 pin lines** (nodes 2–6 after the drops below), whose hard
proof is `eq_of_isRoot_of_isLevel` (164 lines) and whose port estimate is
≈650–750. Its route risks are marked **(tail)** below.

**Route risks.** The `jqN_mem_of_div_primes` bullet is the mandatory scope's
only real risk; the rest are marked **(tail)** and are kept for a future session.

- **(mandatory) `jqN_mem_of_div_primes` (133 lines).** Port it **once**, in the
  generation block. Its hypotheses are the same in both pin copies
  (`S_…_full_eq_adjoin_full_div_prime.lean:397` and
  `S_…_full_eq_adjoin_primes.lean:397`); diff them before transcribing, then record
  the `grep -c` for the second copy (the deferred tail would have been its other
  consumer). The proof is the unique-common-root engine on `` $`\Phi_p`$ `` and
  `` $`\Phi_q`$ ``, with the slot API T14 already exposes.
- **(tail) `eq_of_isRoot_of_isLevel` (pin 484–647, 164 lines).** The longest and
  least structured proof in the original topic: it shows the `IsLevel` conjugates
  of `` $`j(q^N)`$ `` are distinct by pushing `` $`\Phi_q`$ ``'s slot description
  through a primitive `` $`N^2`$ ``-th root and comparing exponents modulo
  `` $`q`$ `` (the `b = b'` case split at 553–647). The audit found no shorter
  route from `CommonRoot`'s engines.
- **(tail) `finrank_adjoin_jqN_eq_of_squarefree`'s counting (pin 687–860).** The
  `CyclotomicField (N*N)` coefficient extension with
  `ι = coeffEmb ∘ qExpand (N*N)`, the installed
  `Algebra ℚ⟮jq⟯ (LaurentSeries K)` instance, the `extendScalars` identification
  `hE`, and the final `ψ(N)`-root count against `hup`. Copy T15/T16's instance
  shape.
- **(tail) `w1_relfinrank_insert`.** Do **not** port the pin's 45-line version. The
  port's generic `Defs/Fields.lean` lemma (from T16) already gives
  `relfinrank E (adjoin ℚ (insert α E)) = finrank E (adjoin E {α})`; the
  prime-insert instance needs only the set equality
  `insert jq {jqN q : q ∈ insert p S} = insert (jqN p) (adjoin-set)` and then
  T16's `finrank_adjoin_jqN_prime_of_not_mem` with T17's
  `jqN_prime_not_mem_adjoin`.
- **(tail) `toAdjoin_eq_minpoly`.** The pin states it with `phiAtSeed data jGen`;
  the port's private version (`ModularPolynomialUniqueness.lean`) states
  `data.toAdjoin = minpoly`. Prove the `phiAtSeed data jGen = data.toAdjoin`
  bridge once, or restate in the `phiAtSeed` form; do not leave two public copies.
- **(tail) `exists_pow_eq_of_coprime`.** Replace with mathlib
  `exists_pow_eq_self_of_coprime` + `orderOf_dvd_of_pow_eq_one`.
- **(tail) the dead `dedekindPsi` helpers.** `psi_prime_pow_aux` and the local
  `dedekindPsi_prime_pow` are not used by `dedekindPsi_of_squarefree`; the port
  already has the public `dedekindPsi_prime_pow` (`Defs/Jq.lean:221`). Drop both.

## 8. Definition of done (T18)

- [ ] `FunctionFieldGeneration/Generation.lean` created, the one public node
      `full_eq_adjoin_full_div_prime` verbatim from its wrapper;
- [ ] `jqN_mem_of_div_primes` exists **once** in the port (one declaration); the
      second pin copy — the deferred tail's would-be consumer — is dropped with a
      recorded `grep -c`;
- [ ] `gen_prime` lands in `Defs/Fields.lean` beside `gen_one`, and `tight_one`/
      `gen_one` are promoted out of `Spine.lean` (the T19 substitution
      prerequisite);
- [ ] nodes 2–6 are **not** ported, and the decision is recorded as intentional
      (optional API tail), not an omission;
- [ ] `lake build` green, 0 warnings, no `sorry`;
- [ ] `#print axioms` clean on `full_eq_adjoin_full_div_prime` and `gen_prime`;
- [ ] the wrapper in `SOURCES`, 0 mismatched, 0 missing; `PORT_FILES` updated;
- [ ] Zone P recorded and green, with the `Inputs` composition (debt 3 → 2) and a
      `gen_prime` example as its wire test;
- [ ] README, `PORTING-FFG.md` §7.8 (including T19's `gen_prime` note) and
      `logs/ffg-port.md` updated;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The debt** — confirm `full_eq_adjoin_full_div_prime` is an `Inputs` field
   discharged (3 → 2) and the structure was not touched.
2. **The substitution** — confirm `gen_prime` and the `tight_one`/`gen_one`
   promotions landed, and state the exact T19 edit they enable (replace the pin's
   lines 1637–1639 with the direct `Tight p` proof plus `gen_prime p`).
3. **The scope** — confirm nodes 2–6 were deferred as intended, with the evidence
   of §1 re-checked, and that no consumer on the capstone or the §2.1 outbound tier
   was left unsatisfied.
4. **The dedup** — `jqN_mem_of_div_primes` is one declaration; the second copy has
   a recorded `grep -c`.
5. **The route** — did the descent transcribe as-is against T14's slot API?
6. **The cost** — rounds, declarations, lines, ratio against ≈221 + the ≈50-line
   promotion, and the corrected T18 figure for §7.8.

## 10. Where this sits

T18 is now a short topic: it discharges the fifth `Inputs` field (debt 3 → 2) and
lands the `gen_prime` substitution T19 needs. The squarefree generation/degree
block — nodes 2–6 — is explicitly deferred optional API; the mathematics it
formalizes is the redundant squarefree branch that math/010 §8 flags and that
`hall_all` already covers. T19 (the slot product and `jqN_prime_not_mem_full`) is
then the last topic before the capstone, and it follows T17 directly rather than
waiting on this block. The dependency order, the T19 route win and the drop/keep
decisions are [PORTING-FFG.md](../PORTING-FFG.md) §7.8.
