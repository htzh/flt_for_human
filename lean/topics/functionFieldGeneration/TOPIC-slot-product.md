# Topic 19: the slot product and prime non-membership

**Status: work order, ready to open.** T14–T18 are done, committed and green; the
`Inputs` debt is **2**. T19 discharges the last two fields
(`minpoly_jqN_map_eq_prod_slots` and `jqN_prime_not_mem_full`), so the debt is
**2 → 0** and the `Inputs` structure is fully discharged; T20 then constructs it.
T19's prerequisite is **T17, not T18**: T18 landed the route audit's `gen_prime`
substitution, so the pin's `functionFieldGeneration_of_squarefree p` call at
`S_ModularCurve_jqN_prime_not_mem_full.lean:1638` is replaced and the deferred
squarefree block is not needed.

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
>   (`lakefile.lean`); the pin raises it locally (`3200000`) only in
>   `chain_endgame`, which is T17's and already omitted. The usual stall cause is
>   a `FunLike`-quantified lemma instantiated at a bare function type — restate it
>   over the concrete function instead (T5's log §2.2). This topic's likely stall
>   is `rval_aux`'s 493-line `hslot_root`.

**Audience.** A fresh session taking T19 — the last topic before the capstone.
Read, in this order:

1. [PORTING-FFG.md](../../PORTING-FFG.md) §7.8, its "Audit outcomes", and §1;
2. [math/010](../../../math/010-function-field-generation.md) §3 and §6a — the
   slot description of the conjugates and the non-membership that reads it;
3. [TOPIC-slot-machinery.md](TOPIC-slot-machinery.md) (T14 — the vocabulary this
   topic instantiates), [TOPIC-nonmembership.md](TOPIC-nonmembership.md) (T17 —
   the same `CommonRoot` engine) and [TOPIC-generation.md](TOPIC-generation.md)
   (T18 — the `gen_prime` substitution this topic uses);
4. [logs/audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md)
   — the closed-form slot count, and
   [logs/audit-rval-aux-compressibility.md](../../logs/audit-rval-aux-compressibility.md)
   — `rval_aux`'s block map and what is *not* compressible;
5. [porting-playbook.md](../../porting-playbook.md) §3.5–§3.7, §3.9, §7.3.

## 1. Goal, and why this topic

**Goal.** Port the slot product and the prime non-membership that reads it.

1. **`minpoly_jqN_map_eq_prod_slots`** (an `Inputs` field, and the pin's
   `rval_aux`) — the explicit conjugate list: for a primitive `` $`M`$ ``-th root
   `` $`\zeta`$ ``,

   ```text
   (minpoly ℚ⟮jq⟯ (jqN M)).map (coeffEmb K ∘ qExpand ℚ M ∘ ℚ⟮jq⟯ ↪ ℒ)
     = ∏ a ∈ M.divisors, ∏ b ∈ (range (M/a)).filter (gcd (gcd a b) (M/a) = 1),
         (X − C (qExpand K (a*a) (qTwist (ζ^(b*a)) (coeffEmb K jq))))
   ```

   proved by strong induction on `` $`M`$ `` from T13's `splits_prime_at_slot`,
   with `Hall M` as the induction input. Its values are named `sv K ζ a b`, and
   the statement is the source of truth for *which* conjugate is which — the
   `root_shape`/`htw`/`hsp` side conditions T15 left as arguments, and the
   `IsLevel`-style slot analysis the deferred T18 tail would have used.
2. **`jqN_prime_not_mem_full`** (the last `Inputs` field) —
   `` $`j(q^p) \notin F_M^{\mathrm{full}}`$ `` for `` $`p \nmid M`$ ``, from `Hall M`.
   The proof reads the ψ(M) slot roots off node 1, writes
   `` $`j(q^p) = g(j(q^M))`$ `` with `` $`\deg g < \psi(M)`$ ``, shows `` $`g`$ ``
   constant on the slots (T4's `mem_range_of_eval_eq_const`), so
   `` $`j(q^p) \in \mathbb{Q}(j)`$ ``, contradicting T16's
   `` $`[\mathbb{Q}(j)(j(q^p)) : \mathbb{Q}(j)] = p+1`$ ``. The pin keeps this
   step in a **private M-arbitrary** `jqN_prime_not_mem_adjoin`; it is *not*
   T17's public Finset lemma (both are needed; the audit checked both directions).

**Why last.** Node 1's slot product is the shared root list; node 2 is the
non-membership built on it; together they are the last two `Inputs` fields, so
with them the conditional capstone becomes total on the port's side and T20 only
constructs the structure.

**Settled: the two route wins and the substitution.** The 2026-09-22 audits
fixed this topic's route:

- **Slot counting (pin 405–703, 299 lines) has a real ≈110–150-line win.** The
  108-line CRT `slotAt_mul` is replaced by the closed form
  `` $`\mathrm{slotAt}(n,d) = (d/\gcd(n/d,d))\cdot\varphi(\gcd(n/d,d))`$ `` and
  mathlib `Nat.Coprime.divisors_mul`; the reusable ingredients
  (`card_filter_coprime_range_mul`, `card_fibre`, `h_mul`) already exist verbatim
  in the pin's `S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean`
  (L18–31, 33–45, 132–155). The four `dedekindPsi_*` re-proofs (64 lines) are
  already public in `Defs/Jq.lean`. See
  [audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md).
- **`rval_aux` is ~64% irreducible mathematics.** Its body is 680 lines
  (`hslot_root` alone is 493), and the realistic cleanup is only ~50 inside plus
  the 18-line `mem_range_of_eval_eq_const`, which is a verbatim copy of T4's
  engine and is **imported, not restated**. Do not hunt for a shorter route. See
  [audit-rval-aux-compressibility.md](../../logs/audit-rval-aux-compressibility.md).
- **The pin's line 1638 is already replaced.** T18 landed `gen_prime`
  (`Defs/Fields.lean`) and promoted `tight_one`/`gen_one`; node 2's local `hallp`
  at `` $`d = p`$ `` uses them instead of
  `functionFieldGeneration_of_squarefree p`. Nothing here waits on T18.

## 2. The scouted inventory

One development in one file, duplicated verbatim as the twin
`S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` (same lines, different
namespace). Port it once. The file is 2,003 lines; lines 35–404 are T14's prelude
(ported, **not** to be re-copied), so the topic-own content is below.

| node | pin span | own |
|---|---|---|
| `minpoly_jqN_map_eq_prod_slots` (= `rval_aux` + wrapper) | 887–1566, 1958–1976 | ≈700 |
| `jqN_prime_not_mem_full` (private M-arb + wrapper) | 1586–1947, 1977–1998 | ≈384 |

### 2.1 Helpers and spans (pin 405–1585)

| helper | pin | span | status |
|---|---|---|---|
| `slotAt`/`slots` | 405–409 | 5 | port (defs) |
| `slotCond_eq`/`slotCond_iff` | 410–417 | 8 | port |
| `gcd_eq_of_modEq`/`slotCond_mod_iff` | 418–427 | 10 | **drop** with the CRT route (used only by `slotAt_mul`) |
| `slotAt_one`/`slotAt_self` | 428–435 | 8 | port (shortened by the closed form) |
| `slotAt_prime_pow_mid` | 436–452 | 17 | port → ≈6 by the closed form |
| `slots_prime_pow` | 453–465 | 13 | port (uses `Nat.sum_divisors_prime_pow`, `Nat.sum_totient`) |
| `dedekindPsi_prime_pow'` | 466–485 | 20 | **drop** — `Defs/Jq.lean` `dedekindPsi_prime_pow` |
| `slotAt_mul` | 486–593 | 108 | **replace** by the closed form + ≈24-line `h_mul` |
| `gcd_mul_left_of_dvd`/`gcd_mul_right_of_dvd` | 594–611 | 18 | **drop** — `Nat.Coprime.divisors_mul` subsumes them |
| `slots_mul` | 612–640 | 29 | port → ≈20–28 |
| `slots_eq_dedekindPsi` | 641–659 | 19 | port (the one public count export) |
| `dedekindPsi_pos`/`_prime`/`_mul_prime_not_dvd`/`_mul_prime_dvd` | 660–703 | 44 | **drop** the re-proofs: `dedekindPsi_pos`/`_prime` are public (`Defs/Jq.lean`), and `_mul_prime_not_dvd`/`_dvd` are **private in `Spine.lean`** — promote those two to `Defs/Jq.lean` beside the other ψ lemmas and have `Spine.lean` import them (delete its private copies) |
| `sv`, `sv_eq`, `sv_eq_TS`, `TS_congr'` | 704–722 | 19 | port (the slot value and its normal forms) |
| `sv_inj` | 723–738 | 16 | port (distinctness of slots) |
| `jqN_congr` | 739–742 | 4 | **drop** — `Defs/Jq.lean` (T14) |
| `sv_top` | 743–747 | 5 | port |
| `aeval_intermediateField_eq_zero` | 748–755 | 8 | T14 — `Defs/PhiAtSlot.lean` |
| `phiAtSeed_eval_of_injective`/`_symm` | 756–775 | 20 | T14 — `Defs/PhiAtSlot.lean` |
| `mem_adjoin_jqN_of_mem_mff` | 776–798 | 23 | port (used by the wrapper, not the private lemma) |
| `qExpand_congr` | 799–803 | 5 | port |
| `mem_range_of_eval_eq_const` | 804–822 | 19 | **import** T4's `Polynomial.mem_range_of_eval_eq_const` (`FieldTheory/CommonRoot.lean:111`) |
| `tight_one`/`gen_one` | 823–857 | 35 | T18 — `Defs/Fields.lean` (public) |
| `map_qExpand_minpoly_eq` | 858–886 | 29 | port → ≈14 (no mathlib lemma; the `map_map`/`map_prod` tail collapses) |
| `rval_aux` | 887–1566 | 680 | port — **the hard half**, ≈50 lines of cleanup only |
| private `jqN_prime_not_mem_adjoin` | 1586–1947 | 362 | port, **using `gen_prime`/`tight_one`/`gen_one`** at the pin's 1634–1639 |
| the two wrappers | 1958–1998 | 41 | port, statements verbatim |

### 2.2 What each node uses

- **Slot product (`rval_aux`)**: T13's `splits_prime_at_slot`, T12's
  `exists_phiIrreducible_evalSymm`, T14's `isRoot_prime_at_slot_iff`,
  `roots_prime_at_slot*`, `phiAtSeed*`, `TS_injective`, `TS_congr`, `qExpand_TS`,
  `qTwist_TS`; the new `sv`/`sv_inj`/`slotAt`/`slots_eq_dedekindPsi`/
  `map_qExpand_minpoly_eq`; mathlib `minpoly.dvd`,
  `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `Monic.natDegree_map`,
  `Polynomial.Splits.eq_prod_roots_of_monic`, `minpoly.monic`,
  `IntermediateField.adjoin.finrank`.
- **Prime non-membership**: node 1, `mem_adjoin_jqN_of_mem_mff`, `Hall M`'s `Gen`
  step, `finrank_adjoin_jqN_eq_of_prime` (T16, ported), T4's
  `mem_range_of_eval_eq_const`, T14's `aeval_intermediateField_eq_zero` and
  `phiAtSeed_eval_symm`, and the local `hallp` built with `gen_prime`,
  `tight_one`, `gen_one`.

## 3. The mathlib-first audit

Audited against the pinned `v4.34.0`. The topic is transcription plus three
specific route wins; there is **no new engine**.

| pin piece | mathlib / port | verdict |
|---|---|---|
| `slotAt`'s CRT (`slotAt_mul`, 108) | closed form + `card_fibre`/`card_filter_coprime_range_mul`/`h_mul` (pin card file) + `Nat.Coprime.divisors_mul` (`Data/Finset/NatDivisors.lean:65`) | **replace**, ≈80–105 |
| `slotAt_prime_pow_mid`'s count | `Nat.totient_eq_card_coprime` (`NumberTheory/EulerTotient`), `Nat.filter_coprime_Ico_eq_totient`, `Nat.periodic_coprime` | call (already in the pin) |
| `slots_prime_pow` | `Nat.sum_divisors_prime_pow`, `Nat.sum_totient` | call |
| the `dedekindPsi_*` re-proofs (64) | `Defs/Jq.lean` (public ψ lemmas) | **drop**; promote `dedekindPsi_mul_prime_not_dvd`/`_dvd` out of `Spine.lean` |
| `mem_range_of_eval_eq_const` | `FieldTheory/CommonRoot.lean:111` (T4) | **import** |
| `map_qExpand_minpoly_eq` | none — `minpoly.map`/`minpoly.map_eq_of_injective` do not exist; only `Polynomial.map_map`, `map_prod`, `map_sub` apply | port, ≈14 |
| `rval_aux`'s monic/dvd/degree assembly | `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `minpoly.dvd`, `Splits.eq_prod_roots_of_monic` | call |
| the M-arbitrary non-membership | `gen_prime` + `tight_one`/`gen_one` (T18) replace `functionFieldGeneration_of_squarefree`; `finrank_adjoin_jqN_eq_of_prime` (T16) | call |

**Headline.** One real win (the slot count), one import (`mem_range_of_eval_eq_const`),
one substitution (`gen_prime`); the rest is faithful transcription. `rval_aux` has
no shorter route — the audit's verdict is that the 493-line `hslot_root` is
irreducible, so budget for it rather than golf it.

## 4. Module

One module, one development:

| module | gains | imports |
|---|---|---|
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean` **(new)** | `slotAt`/`slots` + the count (`card_*`/`slots_eq_dedekindPsi`), `sv`/`sv_inj`/`sv_top`, `map_qExpand_minpoly_eq`, `rval_aux`, public `minpoly_jqN_map_eq_prod_slots`, `mem_adjoin_jqN_of_mem_mff`, the private M-arbitrary `jqN_prime_not_mem_adjoin`, public `jqN_prime_not_mem_full` | `Defs/PhiAtSlot`, `Defs/TS`, `Defs/Laurent`, `Defs/Cyclotomic`, `Defs/Fields`, `Defs/Jq`, `ModularCurve/PhiSlotRoots`, `ModularCurve/PhiGenSplits`, `ModularCurve/ModularPolynomialProperties`, `ModularCurve/ModularPolynomialUniqueness`, `FunctionFieldGeneration/Collapse`, `FunctionFieldGeneration/DegreeStep`, `FunctionFieldGeneration/Nonmembership`, `FieldTheory/CommonRoot` |

Declare in dependency order: the slot count, then `sv` and `map_qExpand_minpoly_eq`,
then `rval_aux` and its public wrapper, then `mem_adjoin_jqN_of_mem_mff`, the
private M-arbitrary lemma and its wrapper. If the module proves unmanageable, the
seam is the slot product (`rval_aux` + wrapper) against the non-membership
(`mem_adjoin_jqN_of_mem_mff` + M-arbitrary + wrapper); split there and say so —
but do not pre-split.

**Statements.** The two public theorems are transcribed **verbatim from their
`Theorems/` wrappers**, which write FLT's `hall` hypothesis out as the explicit
conjunction. Do **not** state them with the port's `Hall M` abbreviation: the
checker would then diff `Hall M` against the pin's conjunction and report a
mismatch. The `Inputs` fields in `Spine.lean` already use `Hall M`; that is the
defeq abbreviation and stays as it is. T20 passes these verbatim theorems into
those fields.

## 5. Prerequisites — public, verified

`isRoot_prime_at_slot_iff`, `roots_prime_at_slot(_nodup)(_roots_nodup)`,
`prod_form_ne_zero` (`PhiSlotRoots`); `PhiGen.splits_prime_at_slot`
(`PhiGenSplits`); `exists_phiIrreducible_evalSymm`
(`ModularPolynomialProperties`); `phiAtSeed*`, `aeval_intermediateField_eq_zero`
(`Defs/PhiAtSlot`); `TS_injective`/`TS_congr`/`qExpand_TS`/`qTwist_TS`
(`Defs/TS`); `coeffEmb_qExpand`, `qExpand_*` (`Defs/Laurent`); `cycUnit`/
`cycUnit_spec` (`Defs/Cyclotomic`); `modularFunctionFieldFull`, `jqd_mem_full`,
`Tight`/`Gen`/`Hall`, `tight_one`/`gen_one`/`gen_prime` (`Defs/Fields`);
`dedekindPsi_prime`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime`,
`jqN_congr` (`Defs/Jq`); `finrank_adjoin_jqN_eq_of_prime`
(`ModularPolynomialUniqueness`); `finrank_adjoin_jqN_prime_of_not_mem`
(`DegreeStep`, T16); `Polynomial.mem_range_of_eval_eq_const` (`CommonRoot`); the
`jqN`/`jq`/`qExpand`/`qTwist`/`coeffEmb` vocabulary (`Defs/Jq`, `Defs/Laurent`,
`Defs/Twist`). Nothing needed is `private` except the pin's own M-arbitrary
helper, which this topic declares.

## 6. Verification

1. **`#print axioms`** clean on both public nodes (and on the slot count).
2. **Statement checker.** Append
   `Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` and
   `Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean` to `SOURCES`. Both are
   public wrappers, so they verify by direct name match; if the private
   M-arbitrary lemma is also to be verified, use the `S_`-carrier route T14
   established. Report before/after; T18 left it at **293**.
3. **`PORT_FILES`** gains `FunctionFieldGeneration/SlotProduct.lean`.
4. **The wire test — Zone Q.** T18 took Zone P. Build a **fully discharged**
   `Inputs` with all seven fields, so the debt visibly reaches **0**; that
   structure is T20's capstone input. Also record a concrete slot evaluation
   (`M = 2`, `K = ℂ`, `ζ = -1`) if it is in reach.
5. **Build.** `lake build` green, 0 warnings, no `sorry`; library-wide `grep`.
6. **README** gains the module; **`PORTING-FFG.md` §7.8** marks T19 done and
   records the measured cost; `logs/ffg-port.md` gains T19's entry, including the
   route wins actually taken.

## 7. Budget and route risks

Topic-own pin content is ≈1,387 lines before the route wins: `rval_aux` 680, the
private M-arbitrary lemma 362, the wrappers 41, the slot count 207 (299 minus the
92 lines of dead `dedekindPsi_*`/`gcd_*` helpers), and ≈97 of `sv`/
`mem_adjoin_jqN_of_mem_mff`/`map_qExpand_minpoly_eq` helpers (the T14 helpers,
`mem_range_of_eval_eq_const`, `tight_one` and `gen_one` are already excluded —
they are imported, not ported). The wins remove ≈90–110 (the closed-form slot
count), ≈15 (`map_qExpand_minpoly_eq`) and ≈50 (`rval_aux` cleanup), for
**≈1,210–1,235 port lines** and **two to three goal rounds**. The plan's
`~1,100–1,400` bracket holds; this is the largest single topic of the remainder,
and `rval_aux` alone is more than half of it.

**Route risks, in the order they will bite.**

- **`rval_aux`'s `hslot_root` (pin 905–1397, 493 lines).** Every admissible
  `sv K ζ a b` is a root of the mapped minimal polynomial, by case-splitting on
  `` $`p \mid a`$ `` and matching exponent data through `TS_injective` and the
  prime slot description. The audit's block map is the reading order; the two
  branches share a byte-identical 12-line tail (hoist it, ~11 lines). Transcribe,
  do not golf — the audit puts the irreducible core at ~64%.
- **The slot count's closed form.** Route-check
  `` $`\mathrm{slotAt}(n,d) = (d/\gcd(n/d,d))\cdot\varphi(\gcd(n/d,d))`$ ``
  against `card_fibre`/`h_mul` in a scratch file before deleting `slotAt_mul`;
  the identity was verified numerically but the port's `slotAt` has the
  `gcd (gcd a b) d = 1` shape, so the first step is the `slotCond_iff` rewrite to
  `Coprime (gcd a d) b`. If the closed form resists, fall back to transcribing
  `slotAt_mul` and record why.
- **The M-arbitrary non-membership (pin 1586–1947, 362 lines).** Its `hallp`
  (pin 1624–1639) is where T18's substitution lands: the `` $`d = 1`$ `` branch is
  `⟨tight_one, gen_one⟩`, and the `` $`d = p`$ `` branch is the direct `Tight p`
  proof plus `gen_prime p`. Do **not** reintroduce
  `functionFieldGeneration_of_squarefree`. The rest is the constant-on-slots
  argument, sharing T4's engine with T17's `step_contradiction` but with the
  ψ(M)-slot root list instead of `` $`\Phi_p`$ ``'s `` $`p+1`$ `` roots.
- **`map_qExpand_minpoly_eq` (29 lines).** No mathlib replacement exists
  (`minpoly.map`/`minpoly.map_eq_of_injective` do not); only the
  `Polynomial.map_map`/`map_prod` tail collapses, to ≈14. Keep it a named
  monomorphic helper.
- **Statement shape.** The two public theorems take the explicit `hall`
  conjunction, not `Hall M` (§4); the pin's wrappers write it out. Getting this
  wrong is the one thing that would make the checker report a mismatch.
- **The `Algebra ℚ⟮jq⟯ (LaurentSeries K)` instance.** Both the slot product's
  coefficient extension and the non-membership install it; T15–T18 already
  established the shape, so copy it and do not re-derive.

## 8. Definition of done (T19)

- [ ] `FunctionFieldGeneration/SlotProduct.lean` created, both public statements
      verbatim from their wrappers (explicit `hall`, not `Hall M`);
- [ ] the slot count uses the closed form and one public `Finset.card` export;
      `slotAt_mul`, `gcd_mul_left/right_of_dvd`, `gcd_eq_of_modEq`,
      `slotCond_mod_iff` and the four `dedekindPsi_*` re-proofs are dropped with
      recorded counts;
- [ ] `mem_range_of_eval_eq_const` is imported from `FieldTheory/CommonRoot`, not
      restated; the two `dedekindPsi_mul_prime_*` helpers are promoted to
      `Defs/Jq.lean` and `Spine.lean`'s private copies are deleted;
- [ ] the M-arbitrary `hallp` uses `gen_prime`/`tight_one`/`gen_one`; the pin's
      `functionFieldGeneration_of_squarefree` is not referenced;
- [ ] `lake build` green, 0 warnings, no `sorry`;
- [ ] `#print axioms` clean on both public nodes;
- [ ] both wrappers in `SOURCES`, 0 mismatched, 0 missing; `PORT_FILES` updated;
- [ ] Zone Q recorded and green, with a **fully discharged** `Inputs` (debt 2 → 0)
      as its wire test;
- [ ] README, `PORTING-FFG.md` §7.8 and `logs/ffg-port.md` updated;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The debt** — confirm both fields are discharged, `Inputs` is total, and the
   structure was not touched.
2. **The routes** — did the closed-form slot count hold, or was `slotAt_mul`
   transcribed? Was `rval_aux` the stall point? Did `map_qExpand_minpoly_eq`
   shrink to ≈14?
3. **The substitution** — confirm the M-arbitrary `hallp` uses
   `gen_prime`/`tight_one`/`gen_one` and that no squarefree-block declaration was
   pulled in.
4. **The dedup** — the slot-count drops and the `dedekindPsi_*`/engine imports
   have recorded `grep -c` counts.
5. **The cost** — rounds, declarations, lines, ratio against the ≈1,387 pre-win
   figure (target ≈1,210–1,235), and the corrected T19 figure for §7.8.

## 10. Where this sits

T19 is the last topic before the capstone. With its two fields discharged, the
`Inputs` structure is total and T20 needs only to construct it, apply the proved
`functionFieldGeneration_of`, and replace the consumer's deferred `sorry` — the
one remaining `sorry` in the library. The dependency order, the T19 route wins and
the deferred T18 tail are [PORTING-FFG.md](../../PORTING-FFG.md) §7.8.
