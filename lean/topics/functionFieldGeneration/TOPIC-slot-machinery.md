# Topic 14: the slot machinery (the shared prelude)

**Status: done (2026-09-22) — one goal round.** The prelude is written once:
`Defs/PhiAtSlot.lean` (237 lines) and `ModularCurve/PhiSlotRoots.lean` (153) are new,
`Defs/TS.lean` +51, `Defs/Twist.lean` +56, `Defs/Jq.lean` +6; the six `private`
twins in `Spine.lean`/`PhiGenSplits.lean` are deleted. **503 port lines** against
the pin's ~306 (ratio ≈1.64), not the row's `~250`. The checker moved 244 → 276
(12 promoted), 0 mismatched/0 missing; `#print axioms` is clean on all 32 public
declarations; the consumer's Zone L is green, with chosen wire
`roots_phiProd_conj_nodup` at `p = 2`, `K = ℂ`, `ζ = -1`. Two findings correct
this work order: most of the prelude is already **public** in
`S_ModularCurve_functionFieldGeneration.lean` (so only `prod_form_ne_zero` needed
the dotted route), and `Defs/TS.lean`'s import of `Defs/Twist.lean` forces the
four `TS`-dependent declarations into `Defs/TS.lean` rather than §4's Twist/Jq
homes. See [logs/ffg-port.md](../../logs/ffg-port.md) §2g for the measured cost
and the route results. T13 is done and committed (`a20e711`, `5fd38be`).

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
> - **Never raise `maxHeartbeats`.** The cap already fails in under 20 s; raising
>   it turns that into an unbounded wait. The usual cause is a
>   `FunLike`-quantified lemma instantiated at a bare function type
>   (`DFunLike.coe` unfolds without bound) — restate it over the concrete function
>   instead. T5's log §2.2 has the worked example.

**Audience.** A fresh session taking T14 of the `functionFieldGeneration` effort.
Read, in this order:

1. [PORTING-FFG.md](../PORTING-FFG.md) §7.8 (the plan and why T14 is first) and
   §2.1 (the interface ledger);
2. [PORTING-PhiGen.md](../PORTING-PhiGen.md) §5–§6 and T13's module header
   (`PhiGenSplits.lean`), which records what the cone's route does *not* need;
3. [math/010](../../../math/010-function-field-generation.md) §3–§6 — the slot
   description, descent, generation and the degree steps;
4. [TOPIC-splitting.md](../phiGenSplitting/TOPIC-splitting.md) (T13, the immediate
   predecessor) and [logs/phiGen-port.md](../../logs/phiGen-port.md) §13;
5. [porting-playbook.md](../../porting-playbook.md) §2 (deduplicate at the source),
   §3.9, §3.11.

## 1. Goal, and why this topic

**Goal.** Write the pin's shared slot prelude **once**, in shared modules, so that
T15–T19 import it instead of each re-copying the pin's ~370-line prelude (of
which ~306 lines are new work here). Concretely:

1. **promote** the bridges the cone already has but keeps `private`
   (`iota_jqN`, `jqN_congr`, `iota_jq`, `conj_zero_eq`, `conj_succ_eq`,
   `qExpand_qTwist_TS`) to their shared homes;
2. **port** the unported rest — the twist equivalence, the `phiProd` roots, the
   `phiAtSeed` block and the at-slot roots API — statements verbatim from the pin;
3. deliver it as the parent remainder's import, with `#print axioms` clean and the
   statements covered by `spec/check_flt_statements.py`.

**Why now, and why it was not T13's.** T13's route proves
`splits_of_prime`/`splits_prime_at_slot` without this prelude and correctly left it
unported: the pin's ~200 lines of it exist for the char-`p`
`*_of_isPrimitiveRoot` variants, which are **outside the 44-node cone**. But the
parent remainder's own files use it heavily — measured across the 17 remaining pin
files, `phiAtSeed` appears in 13 of them at 26–74 uses each, `roots_prime_at_slot`
in 11, `qTwistEquiv` and `phiProd_conj_eq`/`prod_form_ne_zero` in 12 — so
T15–T19 would each re-copy it. That is the same "six developments ship the same
file" situation T10 removed for `TPoleOrderLE`, and it is the largest dedup left.

**Settled: statements are the pin's, verbatim.** Every T14 declaration is
`private` in the pin (none has a `Theorems/` wrapper), so the checker's public
`SOURCES` lookup cannot match them by name; §6 gives the `S_`-carrier route that
verifies them instead of exempting them.

**Settled: two homes, because the roots API is downstream of the cone.**
`roots_prime_at_slot`/`_nodup`/`_roots_nodup`/`isRoot_prime_at_slot_iff` consume
`PhiGen.splits_prime_at_slot` (T13), so they cannot live in `Defs/` — that
directory is upstream of the cone and stays so. Everything else is upstream and
belongs in `Defs/`. §4 is the split.

## 2. The scouted inventory

Source pin: `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` (2,002 lines; the
prelude is lines 35–404) unless marked †, which are in
`P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`.

### 2.1 Already public — no work

`Defs/TS.lean`: `TS` and its nine lemmas (`TS_coeff_mul`, `TS_coeff_of_not_dvd`,
`TS_coeff_neg`, `TS_coeff_of_lt`, `TS_ne_zero`, `TS_injective`, `qTwist_TS`,
`qExpand_TS`, `TS_congr`). `Defs/Laurent.lean`: `coeffEmb_qExpand`. T13 already
promoted the cyclotomic block (`exists_isPrimitiveRoot_cyclotomicField`,
`cycUnit`, `cycUnit_spec`, `cycUnit_pow`, `isPrimitiveRoot_pow_div`) into
`Defs/Cyclotomic.lean` — **import it, do not re-port it.**

### 2.2 Promotions — already ported, currently `private`

| declaration | pin span | current port | shared home |
|---|---|---|---|
| `iota_jqN` | 102–105 (4) | `FunctionFieldGeneration/Spine.lean:72` | `Defs/Jq.lean` |
| `jqN_congr` | 739–742 (4) | `FunctionFieldGeneration/Spine.lean:87` | `Defs/Jq.lean` |
| `iota_jq` | 106–108 (3) | `PhiGenSplits.lean:71` | `Defs/PhiAtSlot.lean` |
| `conj_zero_eq` | 109–111 (3) | `PhiGenSplits.lean:76` | `Defs/PhiAtSlot.lean` |
| `conj_succ_eq` | 112–114 (3) | `PhiGenSplits.lean:81` | `Defs/PhiAtSlot.lean` |
| `qExpand_qTwist_TS` | 237–251 (15) | `PhiGenSplits.lean:186` | `Defs/Twist.lean` |

The four in `PhiGenSplits.lean` are T13's file. Move the canonical copies to their
shared home and have `PhiGenSplits.lean` import them, deleting its private copies —
one declaration, one home. `Spine.lean` likewise imports `iota_jqN`/`jqN_congr`.

### 2.3 Fresh ports — upstream of the cone

| declaration | pin span | content | mathlib inside |
|---|---|---|---|
| `qTwist_iota_of_pow_eq_one` | 115–129 (15) | a twist by a root of unity fixes `qExpand K N x` | `qTwist_qExpand`, `qTwist_one_apply` |
| `qTwistEquiv` | 130–140 (11) | `qTwist u` packaged as `LaurentSeries K ≃+* LaurentSeries K` | `qTwist_qTwist`, `map_mul`/`map_add` |
| `qTwistEquiv_apply` | 142–143 (2) | `@[scoped simp]` unfolding | — |
| `coe_qTwistEquiv` | 145–147 (3) | its coercion is `qTwist u` | `RingHom.ext` |
| `qTwist_TS_one_cycle` | 149–156 (8) | twisting cycles the `p` finite roots | `qTwist_TS`, `Nat.mod_add_div` |
| `phiProd_conj_eq` | 157–165 (9) | the product expands as `(X − extra)·∏_b (X − ζ^b j)` | mathlib `Polynomial` API |
| `roots_phiProd_conj` | 166–180 (15) | its roots are those `p+1` values | `roots_mul`, `roots_X_sub_C`, `roots_multiset_prod_X_sub_C` |
| `roots_phiProd_conj_nodup` | 181–194 (14) | distinctness from `IsPrimitiveRoot` | `Multiset.nodup_cons`, `IsPrimitiveRoot.pow_inj`, `TS_injective` |
| `phiAtSeed` | 351–354 (4) | evaluate `Φ` at `X = x` as a polynomial in `Y` | `Polynomial.eval₂RingHom` |
| `phiAtSeed_map` | 355–363 (9) | naturality in the coefficient ring | `Polynomial.map_map`, `ringHom_ext'` |
| `phiAtSeed_monic` | 364–367 (4) | monic | `Monic.map` |
| `phiAtSeed_natDegree` | 368–371 (4) | `natDegree = dedekindPsi n` | `Monic.natDegree_map`, `data.natDegree_eq` |
| `phiAtSeed_jq_eval` | 372–380 (9) | vanishes at `(jq, jqN n)` | `data.eval_eq_zero`, `Polynomial.eval_map` |
| `phiAtSeed_eval_map` | 381–385 (5) | vanishes after any ring map | `eval_map`, `eval₂_hom` |
| `phiAtSeed_jqN_eval` | 386–390 (5) | vanishes at `(jqN M, jqN (M*n))` | `qExpand_qExpand` |
| `phiAtSeed_iota_eval` | 391–404 (14) | the coefficient-extended form | composition of the above |
| `aeval_intermediateField_eq_zero` | 748–755 (8) | `aeval` at a subfield element | `IntermediateField.aeval_coe` |
| `phiAtSeed_eval_of_injective` | 756–762 (7) | invariance under injective maps | `injective_iff_map_eq_zero` |
| `phiAtSeed_eval_symm` | 763–775 (13) | `EvalSymm` gives the swapped evaluation | `Polynomial.aeval`, `ringHom_ext'` |
| `phiAtSeed_jqN_eval_down` † | 426–430 (5) | the symmetric direction at `jqN` | `phiAtSeed_eval_symm` |
| `qExpand_qTwist_notMem_range_qExpand` † | 431–442 (11) | a twisted `j` is outside a non-matching `qExpand` range | `qExpand_coeff_of_not_dvd`, `TS_coeff_neg` |

### 2.4 Fresh ports — downstream of T13

`prod_form_ne_zero` (252–259, 8) is pure polynomial algebra and could sit upstream,
but it is used only here; put it with its consumers for cohesion.

| declaration | pin span | content |
|---|---|---|
| `prod_form_ne_zero` | 252–259 (8) | the expanded product is nonzero (`X_sub_C_ne_zero`, `monic_prod_of_monic`) |
| `roots_prime_at_slot` | 260–280 (21) | the roots of `data.Φ` read at the slot, via T13's `splits_prime_at_slot` |
| `roots_prime_at_slot_nodup` | 281–312 (32) | those `p+1` roots are distinct |
| `roots_prime_at_slot_roots_nodup` | 313–320 (8) | the packaged `Nodup` form |
| `isRoot_prime_at_slot_iff` | 321–350 (30) | membership in the root multiset, iff form |

## 3. The mathlib-first audit

Audited against `v4.34.0`. This is a **glue topic in the T7/T9/T10 sense**: mathlib
supplies the polynomial, multiset and `IntermediateField` primitives; FLT supplies
the statements and the `TS`/`qTwist` vocabulary.

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| `qTwistEquiv` | `RingEquiv.ofBijective` (`Algebra/Ring/Equiv.lean:446`) + `qTwist_qTwist`/`qTwist_one_apply`; FLT writes the 11-line `where` directly | **route-check both; the pin's `where` is already short.** Prefer whichever reads better; record the choice |
| `phiAtSeed` | `Polynomial.eval₂RingHom` (`Algebra/Polynomial/Eval/Defs.lean:213`) | keep FLT's one-line `def` over mathlib (name is the note's) |
| `phiAtSeed_*`, `aeval_intermediateField_eq_zero` | `Polynomial.map_map`, `ringHom_ext'`, `Monic.map`, `natDegree_map`, `eval_map`, `eval₂_hom`, `injective_iff_map_eq_zero`, `IntermediateField.aeval_coe` (`FieldTheory/IntermediateField/Basic.lean:595`) | port; `aeval_intermediateField_eq_zero` may collapse to a short call — route-check |
| `roots_phiProd_conj` | `Polynomial.roots_mul`, `roots_X_sub_C`, `roots_multiset_prod_X_sub_C` (`Algebra/Polynomial/Roots.lean:318`) | port (mathlib inside) |
| `roots_phiProd_conj_nodup` | `Multiset.nodup_cons`, `IsPrimitiveRoot.pow_inj` | port |
| `prod_form_ne_zero` | `Polynomial.X_sub_C_ne_zero`, `Polynomial.monic_prod_of_monic` | port (short) |
| `roots_prime_at_slot*`, `isRoot_prime_at_slot_iff` | none; consume T13's `splits_prime_at_slot` + mathlib roots | port |
| `qExpand_qTwist_TS`, `qExpand_qTwist_notMem_range_qExpand`, `qTwist_iota_of_pow_eq_one`, `qTwist_TS_one_cycle` | none (the port's `qExpand`/`qTwist`/`TS` API) | port (short) |

**Headline.** No public mathlib lemma replaces a statement. The audit's value is
again negative: do not hunt analogues. `RingEquiv.ofBijective` and
`IntermediateField.aeval_coe` are the two positive ingredients.

## 4. Module split, and the layering constraint

| module | gains | imports |
|---|---|---|
| `FLTForHuman/ModularCurve/Defs/Twist.lean` | `qTwist_iota_of_pow_eq_one`, `qTwistEquiv`, `qTwistEquiv_apply`, `coe_qTwistEquiv`, `qTwist_TS_one_cycle`, `qExpand_qTwist_TS`, `qExpand_qTwist_notMem_range_qExpand` | `Defs/TS.lean`, `Defs/Laurent.lean` |
| `FLTForHuman/ModularCurve/Defs/Jq.lean` | `iota_jqN`, `jqN_congr` | current |
| `FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean` **(new)** | `iota_jq`, `conj_zero_eq`, `conj_succ_eq`, `phiProd_conj_eq`, `roots_phiProd_conj`, `roots_phiProd_conj_nodup`, `phiAtSeed` + its eight lemmas, `aeval_intermediateField_eq_zero`, `phiAtSeed_eval_of_injective`, `phiAtSeed_eval_symm`, `phiAtSeed_jqN_eval_down` | `Defs/TS`, `Defs/Jq`, `Defs/PhiGen`, `Defs/Polynomial` |
| `FLTForHuman/ModularCurve/PhiSlotRoots.lean` **(new)** | `prod_form_ne_zero`, `roots_prime_at_slot`, `roots_prime_at_slot_nodup`, `roots_prime_at_slot_roots_nodup`, `isRoot_prime_at_slot_iff` | `Defs/PhiAtSlot.lean`, `PhiGenSplits.lean` (T13) |

`Defs/PhiAtSlot.lean` is the modular polynomial at the slot (the shared prelude);
`PhiSlotRoots.lean` is the one T14 module
downstream of the cone, so T15–T19 import both and nothing in `Defs/` ever depends
on a cone module. A single `ModularCurve/PhiAtSlot.lean` importing T13 is acceptable if
the split proves awkward, but say so in the log — the layering is the readable
choice. Names are suggestions; what matters is one home per declaration.

> **Executed names (post-T14 rename).** This work order proposed `Defs/Slot.lean`
> and `ModularCurve/SlotRoots.lean`; the executed modules were renamed to
> `Defs/PhiAtSlot.lean` and `ModularCurve/PhiSlotRoots.lean` because "Slot" named
> FLT's positional jargon rather than an object and collided with `Defs/PhiGen.lean`'s
> "slot vocabulary" gloss. Every path above is the executed spelling; no declaration
> name changed.

## 5. Consumers, and the dedup

The prelude is carried by **11–13** of the seventeen remaining pin files, depending
on the symbol. Exact carrier counts (measured over all seventeen, recorded here so
the exec need not re-derive them):

| symbol | carriers (of 17) | uses per carrier |
|---|---|---|
| `phiAtSeed` | 13 | 26–74 |
| `TS K` (the block) | 12 | 35–56 |
| `qTwistEquiv` | 12 | 5–8 |
| `phiProd_conj_eq` | 12 | 2 |
| `roots_prime_at_slot` | 11 | 6–8 |
| `prod_form_ne_zero` | 11 | 3 |
| `isRoot_prime_at_slot_iff` | 11 | 1–4 |
| `jqN_congr` | 10 | 1–14 |
| `phiAtSeed_eval_symm` | 7 | 2 |
| `qExpand_qTwist_notMem_range_qExpand` | 2 | 2 |

Writing it once is the largest single removal left in the parent effort. The
`TS` block and cyclotomic roots are already written once (`Defs/TS.lean`,
`Defs/Cyclotomic.lean`) — this topic finishes the job.

## 6. Verification

1. **`#print axioms`** clean on every public declaration (only `propext`,
   `Classical.choice`, `Quot.sound`).
2. **Statement checker.** None of T14's declarations has a `Theorems/` wrapper, and
   all are `private` in the pin. The T10 mechanism handles this: add the pin's
   carrier `S_` files to `SOURCES`, whose `private` declarations enter
   `dotted_source` and are matched against the port's dotted names —
   `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` carries §2.2–§2.4 except
   the two † entries, and `P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`
   carries those. **Report the before/after counts and the promoted total.** Order
   matters (`source.setdefault` keeps the first public hit): put the `Them_` and
   `Defs` sources ahead of these `S_` files, exactly as T13's entries do, and
   re-run the checker to confirm no existing match flips.
3. **`PORT_FILES`** gains `Defs/PhiAtSlot.lean` and `PhiSlotRoots.lean` (and none removed).
4. **The wire test — Zone L.** T11–T13 took Zones I–K; this takes the next free
   zone in `spec/ModularCurveConsumer.lean`. It should be a *cross-module
   composition*, not a binding:
   - `qTwistEquiv` round-trip: `qTwistEquiv u (qTwist u⁻¹ f) = f` for a concrete
     `f` (uses `Defs/Twist.lean` and the promoted bridges);
   - `phiAtSeed_monic`/`_natDegree` at `data = modularPolynomialDataOne`
     (uses `Defs/Polynomial.lean` and `Defs/PhiAtSlot.lean`);
   - `roots_phiProd_conj` at `p = 2`, `K = ℂ`, `ζ = -1` via
     `IsPrimitiveRoot.neg_one` (uses `Defs/PhiGen.lean`, `Defs/PhiAtSlot.lean`).
   Record which one is chosen and why.
5. **`#print axioms`/build.** `lake build` green, 0 warnings, no `sorry`; run the
   library-wide `grep -rn 'sorry' FLTForHuman/ModularCurve/` check.
6. **README** gains the two new modules in the module table.
7. **`PORTING-FFG.md` §7.8** marks T14 done, records the measured cost, and
   corrects the row's `~250` estimate if the port lands outside it; the log
   [logs/ffg-port.md](../../logs/ffg-port.md) gains T14's entry.

## 7. Budget and route risks

Pin content is **~306 lines**: **32 promoted**, **175 fresh upstream**, **99
downstream**. At the sub-effort's measured ratios (T7 1.05, T8 0.98, T9 0.93,
T10 1.27) expect **~320–420 port lines** plus headers/docstrings — larger than
§7.8's `~250` row, which was a pre-scouting estimate. Budget **two goal rounds**;
the work is mechanical transcription, but the route checks in §7 come first.

**Route risks, in the order they will bite.**

- **`phiAtSeed_eval_symm`'s coercion `hhom`.** The pin identifies
  `Polynomial.eval₂RingHom (Int.castRingHom _) z` with `(Polynomial.aeval z).toRingHom`
  through `ringHom_ext'` + `simp [Polynomial.coe_eval₂RingHom]`. That is exactly the
  `FunLike`/transparency family that bit T5 and T8. If it does not close quickly,
  state the identity as a named `private` monomorphic bridge (rule §1.3) rather
  than fighting `simp`.
- **`qTwistEquiv`'s route.** Try `RingEquiv.ofBijective (qTwist u) hf` first (mathlib
  positive ingredient); if the inverse/`Commute` obligations are fiddly, the pin's
  11-line `where` is the fallback and is already short. Either way record which.
- **`aeval_intermediateField_eq_zero`.** `IntermediateField.aeval_coe` may collapse
  the 8-line injection argument to a call; check the statement direction
  (`aeval (E.val x) P = E.val (aeval x P)`) before adopting it, per §4.2's
  "route-check first" rule.
- **The T13 entanglement.** `iota_jq`/`conj_zero_eq`/`conj_succ_eq`/
  `qExpand_qTwist_TS` are private in `PhiGenSplits.lean` (T13 kept them private, as
  its header records). Move the canonical copies to `Defs/` and delete T13's, or
  expose them in place; do not leave both. Likewise `Spine.lean`'s
  `iota_jqN`/`jqN_congr`.
- **The roots API depends on T13.** If T13's `splits_prime_at_slot` statement shape
  drifted from the pin (check the checker's T13 entries), `roots_prime_at_slot`'s
  `rw` will not fire; that is the one cross-topic shape risk.
- **`@[scoped simp] qTwistEquiv_apply`.** Keep the scoped attribute as the pin has
  it; do not promote it to a global simp lemma.

## 8. Definition of done (T14)

- [ ] the six promotions are public in their shared homes, and `Spine.lean` /
      `PhiGenSplits.lean` no longer carry private copies;
- [ ] `Defs/Twist.lean`, `Defs/Jq.lean` extended, `Defs/PhiAtSlot.lean` and
      `ModularCurve/PhiSlotRoots.lean` created, all green, 0 warnings, no `sorry`;
- [ ] every T14 statement is the pin's, and the checker reports them as verified
      (via the `S_`-carrier/dotted route) rather than exempted;
- [ ] `#print axioms` clean on every public T14 declaration;
- [ ] Zone L recorded and green in the consumer;
- [ ] README module table, `PORTING-FFG.md` §7.8 and `logs/ffg-port.md` updated;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The dedup** — confirm the one-home rule held (six promotions, no copy left in
   `Spine.lean`/`PhiGenSplits.lean`), and the checker's before/after
   verified/promoted counts.
2. **The routes** — did `RingEquiv.ofBijective` and `IntermediateField.aeval_coe`
   close? Did `phiAtSeed_eval_symm` need the named bridge? Which wire test was used?
3. **The cost** — rounds, declarations, lines, port/pin ratio against ~306.
4. **The layering** — did `Defs/PhiAtSlot.lean` + `PhiSlotRoots.lean` hold, or was a single
   downstream module used, and why?
5. **The estimate** — the corrected T14 line count for `PORTING-FFG.md` §7.8.

## 10. Where this sits

T14 is the first parent topic after the Φ_p cone, and the last one that is pure
plumbing: it hands T15–T19 the vocabulary the pin repeats in up to thirteen files. T15
(descent and the collapse), T16 (the degree step), T17 (non-membership), T18
(generation) and T19 (the slot product) follow, each importing this topic and none
copying it. The frontier and their dependency order are
[PORTING-FFG.md](../PORTING-FFG.md) §7.8.
