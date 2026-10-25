# Topic: the `C`-layer tail of `functionFieldGeneration` — the slot product and the prime-power step over an arbitrary field

Status: **landed 2026-10-25** (ground, CL1 and CL2 all green; record:
[logs/c-layer-slot-product-and-primestep.md](../../logs/c-layer-slot-product-and-primestep.md)). This file is the measurement and the work-order cut
for three D-S target nodes:

| target | pin `S_` | raw lines | citers |
|---|---|---:|---:|
| `ModularCurve.minpoly_jqNModC_map_eq_prod_slots` | `S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean` | 1,914 | 6 |
| `ModularCurve.jqNModC_prime_not_mem_fullC` | `S_ModularCurve_jqNModC_prime_not_mem_fullC.lean` | 1,909 | 1 |
| `ModularCurve.relfinrank_fullC_mul_prime_pow` | `S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean` | 1,175 | 1 |

They are **the three largest ready `ModularCurve` nodes of the D-S demand** (measured, §2: the
next is 868 raw lines), and they are the `C`-layer (arbitrary field `K`) counterparts of the `ℚ`
layer the port has already banked. The set is cut into **two modules and two work orders** (§6):
CL1 carries the two twin headlines, CL2 the prime-power step. Nothing here has been written yet.

Parent topic (the whole `C` layer, 22 remaining nodes):
[functionFieldGeneration/TOPIC-qexp-function-field-c.md](../functionFieldGeneration/TOPIC-qexp-function-field-c.md).
Orders: [WORKORDER-CL1-slot-product-any-field.md](WORKORDER-CL1-slot-product-any-field.md),
[WORKORDER-CL2-fullc-prime-power-step.md](WORKORDER-CL2-fullc-prime-power-step.md).

**Audience.** A session taking the `C`-layer tail. Read
[porting-playbook.md](../../porting-playbook.md) §0.2 (staffing), §2.1 (measure the cone), §2.3
(whole nodes), §2.4 (dedup before coding), §3.3–§3.5 (order, sets, build ladder), §4
(faithfulness); [notes/lean-build-cost.md](../../../notes/lean-build-cost.md) for the build
budget.

## 1. What the mathematics is

All three are **conditional** theorems: they take the degree data as a hypothesis and never need
a capstone.

1. **`minpoly_jqNModC_map_eq_prod_slots`** — the minimal polynomial of `jqNModC K M` over
   `K⟮jqModC K⟯`, pushed into `LaurentSeries K` by `qExpand K M`, is the explicit slot product

   ```lean
   ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
     (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
       letI : NeZero a := ⟨h⟩
       qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))))
   ```

   proved by strong induction on `M` from the char-`p` splitting of `Φ_p` at a slot
   (`PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, ported). Its body in the pin is the
   monolithic `rval_aux` (`S_:832`).
2. **`jqNModC_prime_not_mem_fullC`** — `jqNModC K p ∉ fullC K M` for `p ∤ M`, from the same
   `hall` plus `hbase`. The proof reads the `ψ(M)` slot roots off item 1, writes
   `jqNModC K p = g(jqNModC K M)` with `deg g < ψ(M)`, shows `g` constant on the slots
   (`mem_range_of_eval_eq_const`), so `jqNModC K p ∈ K(jqModC K)`, contradicting `hbase`.
   In the pin this is the private `jqNModC_prime_not_mem_adjoin` (`S_:1515`, 334 lines) plus a
   26-line wrapper.
3. **`relfinrank_fullC_mul_prime_pow`** — the prime-power step of the tower
   `fullC K (M * p ^ a)`: given the previous step (`hprev`) and, at `a = 0`, the
   non-membership (`hnm`), the relative degree
   `[fullC K (M * p ^ (a+1)) : fullC K (M * p ^ a)]` is `p + 1` if `a = 0` and `p` otherwise.
   Its engine is the `eFull` field (`fullC` pushed forward by `qExpand K p`), a root-counting
   degree bound (`le_natDegree_minpoly_jqModC_eFull`), the two-prime descent
   (`jqNModC_mem_of_div_primes`) and the single-prime generation step.

## 2. The measured cone

```bash
cd tools/deps
python3 frontier.py --ds --target ModularCurve.relfinrank_fullC_mul_prime_pow --list
python3 frontier.py --ds --target ModularCurve.minpoly_jqNModC_map_eq_prod_slots --list
python3 frontier.py --ds --target ModularCurve.jqNModC_prime_not_mem_fullC --list
python3 frontier.py --ds --target ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
```

Measured 2026-10-25 (`F` = the ported frontier, `--ds` = the avoided complex-analytic set):

| reading | value |
|---|---|
| D-S demand now | **1,192 nodes / 453,678 raw `S_` lines** |
| each of the three, `needed` | **1 node** (itself) — every premise is ported |
| the three, raw lines | 1,914 + 1,909 + 1,175 = **4,998** |
| D-S demand after landing all three (`--also` ×3) | **1,189 nodes / 448,680 lines** (−3 / −4,998) |
| the parent topic's capstone `qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull` | **22 needed nodes / 10,662 raw** |
| … after these three | **19 nodes / 5,664 raw** |

The "three largest" reading is `--ds --ready --top 0` (the whole ready set, sorted): the
`ModularCurve` rows are 1,914 / 1,909 / 1,175, then 868, 637, 510, 505, … So no other ready
`ModularCurve` node competes with this wave on size.

So the three are pure leaves of the D-S demand: they contribute exactly their own lines. Their
value is positional — they take the `C`-layer capstone's cone from 22 nodes to 19, and
`relfinrank_fullC_mul_prime_pow` is the premise of `package_of_socket` (1,003), the next node in
that cone.

## 3. What is pinned

Wrappers (the checker's statement authority — always take the binders from these):

- [Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean)
- [Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean)
- [Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean)

Proofs: the three `P2M/Sol/S_ModularCurve_<stem>.lean` files at the same pin, 1,914 / 1,909 /
1,175 lines. Each `S_` file also carries the pin's private copy of the headline; it is the
wrapper's statement verbatim (diffed, identical), so the private copy is not ported.

**The two twin `S_` files are one development.** `S_..._minpoly_jqNModC_map_eq_prod_slots.lean`
and `S_..._jqNModC_prime_not_mem_fullC.lean` declare the *same 80 declarations* in the same order;
`diff` is 85 lines, and every one of them is `p2m_*` namespace plumbing (the `p2m_open`/
`p2m_reactivate` paths) or the final `solution`/`#print axioms` tail. Each file proves **both**
headlines: `rval_aux` at `S_:832` feeds the minpoly headline (`S_:1849`), and
`jqNModC_prime_not_mem_adjoin` at `S_:1515` (which itself consumes `rval_aux`, `S_:1556`) feeds
the non-membership headline (`S_:1869`). Port once.

## 4. What is already paid — do not re-derive

Landed and statement-checked before this wave (see the record links):

| block | home | the order uses |
|---|---|---|
| `TS` (general field) and its API | `ModularCurve/Defs/TS.lean` | `TS`, `TS_coeff_mul`, `TS_coeff_of_lt`, `TS_ne_zero`, `TS_injective`, `TS_congr`, `qTwist_TS`, `qExpand_TS`, `qExpand_qTwist_TS`, `qTwist_TS_one_cycle`, `coeffMap_TS`, `jqModC_eq_TS`, `jqNModC_eq_TS`, `qExpand_jqNModC`, `qExpand_jqModC_eq_TS` |
| `qTwist` algebra | `Defs/Twist.lean` | `qTwist`, `qTwist_coeff`, `qTwist_one_apply`, `qTwist_qExpand`, `qTwist_qTwist`, `qTwistEquiv`, `qTwistEquiv_apply`, `coe_qTwistEquiv`, `coeffMap_qTwist` |
| the `Φ_p` slot packet | `Defs/PhiAtSlot.lean` | `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`, `phiAtSeed_natDegree`, `phiAtSeed_eval_map`, `phiAtSeed_eval_of_injective`, `aeval_intermediateField_eq_zero` |
| at-slot roots (char `p`) | `PhiGenSplitsAnyField.lean` | `splits_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot(_nodup)(_roots_nodup)_of_isPrimitiveRoot`, `isRoot_prime_at_slot_iff_of_isPrimitiveRoot`, `roots_phiAtSeed_TS`, `prod_form_ne_zero` (private) |
| `jqModC`/`jqNModC` and the pole | `Defs/JqCoeff.lean`, `X0/FunctionFieldFull.lean` | `jqModC`, `jqNModC`, `jqModC_rat`, `jqNModC_rat`, `coeff_jqModC_of_lt`, `coeff_jqModC_neg_one`, `order_jqModC`, `coeffEmb_jq`, `modularFunctionFieldC` |
| the `C` function fields | `X0/FunctionFieldFull.lean` | `divisorExpansionsC`, `modularFunctionFieldFullC`, `jqModCd_mem_full`, `jqModC_mem_full`, `full_degeneracyC_le`, `full_degeneracyC_map_le`, `JZeroC` |
| cyclotomic roots | `Defs/Cyclotomic.lean` | `isPrimitiveRoot_pow_div` |
| conjoints / cyclotomic conjugates | `Degree/JqCyclotomicConjugates.lean` | `units_pow_eq_one_of_isPrimitiveRoot`, `phiAtSeed_jqNModC_eval(_symm)`, `phiAtSeed_TS_eval(_symm)`, `jqNModC_congr` |
| `ψ` | `NumberTheory/DedekindPsi.lean`, `ModularCurve/Defs/DedekindPsi.lean` | `dedekindPsi_one`, `dedekindPsi_prime`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_prime_dvd`, `dedekindPsi_mul_prime_not_dvd`, `dedekindPsi_mul_of_coprime`, `dedekindPsi_pos` |
| the slot count | `FunctionFieldGeneration/SlotProduct.lean` | `card_slotFilter_eq_dedekindPsi` (**the** public counting export); `slotAt`/`slots` stay `private` there |
| the `qExpand` algebra map | `Defs/Laurent.lean` | `qExpandAlg`, `qExpandAlg_apply`, `qExpand_qExpand`, `qExpand_congr`, `qExpand_one_apply`, `qExpand_injective` |
| the `ℚ` twin of CL1 | `FunctionFieldGeneration/SlotProduct.lean` | `minpoly_jqN_map_eq_prod_slots`, `jqN_prime_not_mem_full` — **the proof template**, not a substitute |
| the `ℚ` twin of CL2 | `FunctionFieldGeneration/Generation.lean`, `DegreeStep.lean` | `jqN_mem_of_div_primes`, `w1_jqN_mem_adjoin_top_insert`, `full_eq_adjoin_full_div_prime`, `finrank_adjoin_jqN_prime_of_not_mem`, `relfinrank_full_eq_mul` — **the proof template** |
| the generic engines | `FieldTheory/CommonRoot.lean`, `ModularPolynomialProperties.lean` | `Polynomial.mem_range_of_unique_common_root`, `Polynomial.irreducible_of_transitive_ringAut`, `exists_phiIrreducible_evalSymm` |

**One definition-layer edit is the manager's, before dispatch** (§6.0): the `C` function fields
carry a vestigial `[NeZero N]`.

## 5. The pin's duplication, and the port's dedup table

Measured with `port_advise.py` + `port_plan.py` over the six target files (three `S_` + three
`Theorems/`): **254 declarations**, and

| reading | lines |
|---|---:|
| raw `S_` lines | 4,998 |
| duplicate copies inside the target set (removable by porting once) | 2,218 |
| boilerplate (`import`/`attribute`/`p2m_*`/`namespace`) | 105 |
| once-cost after dedup | 2,675 |
| already in the port (vetted, tier 1) | 398 |
| **net new math lines** | **2,277** |

* **130 declarations already have their statement in the port** (≈1,063 lines): 123
  byte-identical, 7 binder-only. These are the whole `TS`/`phiAtSeed`/at-slot-roots prelude
  (`S_:20–354`, ~330 lines ×3 files).
* **72 names are declared in ≥2 of the three files**, 2,178 removable lines: `rval_aux` 683,
  `jqNModC_prime_not_mem_adjoin` 334, `slotAt_mul` 108, `map_qExpand_minpoly_eq` 32, `slots_mul`
  29, `jqNModC_prime_not_mem_fullC` 52, … The two twin files account for most of it (§3).
* **Priced per file** (the two dispatches): the twin reads 1,914 raw → **1,462 net new**; the
  prime-power step 1,175 → **874 net new**. The two per-file readings sum 59 above the combined
  2,277, which is the twin's copies of the few declarations the step file also carries.
* **Three "substitutions" are false positives** and must not be used: `fullC` matched
  `x1x0FunctionFieldC` and `slots` matched `TateCurve.b` ×2 — the checker's type-only `def` match
  (a `def`'s statement is its type). Read and rejected; `fullC`'s real relationship to the port
  is `modularFunctionFieldFullC` (§6.0).
* **The pin's own copies that the port must not inherit**: the `divSet`/`fullC`/`qExpandₐK`/
  `eFull` block is written twice in the pin (`S_..._relfinrank_fullC_mul_prime_pow.lean:352–462`
  and `S_..._package_of_socket.lean:362–472`; `diff` = 4 lines, a blank and a line wrap); the
  slot-value block (`sv`, `sv_eq`, `sv_top`, `sv_inj`, `TS_congr'`) and the headline
  `rval_aux` block are each written in the twin's `C` and `ℚ` spellings.
* **Deliberately not cut, with the count**: the private `sv` block (`sv`, `sv_eq`, `sv_eq_TS`,
  `sv_inj`, `sv_top`, `TS_congr'`, ~40 lines) is re-declared `private` in the CL1 module at the
  pin's `C` text. The `ℚ` copy in `SlotProduct.lean` is `[Algebra ℚ K]`-bound and its
  `sv_eq`/`sv_top` *statements* name `coeffEmb K jq`; unifying them would edit a landed module's
  statements for ~40 lines. A `private` name does not clash across modules, so the copy costs
  nothing but text.

## 6. The module cut — 2 modules, 3 targets

**6.0 Ground (manager) — landed 2026-10-25** ([record](../../logs/x0-function-field-general-index.md)).
One hub edit, verified by probe:

`X0/FunctionFieldFull.lean` carries `[NeZero N]` on `divisorExpansionsC` and
`modularFunctionFieldFullC`. The binder is vestigial — 5 of the 7 lemmas of that section already
write `omit [NeZero N]` — and the pin's `C` statements use the fields at `L * n` and at `L`
freely (`divSet_mono`, `fullC_mono`, `fullC_le_iff`, `jqNModC_mem_fullC`, `jqModC_mem_fullC`,
`eFull_le_fullC`, `fullC_succ_eq_adjoin_insert_divSet`, `relfinrank_fullC_insert_eq_natDegree`),
where `[NeZero L]` is *not* synthesizable from the pin's hypotheses. **Drop `[NeZero N]` from
both `def`s (and the two `variable` lines, and the five `omit` lines).** Consumers of
`modularFunctionFieldFullC`: 52 references in 7 modules (of `divisorExpansionsC`: 7 in 2), all
of which supply `NeZero` today, so a call site only loses an implicit argument.

A scratch probe (a throwaway file importing `X0/FunctionFieldFull`, run 2026-10-25, exit 0, no
output) confirms the three definitional equalities the plan rests on, at `[NeZero L]`:

```lean
example (L : ℕ) [NeZero L] :
    divisorExpansionsC K L
      = {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ L ∧ x = jqNModC K d'} := rfl
example (L : ℕ) [NeZero L] :
    modularFunctionFieldFullC K L
      = IntermediateField.adjoin K
          {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ L ∧ x = jqNModC K d'} := rfl
example (n : ℕ) [NeZero n] (f : LaurentSeries K) : qExpandAlg K n f = qExpand K n f := rfl
```

So the pin's local `divSet`/`fullC`/`qExpandₐK` are the homed objects, and CL2 states them as
one-line `abbrev`s over `divisorExpansionsC`/`modularFunctionFieldFullC`/`qExpandAlg`. That keeps
the transcription verbatim (0 `own:` rows) while the mathematics has one home. The alternative —
stating the module over the homed names — costs ~10 `own:` rows and is recorded as the
fallback.

**6.1 CL1 — `ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean`** (new, wired;
**landed 2026-10-25**: 1,283 lines, 17 declarations, checker 2 ok / 0 own, both nodes `needed 0`):
`rval_aux` + the slot-value block + `map_qExpand_minpoly_eq` + the non-membership engine + the two
headlines. One module, because the pin writes one development and because the port's `ℚ` twin
(`SlotProduct.lean`) homes both headlines in one module. Splitting at the headline boundary would
put a public `rval_aux`-shaped interface (663 lines of proof) between two modules to isolate 26
lines.

**6.2 CL2 — `ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean`** (new, wired;
**landed 2026-10-25**: 1,108 lines, 45 declarations, checker 45 ok / 0 own, `needed 0`, dedup 0
clusters — see the order's §7):
the `C` prime-power step — the `fullC`/`eFull` layer, the two-prime descent, the root-counting
degree bound, and the headline. The mathematical fork with CL1 is real: CL1 is the **slot
product** (a minpoly formula), CL2 is the **field tower** (a relative degree). They share only
imports, so they are two modules.

## 7. Route — mathlib first, then the banked template

**Reuse wins.** `Polynomial.mem_range_of_eval_eq_const` is already homed at the `algebraMap` form
(`FieldTheory/CommonRoot.lean:111`); the pin's `C` text takes a general `ι : F →+* L`, so CL1
restates the `ι` form (30 lines) rather than deriving it — the pin's text is the authority and
its statement matches the wire. `Polynomial.irreducible_of_transitive_ringAut`,
`exists_phiIrreducible_evalSymm`, `IntermediateField.adjoin.finrank`,
`IntermediateField.extendScalars_adjoin`, `IntermediateField.relfinrank_eq_finrank_of_le` and
`minpoly.monic`/`natDegree_map`/`card_roots'` are the whole of CL2's tower algebra — none of it is
re-proved.

**The route is "transcribe with `C` substitution", measured, not assumed.** The pin's `C` proof
texts are the same proofs as their `ℚ` twins with `coeffEmb K (qExpand ℚ M ·)` replaced by
`qExpand K M (jqNModC K M)` and the `letI : Algebra ℚ⟮jq⟯ (LaurentSeries K)` block deleted:

| block | `C` lines | `ℚ` lines | differing lines |
|---|---:|---:|---:|
| `rval_aux` | 663 | 663 | 206 (31 %) |
| `jqNModC_prime_not_mem_adjoin` vs `jqN_prime_not_mem_adjoin` | 334 | 334 | 151 (45 %) |
| `jqNModC_mem_of_div_primes` vs `jqN_mem_of_div_primes` | 113 | 136 | 125 |

**Genuinely new mathematics** (no `ℚ` twin anywhere in the port or the pin):
`eFull` and its degree block — `le_natDegree_minpoly_jqModC_eFull` (the `p` `qTwist` conjugates of
`jqModC K` are distinct roots of `minpoly (eFull K p L₀) (jqModC K)` because `eFull` is
`qTwist`-fixed, so `p ≤ natDegree`), `relfinrank_eFull_fullC_eq_natDegree`, and
`natDegree_minpoly_le_of_phiAtSeed_root_of_root_mem` (34) with its three satellites. `grep` for
`eFull` / `le_natDegree_minpoly_jqModC_eFull` over the pin returns only the two `C` files
(`relfinrank_fullC_mul_prime_pow`, `package_of_socket`) — no `ℚ` twin exists. That is ~180 of
CL2's 874 lines; everything else in CL2 is a `C` replay of `Generation.lean` + `DegreeStep.lean`,
whose *statements* differ (base field `ℚ` vs `K`) so they cannot be imported — they are the
template, read side by side.

**Recorded negatives.** No mathlib lemma gives `[F(α) : F] = natDegree (minpoly F α)` in the
`eFull` shape (`IntermediateField.adjoin.finrank` needs the integrality instance, which the pin
supplies by `isIntegral_jqModC_eFull`); no mathlib statement of the modular `Φ_p` splitting at a
slot (it is the port's `PhiGenSplitsAnyField`); no `slots`-count in mathlib (the port's
`card_slotFilter_eq_dedekindPsi` is the interface).

## 8. Budget (correction ledger)

| row | lines |
|---|---:|
| structural content sum (raw `S_` lines) | 4,998 |
| − duplicate copies inside the set (the twin files, the pin's `C`/`ℚ` spellings) | −2,218 |
| − boilerplate never written | −105 |
| + 0 definition layer (the three respellings are `abbrev`s; one hub edit) | 0 |
| − already in the port (130 substituted declarations) | −398 |
| **content to write** | **≈2,277** |
| × written ÷ content (1.1–1.3, playbook §2.5) | **≈2,500 – 2,960 written** |
| **actual written** | **2,391** (CL1 1,283 + CL2 1,108) — the estimate was an upper bound |

Split over the two dispatches: **CL1 ≈1,400 content / 1,550–1,820 written**, **CL2 874 content /
960–1,140 written**. Both are inside the ~1,500-content-line dispatch size (§0.2); CL1 is at the
top of it, which is why it carries the two headlines and is dispatched first (it also has the
larger gain: 6 citers against 1).

The predictive unit here is the **number of `C` substitutions** (~15 in CL1, ~10 in CL2), not
lines: each is mechanical but each can trip a `simp`/instance shape (§9.2).

## 9. Risks, in the order they will bite, with the stop-early protocol

1. **`rval_aux` at the 200k heartbeat cap.** The pin sets `maxHeartbeats 6400000` on `rval_aux`
   (`S_:830`) and on `jqNModC_prime_not_mem_adjoin` (`S_:1513`). The port must write neither: the
   `ℚ` twin fits at the project cap (`SlotProduct.lean` carries no `set_option`), so the `C` text
   should too. If a declaration does not close, that is a **diagnostic**: split the step or name
   the lemmas; never add `set_option maxHeartbeats`. Report the declaration.
2. **`letI`/`Algebra` blocks and `NeZero` synthesis.** CL1 inherits the pin's `letI : Algebra F
   (LaurentSeries K) := ((qExpand K N).comp (algebraMap F (LaurentSeries K))).toAlgebra` idiom in
   ~6 places, and `haveI : NeZero a` from a `ha : a ≠ 0`. The port's linter flags `haveI` for
   `Prop`-classes — use `have`, as JQ1's record does.
3. **`slotAt` is private.** Both big CL1 proofs need the cardinality step
   `Multiset.card T = dedekindPsi M`. The pin proves it by unfolding its own `slotAt`; the port's
   `slotAt`/`slots` are private in `SlotProduct.lean` *by design* (the slot-counting audit), and
   `card_slotFilter_eq_dedekindPsi` is the public export for exactly this consumer. Prove the
   step through it. **Stop-early**: if that costs more than ~30 lines of reshaping, report — the
   manager will promote `slotAt`/`slotAt_eq` (a 2-line edit) rather than let the worker reshape a
   landed module.
4. **`C`-layer drift (~15 renames).** `jq` → `jqModC`, `jqN` → `jqNModC`,
   `modularFunctionField(Full)` → `…(Full)C`, `coeffEmb K (qExpand ℚ M x)` → `qExpand K M (jqNModC
   K x)`, `ℚ⟮jq⟯` → `K⟮jqModC K⟯`. Keep the list in the result note; do not re-cut the cone over
   it.
5. **The `sv` if-form.** The headline's product is over `if h : a = 0 then 0 else …`, not over
   `sv K ζ a b`; `sv`'s body *is* that `dite`, so the two agree by `unfold sv`/`rfl`. The pin's
   private `rval_aux` states the `sv` form and the headline the `if` form — keep both texts
   exactly (the checker accepts both, each has a wire copy).
6. **`Multiset.range` vs `Finset.range p`.** The pin mixes them (`roots_prime_at_slot` returns a
   `Multiset`, the products are `Finset`); `Fin.prod_univ_eq_prod_range` and the ported
   `roots_prime_at_slot` statements settle it. Do not re-state a ported lemma in `Fin` form.
7. **CL2's `abbrev`s must not become a second home.** `abbrev fullC := modularFunctionFieldFullC`
   etc. live in CL2 only, with a docstring saying so; nothing else may import them. If a second
   module needs them, that is a promotion for the manager (§3.7 of the playbook), not a copy.

## 10. Verification (per order; the union is the set's gate)

1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` in the edit loop;
   `flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.<Module>` per module (single
   module only — **never** a tree `lake build`), **0 warnings**, no `sorry`.
2. `#print axioms` on each headline → `[propext, Classical.choice, Quot.sound]`.
3. `python3 spec/check_port.py --force <module>` → **0 mismatch / 0 missing / 0 own** (with the
   `abbrev`s of §6.0; if the `own:` fallback is taken, every row must carry its reason in
   `spec/decl_markers.tsv`).
4. `python3 tools/deps/dedup.py --module <module>` → 0 clusters; `move_dead.py` → 0 dead.
5. `python3 tools/deps/frontier.py --ds --target <node> --list` → `needed 0`, "target is ported",
   for each of the three.
6. `lean/spec/ModularCurveConsumer.lean` gains a zone that **uses** the three statements (applies
   the minpoly product at a concrete `M`, the step at `a = 0` and `a = 1`), so deleting a module
   fails the consumer.
7. `tools/check_math_delimiters.py` on any Markdown touched.

## 11. Out of scope

- `package_of_socket` (1,003), `finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` (518) and
  `finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi` (238): the next `C`-layer
  nodes, which consume CL2's `eFull` and the `divSet`/`fullC` vocabulary. They are why the
  vocabulary is homed once, but they are not this wave.
- `ModularCurve.StarBank.*` (the eta/Hasse-polynomial descent): a separate set (parent topic §4
  Set B).
- Any re-derivation of the ported `ℚ` layer. Where a `C` proof can call a ported `ℚ` theorem, call
  it.
- Promoting `slotAt`/`slots` or restructuring `SlotProduct.lean`: only on a reported blocker
  (§9.3).

## 12. Reporting back

Wanted in the result note, whatever the answer:

1. The written-line count per module vs §8's bound, and which blocks needed reshaping (the `C`
   substitution count that actually bit).
2. Whether the `abbrev` route (§6.0) held the checker at **0 `own:`** rows, or the fallback was
   needed; if the fallback, the exact rows.
3. Whether `card_slotFilter_eq_dedekindPsi` could carry the cardinality step (§9.3) — this
   calibrates the "public counting export" decision for the rest of the `C` layer.
4. The frontier reading per node, and the parent cone's new figure.

## 13. Next wave: the socket assembly is priced, and it is a transcription (2026-10-25)

The two socket nodes of §11's first bullet have been measured against pin `aa2d8b3`, and the
answer changes their shape: **`package_of_socket` is the assembly layer over exactly the vocabulary
this wave homed, not a new development.** 74 of its 82 declarations are already in the port (the
whole `TS`/`roots` prelude and the `divSet`/`fullC`/`eFull`/prime-step block this wave landed);
`port_advise` reads 56 of 85 statements substituting byte-identically. So the new content is
**223 lines**, and `finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` (and its `…_of_charZero` twin,
32 differing lines of plumbing) adds **242** — 465 together, against the 1,521 raw of the two files.

Two consequences for this topic:

- **`pkg_of_socket` takes the prime step as a parameter** (`hKG1`), and the pin fills it with
  `ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime` — a node this wave's cone touches but
  did not port. So the socket is *downstream* of that step, and it is the only producer of `hall`
  in the `C` layer: the engines this wave landed take `hall`, they do not make it.
- The assembly belongs in `PrimePowerStepAnyField.lean` (where `fullC`, `eFull`, `divSet` and
  `relfinrank_fullC_step` live), with `Pkg` as the one `abbrev` for the `hall` block — not as a
  1,003-line transcription.

Orders: [WORKORDER-JQ2](WORKORDER-JQ2-mffc-mul-prime.md) (the prime step, 231 net new) and
[WORKORDER-CL4](WORKORDER-CL4-socket-assembly.md) (the assembly, 465 net new). Either may land
first. `finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi` (238) is still unscoped,
and the argument, measurements and the two frontier readings are in the parent topic
[§10.3](../functionFieldGeneration/TOPIC-qexp-function-field-c.md).

**Both landed 2026-10-25, and the vocabulary homed by this wave carried them.**
`FunctionFieldGeneration/MffCMulPrime.lean` (251 lines, the prime step) and the nine-declaration
assembly appended to `PrimePowerStepAnyField.lean` (+269) close `package_of_socket`;
`Degree/FinrankAdjoinJqNModC.lean` (367) closes the transport and both degree headlines (the twin
pair, ported once); `Defs/QExpandCharP.lean` (125) the two char-`p` premises. Written 1,012 lines
for 818 net new content. The assembly imported every one of this wave's `fullC`/`eFull`/`divSet`/
`relfinrank_*` declarations and re-proved none of them — 74 of the pin file's 82 declarations were
already in the tree — so the ~2,700-line "socket group" cost 465, as measured in §13's opening
paragraph. All five nodes read `needed 0`, and the D-S column fell to 1,184 nodes / 446,334 raw,
taking this cone from 19 nodes / 5,664 raw to **14 / 3,318**. Records:
[logs/cl4-socket-assembly.md](../../logs/cl4-socket-assembly.md) and the parent topic §10.3.
`finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi` (238) remains unscoped.
