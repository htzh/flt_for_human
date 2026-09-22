# Topic 16: the degree of one prime-power step

**Status: done (2026-09-22) — one goal round.** `FunctionFieldGeneration/DegreeStep.lean`
is **455 lines**, plus 150 promotion lines in `Defs/Laurent.lean`/`Defs/Fields.lean`/
`Defs/Twist.lean`/`Defs/TS.lean` — **605** against ≈435 pin lines (ratio ≈1.39),
inside the scouted `~500–650`. All three nodes are public, statements the
`Theorems/` wrappers' verbatim, `#print axioms` clean, `lake build` green with 0
warnings and no `sorry`. The checker moved **278 → 288** (0 mismatched, 0 missing)
and the consumer's Zone N fills three of the seven `Inputs` fields, so the
capstone's debt is **5 → 4**. Every route risk resolved on the first build,
including the whole pow-succ node (the factor peel, `range_map_eq_rUnit`, and the
cyclotomic automorphism block); `coeffMapEquiv` took `RingEquiv.ofBijective`. Two
corrections to this work order: the `coeffMap_*` promotions live in
`Defs/Twist.lean`/`Defs/TS.lean` (the import layering, as with T14), and the
checker needed the three `S_` carriers as well as the three wrappers. The `p = 3`
non-vacuity example for `irreducible_of_transitive_ringAut` is still out of reach
(mathlib has no cube roots); see [logs/ffg-port.md](../../logs/ffg-port.md) §2i.
T14 and T15 are done. Every Φ_p and engine input this topic needs is a ported,
public theorem: T12's `exists_phiIrreducible_evalSymm`, T13's
`splits_of_prime`/`splits_prime_at_slot`, T14's `qTwistEquiv` family and
`roots_phiProd_conj*`, and T4's
`Polynomial.irreducible_of_transitive_ringAut`.

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

**Audience.** A fresh session taking T16 of the `functionFieldGeneration` effort.
Read, in this order:

1. [PORTING-FFG.md](../PORTING-FFG.md) §7.8 (the topic order and the audited
   routes) and §1 (the design rules);
2. [math/010](../../../math/010-function-field-generation.md) §6 — the two degree
   statements and their proofs; this topic is that section's second half;
3. [TOPIC-descent.md](TOPIC-descent.md) (T15) and [TOPIC-slot-machinery.md](TOPIC-slot-machinery.md)
   (T14) — the two predecessors whose vocabulary and instance machinery this
   topic reuses;
4. [studies/flt-ffg-field-theory.md](../../../studies/flt-ffg-field-theory.md) §2
   (Tier 0's third lemma, Tier 1's bridges);
5. [logs/audit-prelude-bridges.md](../../logs/audit-prelude-bridges.md) §b.4
   (`w1_relfinrank_insert`) and §(c) — the bridge dedup this topic should take;
6. [porting-playbook.md](../../porting-playbook.md) §3.9, §3.11 and §7.3.

## 1. Goal, and why this topic

**Goal.** Port the degree half of the strong induction:

1. **`finrank_adjoin_jqN_prime_of_not_mem`** — the first prime power:
   `` $`[F(j(q^p)) : F] = p + 1`$ `` for `jq ∈ F` and `jqN p ∉ F`. The minimal
   polynomial divides `Φ_p(jq, Y)`, whose `p+1` roots are cycled by the nome twist
   `qTwistEquiv ζ`; `irreducible_of_transitive_ringAut` makes it irreducible, so
   its degree is `Φ_p`'s.
2. **`finrank_adjoin_jqN_pow_succ_of_not_mem`** — later prime powers:
   `` $`[F(j(q^{p^{k+2}})) : F] = p`$ ``. Now `Q = Φ_p(j(q^{p^{k+1}}), Y)` has the
   root `j(q^{p^k}) ∈ F`, so it factors as `(X − j(q^{p^k})) · P` with `deg P = p`;
   the automorphism is no longer the twist but a **coefficient automorphism**
   `coeffMapEquiv τ` (`τ` from a generator of `(ZMod p)ˣ`), which cycles `P`'s `p`
   roots.
3. **`relfinrank_full_eq_mul`** — the tower dispatcher: the relative degree of one
   full prime-power step is `p + 1` when `a = 0` and `p` otherwise, by the two
   statements above plus the mathlib tower law.

The third is an `Inputs` field, so proving all three takes the capstone's debt
**5 → 4**.

**Why now.** T16 is the last topic whose content is a *general* field-theoretic
degree fact about `F(jqN p)`; T17–T19 are non-membership and the slot product.
It is also where three widely-duplicated transfer lemmas finally get one home
(§4), which the 2026-09-22 bridge audit measured at 41 / 14 / 3 pin copies.

**Settled: the two degree proofs use different automorphisms, and the second is
the hard one.** The prime node (52 lines) is the twist argument, the `p+1`
analogue of T13's `finrank_adjoin_jqN_eq_of_prime`, but stated over an arbitrary
`F ∋ jq`. The pow-succ node (187 lines) introduces the cyclotomic coefficient
automorphism and a 73-line re-indexing helper `range_map_eq_rUnit`; it is the
only genuinely new mathematics in the topic, and the audit's route tests apply to
it, not to the prime node.

## 2. The scouted inventory

Three pin files, none of which shares a development with another:

| node | pin file | node span | size |
|---|---|---|---|
| `finrank_adjoin_jqN_prime_of_not_mem` | `S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean` (348) | 293–344 | 52 |
| `finrank_adjoin_jqN_pow_succ_of_not_mem` | `S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean` (758) | 563–749 | 187 |
| `relfinrank_full_eq_mul` | `S_ModularCurve_relfinrank_full_eq_mul.lean` (81) | 49–72 | 24 |

### 2.1 Helpers and bridges, by file

Most of files 1 and 2 is the T14 prelude, already ported. What is **not** ported:

| helper | pin | span | status |
|---|---|---|---|
| `coeffEmb_injective'` | prime 268–273 | 6 | **redundant** — the port's public `Defs/Laurent.lean:326 coeffEmb_injective` states the same thing |
| `iota_injective` | prime 275–276 | 2 | port once (`coeffEmb_injective.comp qExpand_injective`) |
| `phiAtSeed_iota_jq_eq_phiProd` | prime 278–284 | 7 | port (uses T13's `splits_of_prime`) |
| `coeffMap_qTwist` | pow 422–429 | 8 | **private** in `PhiGenDescent.lean:199` — promote |
| `coeffMap_coeffEmb_algHom` | pow 430–434 | 5 | **private** in `PhiGenSplits.lean:97` — promote |
| `coeffMap_TS` | pow 435–445 | 11 | **private** in `PhiGenSplits.lean:102` — promote |
| `coeffMapEquiv` + `_apply` | pow 446–465 | 21 | port (the audit's `RingEquiv.ofBijective` win) |
| `jqN_congr` | pow 467–469 | 3 | **redundant** — public `Defs/Jq.lean:199 jqN_congr` (T14) |
| `rUnit` | pow 470–472 | 4 | port (a private `def`) |
| `range_map_eq_rUnit` | pow 474–546 | 73 | port — the topic's biggest helper |
| `jqN_congr'` | relfinrank 21–22 | 2 | **redundant** — same as `jqN_congr` |
| `w1_relfinrank_insert` | relfinrank 24–42 | 19 | port (Tier-1; the audit says it already uses the mathlib tower law) |

The three redundant bridges are dropped, not ported: the audit's "count before
dropping" rule is satisfied by the statement comparison above, and the `grep -c`
for each name in the port should be recorded. `coeffMap_qTwist` is the audit's
41-copy lemma and `coeffMap_TS` its 14-copy one, so promoting them once is the
topic's main dedup.

### 2.2 What each node uses

- **prime**: T12's `exists_phiIrreducible_evalSymm`; T14's `phiAtSeed*`,
  `qTwistEquiv`/`_apply`, `qTwist_iota_of_pow_eq_one`, `qTwist_TS_one_cycle`,
  `phiProd`, `roots_phiProd_conj(_nodup)`, `TS`, `iota_jqN`;
  `Polynomial.irreducible_of_transitive_ringAut` (T4);
  `dedekindPsi_prime`, `Polynomial.eval_map_algebraMap`, `minpoly.eq_of_irreducible_of_monic`,
  `IntermediateField.adjoin.finrank`.
- **pow-succ**: the above plus `Polynomial.mul_divByMonic_eq_iff_isRoot`,
  `Monic.of_mul_monic_left`, `Polynomial.splits_iff_card_roots`, the new
  `coeffMapEquiv`/`coeffMap_TS`/`coeffMap_coeffEmb_algHom`/`rUnit`/`range_map_eq_rUnit`,
  and mathlib's cyclotomic-automorphism API: `IsCyclotomicExtension.autEquivPow`,
  `IsPrimitiveRoot.autToPow`/`autToPow_spec`/`autToPow_injective`,
  `Polynomial.cyclotomic.irreducible_rat`, `IsCyclic.exists_generator`,
  `ZMod.card_units`, `orderOf_eq_card_of_forall_mem_zpowers`.
- **relfinrank**: `w1_relfinrank_insert`, then the two nodes above (the `a = 0`
  branch via `qExpand_one_apply` and `jqd_mem_full`).

## 3. The mathlib-first audit

Audited against `v4.34.0`. This is a **glue topic with one new engine call**: the
engine is T4's, and the two genuine mathlib wins are `RingEquiv.ofBijective`
(`coeffMapEquiv`) and the cyclotomic-automorphism API.

| pin piece | mathlib / port | verdict |
|---|---|---|
| `irreducible_of_transitive_ringAut` (both nodes) | `FieldTheory/CommonRoot.lean:148` (T4) | **import** |
| `coeffMapEquiv` + `_apply` | `RingEquiv.ofBijective` (`Algebra/Ring/Equiv.lean:446`) | route-check; the pin's explicit `where` is the fallback |
| `w1_relfinrank_insert` | `IntermediateField.relfinrank_eq_finrank_of_le` + `extendScalars_adjoin` (audit b.4) | port (mathlib tower law inside) |
| `iota_injective`, `phiAtSeed_iota_jq_eq_phiProd` | port API (`qExpand_injective`, `coeffEmb_injective`, `splits_of_prime`) | port (short) |
| `rUnit`, `range_map_eq_rUnit` | none — multiset re-indexing by `(ZMod p)ˣ` | port |
| the pow-succ automorphism | `IsCyclotomicExtension.autEquivPow`, `IsPrimitiveRoot.autToPow*`, `Polynomial.cyclotomic.irreducible_rat`, `IsCyclic.exists_generator`, `ZMod.card_units` | call; the heaviest route test |
| the strips/factors | `eval_map_algebraMap`, `eval₂_hom`, `mul_divByMonic_eq_iff_isRoot`, `Monic.of_mul_monic_left`, `splits_iff_card_roots`, `minpoly.eq_of_irreducible_of_monic`, `IntermediateField.adjoin.finrank` | call |

**Headline.** No new mathlib-absent lemma; the engine is T4's. The audit's value
is again negative on replacements and positive on the two imports above.

## 4. Module split

| module | gains | imports |
|---|---|---|
| `FLTForHuman/ModularCurve/Defs/Laurent.lean` | **promote to public** `coeffMap_qTwist`, `coeffMap_coeffEmb_algHom`, `coeffMap_TS` (from `PhiGenDescent.lean`/`PhiGenSplits.lean`, deleting their private copies); add `coeffMapEquiv` + `_apply`, `iota_injective` | current |
| `FLTForHuman/ModularCurve/Defs/Fields.lean` | `w1_relfinrank_insert` (the `relfinrank`/`extendScalars_adjoin` bridge, beside `modularFunctionFieldFull`) | current |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/DegreeStep.lean` **(new)** | the three nodes plus `phiAtSeed_iota_jq_eq_phiProd`, `rUnit`, `range_map_eq_rUnit` | `Defs/Laurent`, `Defs/Fields`, `Defs/PhiAtSlot`, `PhiSlotRoots`, `PhiGenSplits`, `ModularPolynomialProperties`, `FieldTheory/CommonRoot` |

`DegreeStep.lean` sits beside `Target`/`Collapse`/`Spine`/`Descent`; one
declaration, one home. The three promotions are the T11/T13 files' to lose:
`PhiGenDescent.lean` and `PhiGenSplits.lean` must import the public copies rather
than keep private twins. If the pow-succ node proves unmanageable, split the topic
at its natural seam — `finrank_adjoin_jqN_pow_succ_of_not_mem` plus
`rUnit`/`range_map_eq_rUnit` into their own module — and say so in the log.

## 5. Prerequisites — public, verified

`qTwistEquiv`/`_apply`, `qTwist_iota_of_pow_eq_one`, `qTwist_TS_one_cycle`,
`phiProd`, `roots_phiProd_conj(_nodup)`, `phiAtSeed` + its lemmas,
`roots_prime_at_slot*`, `iota_jqN`, `TS_congr` (T14); `splits_of_prime`,
`splits_prime_at_slot` (T13); `exists_phiIrreducible_evalSymm` (T12);
`irreducible_of_transitive_ringAut` (T4); `dedekindPsi_prime`, `coeff_jq_neg_one`,
`coeff_jq_of_lt`, `jqN_congr`, `coeffEmb_injective` (`Defs/Jq.lean`,
`Defs/Laurent.lean`); `cycUnit`/`cycUnit_spec`/`cycUnit_pow`,
`exists_isPrimitiveRoot_cyclotomicField` (`Defs/Cyclotomic.lean`). Nothing else is
`private` after §4's three promotions.

## 6. Verification

1. **`#print axioms`** clean on all three public declarations plus the promotions.
2. **Statement checker.** Add the three `Them_` wrappers to `SOURCES`:
   `Them_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean`,
   `…_finrank_adjoin_jqN_pow_succ_of_not_mem.lean`, `…_relfinrank_full_eq_mul.lean`.
   All are public wrappers, so they verify by direct name match. Report the
   before/after count (T15 left it at **278**).
3. **`PORT_FILES`** gains `FunctionFieldGeneration/DegreeStep.lean`.
4. **The wire test — Zone N.** T15 took Zone M; this takes the next free zone in
   `spec/ModularCurveConsumer.lean`. The meaningful test is the `Inputs`-field
   composition, as in Zone M: build a partially discharged `Inputs` with
   `relfinrank_full_eq_mul := ModularCurve.relfinrank_full_eq_mul`, so the debt
   visibly drops to four fields. Also record the nontrivial instantiation the T4
   log left open: the pow-succ node applies `irreducible_of_transitive_ringAut`
   with a **non-identity** `σ = coeffMapEquiv τ` cycling `p - 1` roots — if it is
   in reach, a small `example` at `p = 3` would finally give that engine a
   nontrivial wire test (log §8.6's open question).
5. **Build.** `lake build` green, 0 warnings, no `sorry`; library-wide `grep`.
6. **README** gains `DegreeStep.lean` and the promoted bridges; **`PORTING-FFG.md`
   §7.8** marks T16 done and records the measured cost; `logs/ffg-port.md` gains
   T16's entry.

## 7. Budget and route risks

T16-specific pin content is **≈ 435 lines**: prime 52 + pow-succ 187 + relfinrank
24, plus ≈ 145 helper lines (of which ≈ 11 are dropped as redundant and ≈ 24 are
promotions moved, not new). Expect **≈ 500–650 port lines** and **two goal
rounds** — the row's `~500` is the pin-side estimate, and the pow-succ node is the
intricate one.

**Route risks, in the order they will bite.**

- **The cyclotomic automorphism block (pow-succ pin 673–710).** This is mathlib's
  `IsCyclotomicExtension.autEquivPow` / `IsPrimitiveRoot.autToPow` API, which
  nothing in the port exercises yet. Route-check the statements and their
  instance requirements (`IsCyclotomicExtension {p} ℚ K`, `Polynomial.cyclotomic p ℚ`
  irreducible) in a scratch file before transcribing; this is the one place a
  mathlib drift could change the proof's shape.
- **`coeffMapEquiv`'s route.** Try `RingEquiv.ofBijective (coeffMap ↑τ) hf` first
  (the audit's positive ingredient, with bijectivity from `τ.symm`); the pin's
  explicit `where` with `coeffMap_coeffMap`/`coeffMap_congr`/`coeffMap_id` is the
  17-line fallback. Record which.
- **`range_map_eq_rUnit` (73 lines).** Pure multiset re-indexing; transcribe it
  rather than seeking a shorter route on the first attempt. It is the topic's
  biggest single helper and the likely place a build stalls.
- **The three promotions.** `coeffMap_qTwist` lives in `PhiGenDescent.lean` (T11)
  and `coeffMap_coeffEmb_algHom`/`coeffMap_TS` in `PhiGenSplits.lean` (T13); moving
  the canonical copies to `Defs/Laurent.lean` and re-pointing those modules is the
  one edit outside the new module. Watch for an import cycle: `Defs/Laurent.lean`
  is upstream of both, so the direction is safe, but `coeffMap_TS` mentions `TS`
  and therefore must import `Defs/TS.lean` (as T14's layout discovered).
- **The `Algebra F (LaurentSeries K)` / `ι` instance.** Both nodes install it
  exactly as T15 did; that closed on the first build, so transcribe the same
  shape and do not re-derive.
- **`w1_relfinrank_insert`.** The audit confirms it already uses mathlib's tower
  law; port as-is, no replacement to hunt.

## 8. Definition of done (T16)

- [ ] `Defs/Laurent.lean`/`Defs/Fields.lean` extended, the three bridges public,
      and `PhiGenDescent.lean`/`PhiGenSplits.lean` no longer carry private twins;
- [ ] `FunctionFieldGeneration/DegreeStep.lean` created, three nodes public,
      statements verbatim from the wrappers;
- [ ] `lake build` green, 0 warnings, no `sorry`;
- [ ] `#print axioms` clean on all three plus the promotions;
- [ ] the three wrappers in `SOURCES`, 0 mismatched, 0 missing; `PORT_FILES`
      updated;
- [ ] Zone N recorded and green, with the `Inputs` composition (debt 5 → 4) as its
      wire test;
- [ ] README, `PORTING-FFG.md` §7.8 and `logs/ffg-port.md` updated;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The debt** — confirm `relfinrank_full_eq_mul` is an `Inputs` field
   discharged (5 → 4) and that the structure's statements were not touched.
2. **The routes** — did the cyclotomic-automorphism block transcribe as-is? Did
   `coeffMapEquiv` take `RingEquiv.ofBijective`? Was `range_map_eq_rUnit` the
   stall point?
3. **The promotions** — the three `coeffMap_*` bridges are public, the private
   twins gone, no cycle; and the `grep -c` counts for the four dropped/duplicated
   names.
4. **The cost** — rounds, declarations, lines, ratio against ~435, and the
   corrected T16 figure for §7.8.
5. **The non-vacuity bonus** — if the `p = 3` `example` for
   `irreducible_of_transitive_ringAut` closed, record it against log §8.6.

## 10. Where this sits

T16 is the second `Inputs`-field topic and the last purely field-theoretic one:
with it, `Tight`'s degree input is proved and the debt is four. T17
(non-membership) and T18 (generation) follow from the slot product T19 supplies;
the dependency order and the audited T19 route are
[PORTING-FFG.md](../PORTING-FFG.md) §7.8.
