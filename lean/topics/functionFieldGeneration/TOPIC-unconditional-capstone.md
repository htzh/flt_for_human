# Topic 20: the unconditional capstone

**Status: DONE (2026-09-22) — the effort is complete.** T14–T19 are done and the
`Inputs` structure is total. `Capstone.lean` constructs it, proves the
unconditional `functionFieldGeneration`, ports the corollary layer and the
interface tail, and the consumer's Zone A capstone is now the theorem. The body
below is the plan as executed; §7's predicted friction point (the `Hall` binder)
did not bite, and the fraction-ring tail closed on the second build. See
[logs/ffg-port.md](../../logs/ffg-port.md) §2m for the measured cost.

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
> - **Never raise `maxHeartbeats`.** The global cap is `4000000`
>   (`lakefile.lean`). The optional tail's fraction-ring construction is the one
>   place a `whnf` might bite; if it does, quarantine and bisect.

**Audience.** A fresh session taking T20. Read, in this order:

1. [PORTING-FFG.md](../../PORTING-FFG.md) §7.8 (including the T20 row and the
   effort's definition of done) and §1;
2. [TOPIC-conditional-capstone.md](TOPIC-conditional-capstone.md) — the
   *conditional* artifact T20 makes total; do not re-derive `Spine.lean`;
3. [TOPIC-slot-product.md](TOPIC-slot-product.md) (T19) and the T15–T18 work
   orders — the fields T20 assembles;
4. [math/010](../../../math/010-function-field-generation.md) §7 — the assembly;
5. [porting-playbook.md](../../porting-playbook.md) §7.3 and the friction-log
   convention.

## 1. Goal, and why this topic

**Mandatory capstone (≈60–100 port lines).**

1. **Construct `Inputs`** from the seven proved theorems:

   | `Inputs` field | proved by |
   |---|---|
   | `full_eq_adjoin_full_div_prime` | `Generation.lean` (T18) |
   | `jqN_prime_not_mem_full` | `SlotProduct.lean` (T19) |
   | `jqN_pow_not_mem_adjoin_full` | `Nonmembership.lean` (T17) |
   | `minpoly_jqN_map_eq_prod_slots` | `SlotProduct.lean` (T19) |
   | `modularFunctionField_eq_full_of` | `Descent.lean` (T15) |
   | `jqN_div_mem_modularFunctionField` | `Descent.lean` (T15) |
   | `relfinrank_full_eq_mul` | `DegreeStep.lean` (T16) |

2. **`ModularCurve.functionFieldGeneration (N) [NeZero N] : FunctionFieldGeneration N`**,
   verbatim from `Theorems/Thm_ModularCurve_functionFieldGeneration.lean`, as
   `functionFieldGeneration_of inputs N`.
3. **The corollary layer** the rest of FLT consumes — `modularFunctionField_eq_full`,
   `finrank_adjoin_jqN_eq_dedekindPsi`, `relfinrank_full_eq_dedekindPsi` — each a
   few lines from `hall_all` (see §4).
4. **Replace the consumer's last `sorry`**: `spec/ModularCurveConsumer.lean` line
   175 becomes `functionFieldGeneration N`, so the file carries **0** `sorry`s
   and the target is finally unconditional.

**Interface-completion tail (≈160–180 port lines; needed for the effort's §2.1
claim).** §2.1's out-of-cone ≥5-indegree tier names five nodes; four are done and
**`exists_phiIrreducible_of_finrank_eq` is the fifth**, so it is required for the
effort's "100% covered" definition of done even though the capstone does not need
it:

5. **`exists_monic_evalAtJ_jqN_eq_zero`** — the integrality input.
6. **`exists_phiIrreducible_of_finrank_eq`** — given the degree, an irreducible
   datum at every level.
7. **`exists_phiIrreducible`** — the corollary of (6) and (3), consumed downstream.

**Why this is the last topic.** (1)–(4) make the headline true; (5)–(7) close the
interface. Nothing else remains in §7.8's 17-node remainder.

## 2. The scouted inventory

Three small pin developments plus the assembly, which exists in the pin's
`S_ModularCurve_functionFieldGeneration.lean` as the tail of `hall_all`'s file.

| node | pin file | span | own |
|---|---|---|---|
| `functionFieldGeneration` | `S_ModularCurve_functionFieldGeneration.lean` | 728–732 | 5 (plus the `Inputs` literal, ours) |
| `modularFunctionField_eq_full` | same | 722–727 | 6 |
| `finrank_adjoin_jqN_eq_dedekindPsi` | same | 713–721 | 9 |
| `relfinrank_full_eq_dedekindPsi` | same | 739–749 | 11 |
| `exists_monic_evalAtJ_jqN_eq_zero` | `S_…_exists_monic_evalAtJ_jqN_eq_zero.lean` (109) | 63–104 | ≈42 |
| `exists_phiIrreducible_of_finrank_eq` | `S_…_exists_phiIrreducible_of_finrank_eq.lean` (159) | 46–154 | ≈109 |
| `exists_phiIrreducible` | `S_ModularCurve_functionFieldGeneration.lean` | 733–738 | 6 |

### 2.1 Helpers and status

| helper | pin | span | status |
|---|---|---|---|
| `hall_all` | `S_…_functionFieldGeneration.lean` | 614–700 | **already ported**, `private` in `Spine.lean:308` — promote (§4) |
| `phiAtSeed` + its six lemmas | monic file 16–55 | 40 | **drop** — T14 (`Defs/PhiAtSlot.lean`) |
| `jqN_congr` | monic file 56–62 | 7 | **drop** — `Defs/Jq.lean` |
| `coe_evalAtJGen`, `aeval_map_intCast`, `evalAtJ_C` | of_finrank_eq 20–32 | 13 | port (3 short evaluation lemmas) |
| `evalAtJGen_injective` | of_finrank_eq 33–45 | 13 | **already in the port** (`ModularPolynomialIrreducible.lean:103`) — import |
| the fraction-ring construction | of_finrank_eq 46–154 | 109 | port **only if** the short route fails (§7) |

### 2.2 What each node uses

- **The assembly**: `Spine.lean`'s `Inputs` and `functionFieldGeneration_of`, plus
  the seven proved field theorems. Nothing else.
- **`modularFunctionField_eq_full`**: `hall_all`'s `.2`.
- **`finrank_adjoin_jqN_eq_dedekindPsi`**: `hall_all`'s `.1`.
- **`relfinrank_full_eq_dedekindPsi`**: `modularFunctionField_eq_full`,
  `relfinrank_modularFunctionField` (`Defs/Fields`),
  `finrank_adjoin_jqN_eq_dedekindPsi`.
- **`exists_monic_evalAtJ_jqN_eq_zero`**: T14's `phiAtSeed*` and `jqN_congr`.
- **`exists_phiIrreducible_of_finrank_eq`**: (5), `evalAtJGen_injective`
  (`ModularPolynomialIrreducible.lean:103`), the `evalAtJ` evaluation lemmas, and
  mathlib's `IsFractionRing`/`IsLocalization.integerNormalization` API.
- **`exists_phiIrreducible`**: (6) and (3).

## 3. The mathlib-first audit

Audited against the pinned `v4.34.0`. This is an assembly topic: the engines are
all ported and the only new mathematics is in the optional tail.

| pin piece | mathlib / port | verdict |
|---|---|---|
| the `Inputs` assembly | `Spine.lean` `Inputs` + `functionFieldGeneration_of` | **use** (T20's whole mandatory content) |
| the corollaries | `hall_all` (promote), `relfinrank_modularFunctionField`, `functionFieldGeneration_iff_full_eq` | **use** |
| `exists_monic_evalAtJ_jqN_eq_zero` | T14 `phiAtSeed*` | port ≈42 |
| `exists_phiIrreducible_of_finrank_eq`'s fractions | `IsFractionRing`, `IsLocalization.integerNormalization_spec`, `mem_nonZeroDivisors_iff_ne_zero`, `map_zsmul` | call; route-check the short alternative |
| `evalAtJGen_injective` | already public: `ModularPolynomialIrreducible.lean:103` | **import** |
| `isUnit_iff_ne_zero`, `IntermediateField.mem_adjoin_simple_iff`, `div_mul_cancel₀` | mathlib | call |

**Headline.** No mathlib-absent lemma. The mandatory capstone is a structure
literal and three one-liners; the tail is the only place with real proof content,
and its pin route (a `ℤ[X] → ℚ⟮jq⟯` fraction-ring structure) deserves a
route-check before transcription.

## 4. Module

| module | gains | imports |
|---|---|---|
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean` **(new)** | the `inputs` definition, public `functionFieldGeneration`, `modularFunctionField_eq_full`, `finrank_adjoin_jqN_eq_dedekindPsi`, `relfinrank_full_eq_dedekindPsi`; and the tail `exists_monic_evalAtJ_jqN_eq_zero`, `exists_phiIrreducible_of_finrank_eq`, `exists_phiIrreducible` | `FunctionFieldGeneration.Spine`, `.Descent`, `.DegreeStep`, `.Nonmembership`, `.Generation`, `.SlotProduct`, `ModularCurve.ModularPolynomialUniqueness`, `ModularPolynomialProperties` |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` **(edit)** | promote `hall_all` from `private` to public, with a docstring: it is the strong induction and the corollary layer's source | current |

`Capstone.lean` sits beside `Spine.lean`. Keep the conditional surface
(`Inputs`, `functionFieldGeneration_of`) untouched; the unconditional theorem is a
new declaration, and the consumer's example binds to it.

**Why promote `hall_all` rather than inline the corollaries into `Spine.lean`.**
`Spine.lean` is documented as the *conditional* artifact; the corollaries are part
of the unconditional capstone's surface. `hall_all` is FLT's own declaration
(private in the pin's S file), so the checker can verify it through the T14
`S_`-carrier route, like the other promoted pin-private helpers.

## 5. Prerequisites — public, verified

All from the landed topics: `Inputs`, `functionFieldGeneration_of`, `Tight`/`Gen`/
`Hall`, `hall_all` (after §4's promotion) in `Spine.lean`;
`functionFieldGeneration_iff_full_eq` (`Collapse`); `FunctionFieldGeneration`,
`functionFieldGeneration_one` (`Target`); `modularFunctionField_eq_full_of`,
`jqN_div_mem_modularFunctionField` (`Descent`); `relfinrank_full_eq_mul`,
`finrank_adjoin_jqN_prime_of_not_mem` (`DegreeStep`);
`jqN_pow_not_mem_adjoin_full` (`Nonmembership`);
`full_eq_adjoin_full_div_prime` (`Generation`);
`minpoly_jqN_map_eq_prod_slots`, `jqN_prime_not_mem_full` (`SlotProduct`);
`relfinrank_modularFunctionField` (`Defs/Fields`); `phiAtSeed*`
(`Defs/PhiAtSlot`); `jqN_congr` (`Defs/Jq`); `evalAtJGen_injective`,
`ModularPolynomialData.minpoly_jqN_eq` (`ModularPolynomialIrreducible`);
`exists_phiIrreducible_evalSymm` (`ModularPolynomialProperties`). Nothing needed is
`private` after the §4 promotion.

## 6. Verification

1. **`#print axioms`** clean on `functionFieldGeneration`, the three corollaries,
   and the three tail nodes. In particular, on `functionFieldGeneration` the
   output must be only `propext, Classical.choice, Quot.sound`: this is the
   effort's headline check.
2. **Statement checker.** Append to `SOURCES`
   `Theorems/Thm_ModularCurve_functionFieldGeneration.lean`,
   `…_modularFunctionField_eq_full.lean`,
   `…_finrank_adjoin_jqN_eq_dedekindPsi.lean`,
   `…_relfinrank_full_eq_dedekindPsi.lean`, and — if the tail is ported —
   `…_exists_monic_evalAtJ_jqN_eq_zero.lean`,
   `…_exists_phiIrreducible_of_finrank_eq.lean`, `…_exists_phiIrreducible.lean`.
   Report before/after; T19 left it at **297**.
3. **`PORT_FILES`** gains `FunctionFieldGeneration/Capstone.lean`.
4. **The consumer: `sorry` → 0.** Replace line 175's
   `example (N) [NeZero N] : FunctionFieldGeneration N := by sorry` with
   `functionFieldGeneration N`; bind the Zone Q fully-discharged `Inputs` to
   `Capstone.inputs` instead of rebuilding it locally. Record the file's final
   `sorry` count (**0**) and its `0 errors`.
5. **Build.** `lake build` green, 0 warnings, no `sorry`; library-wide `grep`
   for `sorry`.
6. **README** gains the module and the promoted `hall_all`; **`PORTING-FFG.md`
   §7.8** marks T20 done, §2.1/§7.8 record the outbound tier at **100%**, and the
   header status becomes "the effort is complete"; `logs/ffg-port.md` gains T20's
   entry and the effort's closing summary.

## 7. Budget and route risks

Mandatory capstone: the `Inputs` literal (≈25), `functionFieldGeneration` (5), the
three corollaries (≈26), plus `hall_all`'s promotion (visibility only) — **≈60–100
port lines, well under one goal round**. Tail: `exists_monic_evalAtJ_jqN_eq_zero`
≈42, `exists_phiIrreducible_of_finrank_eq` ≈109, `exists_phiIrreducible` ≈6 —
**≈160–180**. Total **≈220–280 port lines**, **one to two goal rounds**. The plan's
`~50 (+250)` row holds.

**Route risks, in the order they will bite.**

- **The `Inputs` literal's `Hall M` fields (pin/T19).** Fields 2 and 4 have type
  `… → Hall M → …`, while the standalone theorems take the pin's explicit
  conjunction. `Hall` is an `abbrev`, so the two are defeq, but a bare field
  assignment can still fail on binder shape. Try
  `jqN_prime_not_mem_full := jqN_prime_not_mem_full` first; if it does not
  elaborate, use `fun M _ p _ hpM hall => jqN_prime_not_mem_full M p hpM hall` (and
  likewise for the minpoly field). This is the topic's only real friction point.
- **`hall_all`'s visibility.** It is `private` in `Spine.lean`; the corollaries
  cannot call it until it is promoted. Promote it in the same commit and check no
  shadowing/duplicate is introduced.
- **`exists_phiIrreducible_of_finrank_eq`'s route.** The pin builds the
  `IsFractionRing (Polynomial ℤ) ℚ⟮jq⟯` structure (109 lines). Before
  transcribing, route-check the short alternative: the port already has
  `evalAtJGen_injective`, `ModularPolynomialData.minpoly_jqN_eq`,
  `phiIrreducible_of_splits` and `exists_phiIrreducible_evalSymm`; a datum from
  `exists_monic_evalAtJ_jqN_eq_zero` plus the degree hypothesis may give
  `PhiIrreducible` in a few lines. Record which route was used; if the short one
  fails, transcribe the pin's and say so.
- **`exists_monic_evalAtJ_jqN_eq_zero`'s prelude.** Its pin file re-copies T14's
  `phiAtSeed*` (40 lines) and `jqN_congr`; import them, do not re-port.
- **Do not touch the conditional surface.** `Inputs` and
  `functionFieldGeneration_of` are frozen; T20 constructs the structure, it does
  not add fields.

## 8. Definition of done (T20)

- [ ] `FunctionFieldGeneration/Capstone.lean` created; `inputs` and public
      `functionFieldGeneration` (statement verbatim from its wrapper);
- [ ] `modularFunctionField_eq_full`, `finrank_adjoin_jqN_eq_dedekindPsi`,
      `relfinrank_full_eq_dedekindPsi` public and statement-verified;
- [ ] the interface tail ported: `exists_monic_evalAtJ_jqN_eq_zero`,
      `exists_phiIrreducible_of_finrank_eq`, `exists_phiIrreducible`;
- [ ] `hall_all` is public and the checker still reports 0 mismatched / 0 missing;
- [ ] `lake build` green, 0 warnings; library-wide `grep` finds no `sorry`;
- [ ] `#print axioms` clean on every new declaration, the headline
      `functionFieldGeneration` included;
- [ ] the consumer's line 175 is the proved theorem and the file carries **0**
      `sorry`s and 0 errors;
- [ ] README, `PORTING-FFG.md` §2.1/§7.8/header and `logs/ffg-port.md` updated,
      with the outbound tier recorded at **100%**;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The headline** — `#print axioms ModularCurve.functionFieldGeneration` and the
   consumer's `sorry` count 0.
2. **The assembly** — did the `Inputs` literal need the `Hall`-binder `fun`
   wrappers? Record which fields.
3. **The routes** — was `exists_phiIrreducible_of_finrank_eq` the short corollary
   or the pin's 109-line fraction-ring construction? Was `hall_all` promoted
   cleanly?
4. **The cost** — rounds, declarations, lines, mandatory vs tail, and the
   corrected T20 figure for §7.8.
5. **The effort close** — the final module count, the measured line total against
   §7.8's ≈4.5k–4.9k estimate, and the friction log's last entries.

## 10. Where this sits

T20 is the end. Its mandatory half makes `ModularCurve.functionFieldGeneration`
unconditional and empties the consumer's `sorry`s; its tail closes §2.1's
out-of-cone ≥5-indegree tier at 100%, so every declaration through which the rest
of FLT reaches this segment — the analytic ones included — is a ported theorem
rather than a reference. The dependency order, the audit outcomes and the effort's
definition of done are [PORTING-FFG.md](../../PORTING-FFG.md) §7.8.
