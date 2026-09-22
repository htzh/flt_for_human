# Topic 15: descent by one prime, and the one-prime reduction

**Status: done (2026-09-22) — one goal round.** `FunctionFieldGeneration/Descent.lean`
is **252 lines** against the 173-line pin tail (ratio ≈1.46), inside the scouted
~200–280 band. Both declarations are public, statements the `Theorems/` wrappers'
verbatim, `#print axioms` clean, `lake build` green with 0 warnings and no `sorry`.
The checker moved **276 → 278** (0 mismatched, 0 missing). The two `Inputs` fields
are discharged, so the capstone's debt is **7 → 5**, and the consumer's Zone M wire
test builds a partially discharged `Inputs` with them filled. All four route risks
resolved on the first build: the `Algebra`/`ι₀`/`hcomp` machinery closed by `rfl`
with no `respectTransparency` and no named bridge, and
`isRoot_prime_at_slot_iff` / `mem_range_of_unique_common_root` fired at the pin's
call shape. The only friction was the `linter.style.haveILetI` pair on two
genuinely-needed local instances (same module-level disable as `PhiGenSplits.lean`).
The dedup premise held: the two `S_` files are one development, and none of the
~542 prelude lines was re-copied. See [logs/ffg-port.md](../../logs/ffg-port.md)
§2h for the measured cost and route results. T14 is done and committed (`52a4afd`),
so the pin's shared slot prelude is public (`Defs/PhiAtSlot.lean`,
`ModularCurve/PhiSlotRoots.lean`, `Defs/TS.lean`), and every Φ_p input this topic
consumes is a ported theorem (T12's `exists_phiIrreducible_evalSymm`, T13's
`splits_prime_at_slot`, T4's `Polynomial.mem_range_of_unique_common_root`).

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

**Audience.** A fresh session taking T15 of the `functionFieldGeneration` effort.
Read, in this order:

1. [PORTING-FFG.md](../../PORTING-FFG.md) §7.8 (the frontier and the topic order)
   and §1 (the design rules);
2. [math/010](../../../math/010-function-field-generation.md) §4 and §5 — the
   unique-common-root descent and the divisor-lattice collapse; this topic is
   those two sections;
3. [TOPIC-slot-machinery.md](TOPIC-slot-machinery.md) (T14, the immediate
   predecessor) and [logs/ffg-port.md](../../logs/ffg-port.md) §2g;
4. [studies/flt-ffg-field-theory.md](../../../studies/flt-ffg-field-theory.md)
   §2 (Tiers 0–1) and §5;
5. [porting-playbook.md](../../porting-playbook.md) §3.9, §3.11 and §7.3
   ("cost tracks the route, not the subtree").

## 1. Goal, and why this topic

**Goal.** Port the pair of theorems that turn the slot description into the
field-theoretic step:

1. **`jqN_div_mem_modularFunctionField`** — descent by one prime:
   `` $`j(q^M) \in \mathbb{Q}(j(q), j(q^{Mp}))`$ `` — proved by the
   unique-common-root principle applied to the two polynomials of math/010 §4;
2. **`modularFunctionField_eq_full_of`** — the one-prime reduction of the `Gen`
   invariant: `Gen N` follows from the one-prime step `jqN M ∈ F_N` and `Gen M`
   for every factorization `N = M · p`.

Both are `Inputs` fields of `Spine.lean`, so proving them shrinks the conditional
capstone's debt **7 → 5**.

**Why now.** T15 is the first consumer of T14's prelude and the first topic that
produces a field-theoretic `Inputs` field. Its two statements are also the ones
`Spine`'s private `htw_of`/`hsp_of`/`root_shape` were written to feed: the descent
takes the slot hypotheses `htw`/`hsp` as **arguments**, exactly as the pin's node
does, and T19's slot product is what later discharges them. So T15 composes with
T14 and T19 without changing the `Inputs` statements.

**Settled: the `735`-line file is one development, and most of it is already
ported.** `S_ModularCurve_jqN_div_mem_modularFunctionField.lean` and
`S_ModularCurve_modularFunctionField_eq_full_of.lean` are byte-identical except
their exported `solution` line: one development, shipped twice. Its **lines
28–542 are the T14 prelude** (`TS`, `qTwistEquiv`, `phiProd_conj_eq`,
`roots_prime_at_slot*`, `phiAtSeed*`, …), already written once by T14. T15's own
content is only the tail — §2 measures it at ~173 lines, not 325, and far below
the §7.8 row's `~350`, which was priced from the file size before T14 landed.

**Settled: the two ports are the pin's statements, verbatim.** Both nodes have
`Theorems/` wrappers, so `spec/check_flt_statements.py` verifies them by direct
name match rather than exempting them, even though the pin keeps them `private`
in the `S_` file and exports them through `solution`.

**Not in this topic.** `jqN_mem_of_div_primes` (math/010 §5's "two primes beat
one") is **not** here despite the note's prose placing it near this file: it lives
in T18's `S_ModularCurve_full_eq_adjoin_full_div_prime.lean`/`…_adjoin_primes.lean`
(pin line 397) and is T18's to port.

## 2. The scouted inventory

Source pin: `P2M/Sol/S_ModularCurve_modularFunctionField_eq_full_of.lean` (735
lines; `S_ModularCurve_jqN_div_mem_modularFunctionField.lean` is the same file).
The prelude is lines 28–542 (then namespace plumbing through 551); the two nodes are:

| declaration | pin lines | size | content |
|---|---|---|---|
| `ModularCurve.jqN_div_mem_modularFunctionField` | 553–691 | 139 | the unique-common-root descent |
| `ModularCurve.modularFunctionField_eq_full_of` | 694–727 | 34 | the divisor-lattice one-prime reduction |

The statements, from the `Theorems/` wrappers, verbatim:

```lean
theorem ModularCurve.jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (htw : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)))) = 0 → ∀ w : Kˣ, y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq)) → w = 1)
    (hsp : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)))) = 0 → y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))) :
    jqN M ∈ modularFunctionField (M * p)

theorem ModularCurve.modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N → jqN M ∈ modularFunctionField N)
    (hgen' : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N → modularFunctionField M = modularFunctionFieldFull M) :
    modularFunctionField N = modularFunctionFieldFull N
```

### 2.1 The proof's shape (so the port is a transcription, not a redesign)

`jqN_div_mem_modularFunctionField` (math/010 §4) sets
`` $`F = \mathbb{Q}(j(q), j(q^{Mp}))`$ ``, `A = phiAtSeed data ⟨jqN (M*p)⟩` (the
level-`p` polynomial evaluated at the level-`Mp` nome), and `B =` the
`minpoly`-of-`jqN M` mapped into `F`; then applies
`Polynomial.mem_range_of_unique_common_root` with
`x₀ = coeffEmb K (qExpand ℚ (M*p) (jqN M))`. The two hypotheses `htw`/`hsp`
supplied by the caller rule out every other common root. The tail strips the
coefficient extension with `coeffMap_injective` composed with
`qExpand_injective`:

```lean
have hrange := Polynomial.mem_range_of_unique_common_root A B hA0 hAs hAnd x₀ hxA hxB huniq
obtain ⟨f, hf⟩ := RingHom.mem_range.mp hrange
...
have hval : (f : LaurentSeries ℚ) = jqN M := qExpand_injective (M * p) (hemb hf')
```

`modularFunctionField_eq_full_of` (math/010 §5) is 34 lines of `adjoin_le_iff` and
`Nat.minFac` arithmetic with no analytic content.

## 3. The mathlib-first audit

Audited against `v4.34.0`. **Every mathematical ingredient is already a ported
theorem or a mathlib call** — this topic adds no mathlib-absent lemma.

| pin piece | where it comes from | verdict |
|---|---|---|
| `Polynomial.mem_range_of_unique_common_root` (the engine) | `FLTForHuman/FieldTheory/CommonRoot.lean` (T4) | **import; do not re-derive** |
| `exists_phiIrreducible_evalSymm` (the datum) | `ModularPolynomialProperties.lean` (T12) | import |
| `splits_prime_at_slot` (`hAs`) | `PhiGenSplits.lean` (T13) | import |
| `isRoot_prime_at_slot_iff`, `roots_prime_at_slot_roots_nodup` (`hrootA`, `hAnd`) | `PhiSlotRoots.lean` (T14) | import |
| `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic` | `Defs/PhiAtSlot.lean` (T14) | import |
| `iota_jqN`, `TS_congr` (`hseed`/`hdist`/`hspread`) | `Defs/TS.lean` (T14 promotion) | import |
| `coeffMap_injective`, `qExpand_injective`, `coeffEmb` (the strip) | `Defs/Laurent.lean` | import |
| `adjoin_jq_le`, `jqd_mem_full`, `modularFunctionField_le_full` | `Defs/Fields.lean` | import |
| `Polynomial.aeval`/`aeval_def`/`eval_map`/`eval₂_hom`/`eval₂_eq_eval_map`, `Polynomial.map_map`, `minpoly.aeval` | mathlib | call |
| `IntermediateField.subset_adjoin`, `adjoin_le_iff` | mathlib | call |
| `IsPrimitiveRoot.pow_eq_one_iff_dvd`, `Nat.minFac_prime`, `Nat.minFac_dvd`, `Nat.mul_dvd_mul_iff_left` | mathlib | call |

**Headline.** This is a *consumer* topic. The audit's only positive results are
the two imports that replace the pin's own engines T4 and T12 built; there is
nothing to hunt in mathlib and nothing to re-prove.

## 4. Module split

One new module, because the pin ships one development:

| module | public surface | pin |
|---|---|---|
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean` | `ModularCurve.jqN_div_mem_modularFunctionField`, `ModularCurve.modularFunctionField_eq_full_of` | `S_…_modularFunctionField_eq_full_of.lean` 553–727 |

It sits in the theory directory beside `Target.lean`, `Collapse.lean` and
`Spine.lean` (path `...ModularCurve.FunctionFieldGeneration.Descent`, namespace
`ModularCurve`). Do **not** call it `Collapse`: `FunctionFieldGeneration/Collapse.lean`
already holds `functionFieldGeneration_iff_full_eq`, a different reduction. If the
two proofs read better apart, `Descent.lean` + `GenReduction.lean` is acceptable;
one declaration must have one home either way.

## 5. Prerequisites — all public, verified

`phiAtSeed`/`phiAtSeed_map`/`phiAtSeed_monic` (`Defs/PhiAtSlot.lean`);
`isRoot_prime_at_slot_iff`/`roots_prime_at_slot_roots_nodup` (`PhiSlotRoots.lean`);
`iota_jqN`/`TS_congr` (`Defs/TS.lean`); `splits_prime_at_slot` (`PhiGenSplits.lean`);
`exists_phiIrreducible_evalSymm` (`ModularPolynomialProperties.lean`);
`Polynomial.mem_range_of_unique_common_root` (`FieldTheory/CommonRoot.lean`);
`qExpand_injective`/`coeffMap_injective` (`Defs/Laurent.lean`);
`adjoin_jq_le`/`jqd_mem_full`/`modularFunctionField_le_full` (`Defs/Fields.lean`).
No prerequisite is `private`; T15 adds no promotion and imports nothing from the
cone that T14 did not already make public.

## 6. Verification

1. **`#print axioms`** clean on both public declarations (only `propext`,
   `Classical.choice`, `Quot.sound`).
2. **Statement checker.** Add both `Them_` wrappers to `SOURCES`:
   `Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean` and
   `Theorems/Thm_ModularCurve_modularFunctionField_eq_full_of.lean`. Both are
   public wrappers with matching last names, so they verify by direct match; no
   `S_` carrier is needed. Report the before/after count (T14 left it at **276**).
3. **`PORT_FILES`** gains `FunctionFieldGeneration/Descent.lean`.
4. **The wire test — Zone M.** T14 took Zone L; this takes the next free zone in
   `spec/ModularCurveConsumer.lean`. The meaningful test is the one T20 will
   perform: show that **T15's two theorems fill their `Inputs` fields**, i.e.
   that a (partially discharged) `Inputs` value can be built with
   `jqN_div_mem_modularFunctionField := ModularCurve.jqN_div_mem_modularFunctionField`
   and
   `modularFunctionField_eq_full_of := ModularCurve.modularFunctionField_eq_full_of`.
   That is a cross-module composition (imports `Spine.lean` plus the new module)
   and it is exactly the debt being paid — not a statement binding.
5. **Build.** `lake build` green, 0 warnings, no `sorry`; the library-wide
   `grep -rn 'sorry' FLTForHuman/ModularCurve/` check.
6. **README** gains the module row; **`PORTING-FFG.md` §7.8** marks T15 done and
   records the measured cost against the corrected ~173-line tail; the log
   `logs/ffg-port.md` gains T15's entry.

## 7. Budget and route risks

Pin content is **~173 proof lines** (139 + 34) plus the two statements. At the
sub-effort's measured ratios expect **~200–280 port lines** and **one goal
round**; two if the instance machinery below fights. This is well under §7.8's
`~350` row, which priced the whole 735-line file before T14 removed its prelude.

**Route risks, in the order they will bite.**

- **The `Algebra F (LaurentSeries K)` instance and the `ι₀` bridge.** The pin
  installs `letI : Algebra F (LaurentSeries K) := (((coeffEmb K).comp (qExpand ℚ (M*p))).comp (algebraMap F _)).toAlgebra`
  and proves `hcomp : (algebraMap F _).comp ι₀ = ...` by `RingHom.ext fun x => rfl`.
  That is the transparency family that bit T8 (`mapGL`) and T5 (`FunLike`). Port
  it directly; if the `rfl` stops closing, add
  `set_option backward.isDefEq.respectTransparency.types false` locally (T8's
  precedent) or state `hcomp` as a named `private` monomorphic bridge — do not
  re-architect the proof.
- **`isRoot_prime_at_slot_iff`'s call shape.** The proof rewrites with
  `isRoot_prime_at_slot_iff (M*p) ζ hζ p hpN data (M*p*M) 1 y` at pin 622. T14
  wrote that statement verbatim; if the `rw`/`exact` does not fire, the defect is
  in the T14 statement and belongs fixed there, not worked around here.
- **`Polynomial.mem_range_of_unique_common_root`'s signature.** The port's
  `CommonRoot.lean` statement is verbatim from the pin wrapper, but the pin's call
  at line 682 passes `A B hA0 hAs hAnd x₀ hxA hxB huniq`; check the argument
  order matches before assuming.
- **The `minpoly`/`map` strip at pin 651–659.** `Polynomial.aeval_def`,
  `← Polynomial.eval_map`, `Polynomial.map_map`, `Polynomial.eval₂_eq_eval_map`
  and `minpoly.aeval` are re-ordered twice; transcribe them rather than inventing
  a shorter route on the first attempt.
- **`Fact (Nat.Prime p)` vs `p.Prime`.** The descent wrapper uses `[Fact]`, the
  reduction uses a bare `p.Prime` hypothesis; keep each statement's spelling so
  the checker matches.

## 8. Definition of done (T15)

- [ ] `FunctionFieldGeneration/Descent.lean` created: both declarations public,
      statements verbatim from the wrappers;
- [ ] `lake build` green, 0 warnings, no `sorry`;
- [ ] `#print axioms` clean on both;
- [ ] the two wrappers in `SOURCES`, 0 mismatched, 0 missing; `PORT_FILES` updated;
- [ ] Zone M recorded and green, with the `Inputs`-field composition as its wire
      test;
- [ ] README module table, `PORTING-FFG.md` §7.8 and `logs/ffg-port.md` updated;
- [ ] report in the §9 shape.

## 9. Reporting back

1. **The debt** — confirm the two `Inputs` fields are discharged (7 → 5) and that
   the structure's statements were not touched.
2. **The route** — did the `Algebra`/`ι₀`/`hcomp` machinery close as transcribed,
   or was `respectTransparency` / a named bridge needed? Which?
3. **The cost** — rounds, declarations, lines, ratio against ~173, and the
   corrected T15 figure for §7.8.
4. **The dedup** — confirm the twin-file premise (one development, prelude already
   written by T14) held and that no prelude was re-copied.
5. **The split** — did one `Descent.lean` hold?

## 10. Where this sits

T15 is the first parent topic whose output is proof content rather than
vocabulary: with it, the capstone's debt is five fields. It composes with T14
(which supplies the slot prelude) and T19 (which discharges `htw`/`hsp` through
the slot product). T16 (the degree step), T17 (non-membership), T18 (generation)
and T19 (the slot product) follow; the dependency order and the frontier are
[PORTING-FFG.md](../../PORTING-FFG.md) §7.8.
