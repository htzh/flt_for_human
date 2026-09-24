# SET 2 — the bifibre count, the local exchange and the principal-divisors route (T5, T6, T8, T9)

**Status (2026-09-23): work orders written, not started.** This is the run brief for
the **second** coding set of [PORTING-AC.md](../PORTING-AC.md), written *after*
reviewing SET 1 and against what SET 1 actually produced. It authorizes exactly four
topics:

| order | work order | object | pin nodes | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-t5-bifibre.md](TOPIC-t5-bifibre.md) | the generic orbit/index engine + the bifibre count | 5 | 560–650 | SET 1 (T2, T3, T4) |
| 2 | [TOPIC-t6-local-exchange.md](TOPIC-t6-local-exchange.md) | the local exchange + the normal closure | 1 | 230–270 | T5 |
| 3 | [TOPIC-t8-ratfunc-degree.md](TOPIC-t8-ratfunc-degree.md) | the `P¹` places and degree | 11 | 560–680 | SET 1 (AC0, T1) |
| 4 | [TOPIC-t9-transcendence.md](TOPIC-t9-transcendence.md) | `HasPrincipalDivisors` via transcendence | 2 | 450–540 | T8, T2 |

**T7 (the divisor exchange) is the human capstone and is not in this set.** Do not
write `WeilExchange/DivisorExchange.lean`; T5/T6 must expose what it needs
(`sum_ramificationIndex_mul_inertiaDeg_exchange`, `restrict_restrict`, the
`fiberAlong` API) and leave the theorem to the reviewer.

**Do T5 first, and scout before committing.** T5 is the one genuinely new proof in
the whole effort (two lemmas mathlib does not state, and a place-theoretic
orbit-stabiliser count); SET 1's four topics were all transcription. The T5 work
order therefore opens with a **route scout**: before porting, prototype the
generic orbit-intersection count in the gitignored `Scratch.lean` and confirm the
two statements are provable from mathlib's orbit–stabiliser ingredients. If the
scout resists, **stop after writing the scout findings into `logs/ac-port.md`,
report, and wait for the manager to re-task you** (the reviewer may move T8/T9
ahead of T5). Do not burn the run on a stuck proof.

## 0. What SET 1 handed over (verified 2026-09-23)

SET 1 is green: 12 modules, `lake build` 4,022 jobs / **0 warnings / no `sorry`**,
checker **586 identical, 0 mismatched, 0 missing**, consumer **0 errors**,
`#print axioms` clean, no commits. The exact surface SET 2 builds on:

- **`Defs/PushPull.lean`** — `Place.{restrict, ramificationIndex, inertiaDeg,
  restrictInclusion, restrictResidueMap, fiber}`, `Divisor.{pushforward, pullback,
  pullback_apply, pushforward_apply, PushforwardNormFormula, FundamentalIdentity}`,
  `SumRamificationInertia`, the `Pic0` homs, and the ord leaves.
- **`Defs/PlacesOverDVR.lean`** — `Place.{center, centerHeightOneSpectrum,
  integralClosureAt, fiberCenter, mem_fiberCenter_iff_ord_pos, placeOfPrime,
  fiberEquiv, fiberOver, mem_fiberOver, restrict_eq_of_mem_fiberOver,
  subset_fiberOver_of_forall_restrict_eq, finite_setOf_restrict_eq,
  maximalIdeal_ne_bot, algebraMap_integralClosureAt_injective}`.
  `Place.card_fiberOver_eq` and `Place.fiber_eq_fiberOver` were **not** written
  (deferred; `grep -c 0`); T5 re-adds the first only if its proof needs it.
- **`Defs/PlaceDictionary.lean`** — the fibre dictionary, 16 declarations public at
  the pinned names under `AlgebraicCurve.Place` (`eq_ord_of_addHom_of_nonneg_iff`
  is `private`), including `ramificationIndex_eq_ramificationIdx_fiberCenter`,
  `inertiaDeg_eq_inertiaDeg_fiberCenter`, `le_ord_iff_mem_pow_fiberCenter`,
  `neg_log_valuation_fiberCenter_eq_ord`. The statements carry the pin's primed
  `Ideal` text; the module has `set_option linter.deprecated false`.
- **`WeilExchange/FiberOverCount.lean`** — `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`,
  `…_le_finrank`, `Place.inertiaDeg_pos`.
- **`WeilExchange/GaloisRamification.lean`** — `Place.exists_algEquiv_smul_eq_of_restrict_eq`,
  `Place.restrict_ofAlgAut_smul`, `Place.ramificationIndex_eq_of_restrict_eq`,
  `Place.inertiaDeg_eq_of_restrict_eq`, `SemilinearAut.{ramificationIndex_smul,
  inertiaDeg_smul, ord_algebraMap_smul}`.
- **`WeilExchange/Transport.lean`** — the 16 along/`Pic0` nodes **plus the shared
  prelude written once**, public in `AlgebraicCurve.BifibreDev`:
  `inertiaDegAlong_congr`, `isIntegral_toAlgHom`, `toAlgHom_comp_toAlgHom`,
  `restrict_restrict`; and in `AlgebraicCurve.Place`:
  `ramificationIndex_eq_mul_ramificationIndex_restrict`,
  `inertiaDeg_eq_mul_inertiaDeg_restrict`. **T5/T6 must import these, never
  restate them** — that is the point of T4 and the pin's three `BifibreDev`/
  `BifibreW2`/`BifibreWEX` copies are not to be reproduced.
- **`Defs/IntegralAdjoin.lean`** — the three generic `isIntegral_adjoin_*`
  transport facts (T9 uses them).
- **`Defs/RatFuncPlaces.lean`** — the `P¹` vocabulary T8 builds on:
  `Place.{adicValuation_valuationSubring, mem_iff_adicValuation_le_one,
  isEquiv_adicValuation_ofHeightOneSpectrum, ord_ofHeightOneSpectrum_ne_zero_iff,
  ofHeightOneSpectrum_injective}`, `RationalFunctionField.{nontrivial_valueGroup_inftyValuation,
  placeInfty, placeInfty_toValuationSubring, heightOneSpectrumOfIrreducible,
  heightOneSpectrumOfIrreducible_asIdeal, exists_irreducible_span, finitePlace,
  algebraMap_mem_ofHeightOneSpectrum, residueOfHeightOneSpectrum + _apply/ker_/surjective_,
  residueFieldEquivOfHeightOneSpectrum, deg_ofHeightOneSpectrum, deg_finitePlace}`.
- **`Defs/Correspondence.lean`** — `algebraAlong` (an `abbrev`), `FiniteAlong`,
  `SeparableAlong`, `finrankAlong`, `Place.{restrictAlong, ramificationIndexAlong,
  inertiaDegAlong}`, `fiberAlong`, `mem_fiberAlong`, `Divisor.pullbackAlong_apply`,
  `pushforwardAlong_single`, `Divisor.pullbackAlong_single`.
- **`Defs/SemilinearAut.lean`** and **`Defs/Divisor.lean`** as AC0 left them.

## 1. Shared conventions

1. **Build discipline.** Re-read [SET-1.md](SET-1.md) §2 verbatim: every build
   under `timeout 60 lake env lean <file>` / `timeout 120 lake build <module>`;
   non-return at 60 s is a blow-up to bisect; **never add or raise
   `maxHeartbeats`** (the lakefile's global 4,000,000 makes the `timeout` the only
   real guard); never `import Mathlib`; keep the pin's `letI`/`haveI` walls,
   `abbrev`s and `@[reducible]` attributes literal; `lake/env lean` on a fresh
   module needs `lake build <module>` first (the deps' oleans).
2. **Statements come from the `Theorems/` wrappers, binders included.** SET 1 found
   two work orders where the `S_`-file binders differed from the wrapper's
   (`SemilinearAut.ramificationIndex_smul` has no `IsScalarTower`/`IsIntegral`;
   `Divisor.pullbackAlong_pullbackAlong` puts its `HasPrincipalDivisors` after
   `χ`). When the two disagree, the wrapper wins and the divergence goes in the log.
3. **The checker.** Append each topic's AC wrappers to `SOURCES`; append the pin
   `S_` file when a declaration has no wrapper (that is how SET 1 verifies the
   promoted dictionary and the T4 prelude: last-name match). `OWN_PROOFS` is for
   port-authored declarations only, each with a reason. Target: `0 mismatched,
   0 missing`.
4. **Consumer zones.** SET 1 used A (`vocab`), B (`interface`), C (`dictionary`),
   D (`galois`), E (`transport`). SET 2 continues with **F `[bifibre]`** (T5),
   **G `[exchange]`** (T6), **H `[principal]`** (T8), **I `[transcendence]`**
   (T9); the human's T7 closes the exchange zone. Zones must contain a real
   (non-`sorry`) composition, not only `#check`s.
5. **`logs/ac-port.md`** is extended per topic in SET 1's format (cost table,
   per-module table, drop counts, friction log). `README.md`'s module table is
   extended; `PORTING-AC.md` is the manager's and is not edited.
6. **No commits.** The working tree is the hand-off.

## 2. Definition of done (per topic)

- Modules as named in the work order, statements verbatim from the wrappers,
  mathlib-only imports, namespace `AlgebraicCurve`.
- `timeout 90 lake build` green, **0 warnings**, no `sorry`.
- The topic's consumer zone at 0 errors with a real wire test.
- `spec/check_flt_statements.py`: the topic's sources appended; **0 mismatched,
  0 missing**.
- `#print axioms` on the topic's headlines clean.
- `logs/ac-port.md` section + friction log; `README.md` table row(s).

## 3. What to report back

1. The per-topic table (modules, lines, decls, build, consumer zone errors,
   cumulative checker line).
2. **The T5 scout outcome**: whether the two generic statements were provable from
   mathlib's orbit–stabiliser API, and what the proof cost — this is the effort's
   headline measurement.
3. Which named shape risks materialized (T5's orbit count/index product and the
   `resHom` packaging; T6's normal-closure instance block; T8's Ostrowski shape and
   `DecidableEq (RatFunc K)`; T9's `relNorm`/`normalizedFactors` block and
   `PerfectField` firing) — and which did not.
4. Any statement that would not match its wrapper, quoted rather than weakened.
5. The measured cost against [PORTING-AC.md](../PORTING-AC.md) §4.3's budget,
   and the SET-2 hand-off to the human's T7: exactly what `Bifibre.lean` and
   `LocalExchange.lean` expose.
