# SET 6 — the χ₋₃ weight-one Eisenstein series and the Hauptmodul leaves

**Status: done and reviewed (2026-09-24).** Both orders landed and passed
independent verification (full build 4318 jobs, 0 warnings; checker
1275/70/0/0; consumer exit 0; untranscribed heartbeat caps); the review record is
[SET-7.md](SET-7.md) §0. Second coding set of the route-C′ effort. It authorized
**two orders**.
Route plan: [TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md);
mathematics: [../../../math/013-integral-structure-gamma1-basis.md](../../../math/013-integral-structure-gamma1-basis.md);
scout: [../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md).

**Re-cut from SET-5 §8.** SET-5 budgeted `EisensteinChiNegThree` + the whole
`LevelOneHauptmodul` module (≈8,300 `S_` lines) as one set. Both orders of SET-5
took one full run and the two large Hauptmodul packages (1,186 + 858 + 1,317
lines) have not been scouted as portable in one pass, so this set takes the
χ₋₃ theorem **alone** as order 2 and the four *closure-1* Hauptmodul leaves as
order 1. The three big packages are SET 7.

| order | module | declarations | pin `S_` lines | independence |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/LevelOneHauptmodul.lean` | four leaves (table §5.1) | ≈1,094 | each closure 1, no shared premises |
| 2 | `ModularForms/WeightOne/EisensteinChiNegThree.lean` | `EisensteinWeightOne.e1Chi3IsModular` | 3,816 | closure 1 |

Order 1 first: it is light, independent and lands verified work before the big
analytic transcription. Order 2 is the set's headline and the whole route's
riskiest single item.

**Reserved for the manager (do not start):** `WeightOne/IntegralStructure.lean`
(the trace lemma + `hasIntegralStructure_of_two_le`/`_two`) and every later set.
If an order needs a later-module declaration, prove a local `private` helper and
record it; do not open a new module.

## 0. SET-5 review (verified by the manager)

- `WeightOne/Basic.lean` (1,863 lines, 7 headlines) and
  `WeightOne/EisensteinSeries.lean` (798 lines, `eisensteinG` + 2 headlines):
  both green, statements identical to their wrappers, all `S_` helpers `private`.
- Independent re-run: full `lake build` **4130 jobs, exit 0, 0 warnings**;
  checker **1270 identical / 70 promoted / 0 mismatched / 0 missing / 14 own
  (1284 checked)**; `spec/WeightOneConsumer.lean` exit 0.
- One bookkeeping note: the 70th "promoted" is
  `CuspForm.finiteDimensional_of_isArithmetic`, matching the pin's dotted copy
  because its last name collides with `ModularForm.finiteDimensional_of_isArithmetic`
  in `SOURCES`. Statement verified; no action.
- The `lake env lean` probe at the **default** 200 000 cap times out on
  `Basic.lean`'s `IsIntAuxT.mem_span_RSet_of_adjoin_simple_transcendental`
  (82 s user CPU) while `lake build` under the project's global 4 000 000 is
  green. That is the probe cap, not a blow-up; see §2.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3` at
  `~/proj/fermats-last-theorem`. Read it; never modify it.
- Statement = `Theorems/Thm_<dotted, `.` → `_`>.lean`; proof =
  `P2M/Sol/S_<same>.lean`. **The wrapper is the statement authority.**
- v4.34 drift: [porting-playbook.md](../../porting-playbook.md) §4, the SET-5
  report (`if_neg`→`ite_eq_right`, `dif_*`→`dite_eq_*`, `Set.mem_setOf_eq`→
  `Set.mem_ofPred_eq`, `coe_*` aliases, instance-search walls from broader
  imports). Adapt proofs, never statements.

## 2. Build discipline — read and obey first

Measured for this tree: `lake env lean` on a 200–350-line green module ≈ 4 s;
`lake build <module>` deps-cached ≈ 2–5 s; full `lake build` under a minute; a
heartbeat stall errors in ~15–20 s.

- **Fixed bounds, never raised, never bypassed:**
  `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`,
  `timeout 240 lake build`.
  The per-module bound is 180 s (not 90) because order 2 is a 3,816-line analytic
  module; it is still fixed, and a non-return at 180 s is a blow-up, not patience.
  Do not bump it, do not add `-K`, do not raise `maxHeartbeats`/`maxRecDepth`
  (project cap 4 000 000).
- **Important, learned in SET-5.** `lake env lean <file>` runs at the *default*
  200 000-heartbeat cap and can report a `whnf` timeout on a heavy proof that
  `lake build` compiles green under the project's 4 000 000. The acceptance gate
  is `lake build`, the checker and the consumer — not the bare probe. Do **not**
  read this as licence to raise anything: if `lake build <module>` itself hits
  180 s, or the full build 240 s, quarantine and bisect.
- **On a timeout:** comment out/bisect, or reproduce in the gitignored
  `Scratch*.lean` with `set_option diagnostics true` and a low cap. Report the
  declaration and stop if it is load-bearing.
- **Check CPU when in doubt:** `/usr/bin/time -v`. High user CPU + timeout = real
  blow-up (bisect); near-zero user CPU + wall stall = lock contention (re-run
  when idle, do not bisect). Build serially.
- **Likely stall points:** order 2's weight-one modularity proof (hexagonal/
  theta sums, `tsum` manipulations) and order 1's `tprod`/`Periodic` width
  normalisations. State over concrete function types; keep the pin's `private`
  helpers `private`.

## 3. Shared conventions

1. Statements **verbatim** from the wrappers, binders included.
2. Specific imports; no `import Mathlib` in a port module.
3. Only the headlines are public; pin-private helpers stay `private`.
4. Checker: append each order's wrappers to `SOURCES` and the two modules to
   `PORT_FILES` in `spec/check_flt_statements.py` (order 2 imports the already-
   registered definition module `Definitions/Def_ModularForm_EisensteinChiNegThree.lean`;
   verify the name and register it if absent). Target **0 mismatched, 0 missing**.
5. **No commits.** The working tree is the hand-off. Never touch the pin.
6. Do not touch the FFG modules, the Sturm modules (import only), or the capstone.
7. `README.md` gains both rows; `SET`/`TOPIC`/log files are the manager's.

## 4. Definition of done (per module)

- Module at the named path; headlines verbatim; specific imports.
- `timeout 180 lake build <module>` green, 0 warnings, no `sorry`/`admit`.
- `#print axioms` on the order's headlines clean.
- Checker **0 mismatched, 0 missing**.
- `README.md` row added.
- No statement weakened; if one cannot match its wrapper, quote both and stop.

## 5. The orders

### 5.1 — order 1: `FLTForHuman/ModularForms/WeightOne/LevelOneHauptmodul.lean`

Four independent closure-1 leaves; each statement verbatim from its wrapper.

| declaration | `S_` file (lines) | role |
|---|---|---|
| `ModularCurve.surjective_specialLinearGroup_map_zmod` | `S_ModularCurve_surjective_specialLinearGroup_map_zmod.lean` (159) | reduction `SL(2,ℤ) → SL(2, ℤ/N)` is onto |
| `ModularCurve.qExpansion_discriminant_eq_X_mul_tprod` | `…_qExpansion_discriminant_eq_X_mul_tprod.lean` (199) | $`q`$-expansion of $`\Delta`$ as $`q\prod(1-q^{n+1})^{24}`$ |
| `WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le` | `…_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean` (421) | vanishing at cusps ≺ width-`N` coefficient bound |
| `WLight.linearIndependent_complex_of_qExpansion_rational` | `…_linearIndependent_complex_of_qExpansion_rational.lean` (315) | rational $`q`$-coefficients are faithful |

### 5.2 — order 2: `FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean`

| declaration | `S_` file (lines) | role |
|---|---|---|
| `EisensteinWeightOne.e1Chi3IsModular : EisensteinWeightOne.E1Chi3IsModular` | `S_EisensteinWeightOne_e1Chi3IsModular.lean` (3,816) | weight-one Eisenstein series $`E_1(1,\chi_{-3})`$ is modular |

It imports the port's `Defs/EisensteinChiNegThree.lean` (the `Prop` interface
`E1Chi3IsModular`); do not re-define it. This is a single long analytic proof:
transcribe in one module, keep every helper `private` as in the pin, and if it
cannot be completed, report the exact last declaration landed — **no `sorry`, no
placeholder, no partial public declaration**.

Do **not** port the three big Hauptmodul packages
(`levelOne_hauptmodul_package`, `weierstrassP_qExpansion_package`,
`weierstrassP_torsion_qExpansion_package`); they are SET 7.

## 6. Consumer / wire test

Extend `spec/WeightOneConsumer.lean` (SET-5's file) with `#check`s of the five
order-1/2 headlines and **one executed application per order** (order 1: e.g. the
discriminant $`q`$-expansion identity applied to the `tprod`; order 2: the
`E1Chi3IsModular` conclusion consumed as a `Prop`). `timeout 120 lake env lean
spec/WeightOneConsumer.lean` must exit 0 with no warnings. If an honest
application is impossible, say so rather than faking one.

## 7. What to report back

1. Per-order table: module, lines, declarations, `lake build <module>` time,
   checker before/after.
2. Any wrapper statement that did not match, quoted rather than weakened.
3. v4.34 drifts actually hit, per declaration.
4. Any `private` helper promoted, any later-module helper needed locally.
5. For order 2: the declaration count and where the file's proof mass sat; if not
   finished, the exact stopping point.
6. Any build that hit its bound: declaration, CPU reading, outcome — before
   moving on.
7. Confirmation the capstone, the three big Hauptmodul packages, the FFG modules
   and the pin are untouched.

## 8. Later sets (manager's view; not authorized)

| set | orders |
|---|---|
| 7 | the three big `LevelOneHauptmodul` packages (≈3,361) |
| 8 | `FrickePackage` (≈7,500, likely two orders) |
| 9 | `Gamma0Rationality` (≈5,000) |
| 10 | `Gamma1Basis` (≈4,900) |
| capstone (**manager**) | `IntegralStructure` (trace lemma + corollaries) |
