# The `localParam` family — the other two leaves and their four premises

The `localParam` subject of the D-S cone is **complete**. LP1
([localParam-finite-cover.md](localParam-finite-cover.md)) landed the finite cover and
its engine; this record covers the other two leaves of the family and the four premise
leaves the third one needed: **six new modules, 2,653 lines, 167 statement-checked
declarations, five headlines**, all under the new per-module checker
(`spec-pin:` wires, no `PORT_FILES`/`SOURCES` entry anywhere). The family's seven
modules together with LP1's two:

| set | module | lines | public | `check_port` |
|---|---|---:|---:|---|
| LP2 | `AlgebraicCurve/Place/BranchUniqueness.lean` | 370 | 37 | 37 ok |
| LP3a | `AlgebraicCurve/Place/LaurentSeriesModel.lean` | 544 | 1 | 1 ok |
| LP3a | `AlgebraicCurve/Place/TranscendentalOfOrdNeZero.lean` | 75 | 2 | 2 ok |
| LP3a | `AlgebraicCurve/IsCurveOver/FinitenessTransfer.lean` | 122 | 3 | 3 ok |
| LP3b | `Analysis/PowerSeries/EisensteinAlgSeries.lean` | 491 | 24 | 24 ok |
| LP4 | `AlgebraicCurve/Place/MeroRealize.lean` | 639 | 60 | 60 ok |
| LP4 | `AlgebraicCurve/Place/LocalParamDatum.lean` | 480 | 40 | 40 ok |

The orders: [WORKORDER-LP2](../topics/algebraicCurve/WORKORDER-LP2-branch-uniqueness.md),
[LP3a](../topics/algebraicCurve/WORKORDER-LP3a-laurent-and-generator-transfers.md),
[LP3b](../topics/algebraicCurve/WORKORDER-LP3b-power-series-growth.md),
[LP4](../topics/algebraicCurve/WORKORDER-LP4-meromorphic-order-dictionary.md); the
subject's topic is
[TOPIC-localParam-finite-cover.md](../topics/algebraicCurve/TOPIC-localParam-finite-cover.md).

## 1. Measured, on the tree this record leaves

```bash
cd lean
python3 spec/check_port.py --changed
# 206 ok, 0 mismatch, 0 missing, 0 own — 10 module(s), 617 exempt (PORT_FILES); corpus aa2d8b3
timeout 280 python3 spec/old_check_stmts.py | tail -1
# 10473 identical (774 promoted, 83 renamed), 0 mismatched, 0 missing, 42 own (10809 checked)
python3 spec/unwired_register.py --check          # register is current
python3 tools/deps/frontier.py --ds --top 0
# needed 1,373 → 1,368 nodes; F inside the cone 717 → 722
```

* Tier-1 builds, one module at a time under `flock`: LP2 3,291 jobs; LP3a
  2,552 / 2,686 / 2,024; LP3b 3,097; LP4 3,681 — **0 warnings** throughout, and the
  edit loop prints nothing at `-DmaxHeartbeats=200000`.
* `#print axioms` on all five headlines (and on `Fam.fibre`, `SL_mul`,
  `Datum.ord_place`, `Datum.place`): `[propext, Classical.choice, Quot.sound]`.
* Grep sweep of the seven modules: no `sorry`/`admit`/`axiom`/`native_decide`, no bare
  `import Mathlib`, no `maxHeartbeats`. Suppressions are four narrow
  `set_option linter.* in` (one `haveILetI` each on `isRational_of_isCurveOver`,
  `isAlgebraic_adjoin_of_transcendental'`, `MeroRealize.main`, `Datum.place`).
* The frozen checker **10473 identical before and after every landing** — the whole
  family was wired the new way, so the frozen count never moved. The new checker's
  surface went 33 → 206 statements across 10 modules.

**The shared home was corrected in the same wave.** The six generic prelim lemmas
(`evalAt_of_not_mem`, `evalAt_eq_inv_evalAt_inv`, `ne_zero_of_ord_eq_one`,
`evalAt_eq_of_ord_sub_algebraMap_eq_one`, `mem_of_ord_sub_algebraMap_eq_one`,
`eq_of_forall_ord_eq`) were first landed in `Place/BranchUniqueness.lean` because that
leaf needed them first; they are `Place.*` API used by two leaves, so they now sit in
`Place/OrdCalculus.lean` (19 declarations, its wire naming the second pin file too) and
`BranchUniqueness` and `LocalParamDatum` import them. `build_ladder --edit OrdCalculus`
priced that move at a 4-module / 2,266-line cascade, ≈30 s; the three modules re-check at
19 / 37 / 40 and the aggregate fell by the ten duplicated rows it removed.

## 2. What the subject now has

Every premise of the charted-space capstone
`Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` that belongs to
this family is now a ported, statement-checked theorem: the finite cover (`FiniteCover`),
uniqueness of the analytic branch (`BranchUniqueness`), the chart and its order
dictionary (`MeroRealize` + `LocalParamDatum`), and the three supports it rests on —
the Laurent expansion at a degree-one place (`LaurentSeriesModel`), transcendence of a
nonzero-order element (`TranscendentalOfOrdNeZero`), finite-dimensionality transfer
(`FinitenessTransfer`) — plus the analytic majorant (`EisensteinAlgSeries`). What the
capstone still lacks is not in this family: the charted-space assembly itself and
`Place.exists_forall_ord_eq_finset` (291 silo lines, ready on the shelf).

## 3. Friction and deviations

1. **The prelim block cost nothing.** The second and third `S_` files re-prove the same
   prelim block as the first; with `OrdCalculus.lean` and the `Defs/` modules in place,
   LP2 imported 15 of its 21 rows and LP4 imported the nine it shares with LP2's file.
   The shape tier of `port_advise` is what named them (the byte tier still says "none"):
   `BranchUniqueness` was written from a 12-substitution / 5-residue report, and LP4
   from an 8-row one whose two extra pointers were false positives (see 4).
2. **One real API drift, four deprecations.** LP3a's engine needed exactly one mathlib
   rename — `HahnSeries.embDomain_notin_range` → `embDomain_of_notMem_range` — plus four
   `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` sites. LP3b needed four:
   `aeval_algebraMap_apply` → `aeval_algebraMap_apply_eq_algebraMap_eval`,
   `natDegree_eq_zero_of_derivative_eq_zero` → `Polynomial.derivative_eq_zero`, eight
   `if_pos`/`if_neg` → `ite_eq_*`, and one added import
   (`RingTheory.PowerSeries.NoZeroDivisors`). LP2 and LP4 needed one each (`dif_pos` →
   `dite_eq_left`). Everything else — the `HahnSeries`/`LaurentSeries`/`FLT`
   `FormalMultilinearSeries` API, the `meromorphicOrderAt`/`analyticOrderAt` lemmas, the
   `WithTop ℤ` coercions, `SL_mul` and `Datum.ord_place` included — compiled **verbatim**.
3. **The pin's blanket `attribute` prelude is not copied.** The LP4 `S_` file disables
   8 instances and 17 `[simp]` lemmas file-wide because the pin's own files re-declare
   them. The port carries each once, so nothing needed narrowing; the decision is
   recorded in `MeroRealize.lean`'s header.
4. **Two `port_advise` false positives, both type-only `def` matches.** `Fam.isRational`
   /`Fam.eventually_mem` looked like LP2's `Setup.isRational`/`Pkg.eventually_mem` (same
   statement text, but they take an implicit `P : Fam F`), and `AutomorphicForm`'s `S2`
   looked like `MeroRealize.RSet`. The orders flagged the first pair; the second is the
   parser's known "type-only `def`" class. Both were written, not imported.
5. **The pin's repeated prelim blocks are imported, not reproduced.** The third `S_`
   file spends 70 lines (pin 625–694) re-stating ten lemmas the port already has, and
   LP4 does not reproduce them: the block is imported from its homes and the module
   declares only the `Datum` layer (39 + the headline). The same reading applies to
   LP2, which imports 15 of its 21 prelim rows. That is the port's point — one copy of
   the mathematics, at its theory home — so it is not a "deviation" and needs no
   comment beyond the header's import list.
6. **A frontier transient.** `frontier.py`'s `sources` tier now reads `spec-pin:`
   headers, so a module counts as ported **as soon as its header exists** — the engine
   module's header credited the LP4 node while the module was still being written (the
   `names` tier behaves the same way). Harmless (the measurement is of the tree as it
   stands, and the real gate is `check_port`), but a reader should not trust the frontier
   mid-wave. Recorded in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

## 4. Residuals

None of the family's own: the two homing questions this record was opened with — where
the six generic prelim lemmas belong, and whether the pin's repeated prelim block is
reproduced — were settled in the same wave (§1, §3.5). The family's successors are
outside it: the charted-space capstone
(`Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`, 1,576 silo
lines), its connectedness sibling (679) and `Place.exists_forall_ord_eq_finset` (291,
ready).
