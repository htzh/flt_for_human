# SET-AF101 — the stabilizer order of a Weierstrass curve, and the Tate curve's point series

**Status: PLANNING (2026-11-22).** The next set of the AF column in the D–S cone, cut from the
**`leaves` block** — the ready shelf's AF-subject half was emptied by SET-AF100, and the three
stories this set takes are the ones SET-AF65's §leaves table priced and deferred (496, 471, 256, 247,
213, 187, 157, 156, 100, 70, 40, 34, 29, 28, 26, 26, 22, 19, 19, 17, 17 silo). **Five orders, 22 rows,
2,196 silo, ~1,901 net new lines**, four new modules and one insertion — the two Tate-curve
points-law rows were **cut mid-set** when their order hit a definition-layer gate (see §7).

The subject is the elliptic side of the cone, in two stories:

* **the automorphism group of a Weierstrass curve** — the *order* of the stabilizer of the curve in
  the group of variable changes: the four-case bound of `finite_stabilizer_and_natCard_le_of_j`
  (≤ 6, ≤ 4, ≤ 12, ≤ 24, by whether `6` is a unit and whether `j` is `0` or `1728`), the exact count
  `= 2` away from the exceptional `j`s (both in residue characteristic `≠ 2, 3` and in characteristic
  2 or 3), the Deuring normal form that produces the exceptional points at 3-torsion (in
  characteristic `≠ 2, 3` and in characteristic 2), and the transcendental-`j` perturbation;
* **the Tate curve's point series** — the addition law of the `pointX`/`pointY` coordinates on the
  norm-≤-1 locus and on the norm-= 1 locus, and the convergence/q-multiplication identities of the
  `xfun`/`yfun` series.

**No definition-layer work, and that is the reason this set is cut now.** Every statement's
vocabulary is either mathlib (`WeierstrassCurve.VariableChange`, `MulAction.stabilizer`,
`WeierstrassCurve.Affine.ψ`/`ΨSq`/`Φ`, `ValuationSubring`, `IsLocalRing.ResidueField`) or the port's
own `TateCurve/QSeries.lean` + `TateCurve/PointSeries.lean` (the pins' `Def_TateCurve_QSeries` and
`Def_TateCurve_PointSeries`, transcribed whole). The two leaves that *would* need a definition gate
(`stepCurve_stepSubgroup_two_eq` 231, `exists_map_eq_veluQuotient_…` 194) are deferred in §7 even
though their definitions are ported — they are a different story (cyclic quotients), not this one.

| # | order | rows | silo | net | modules |
|---|---|---|---:|---:|---|
| W1 | the four-case stabilizer bound and the exact count `= 2` | 3 | 939 | 883 | `WeierstrassCurve/Automorphism/StabilizerOrder.lean` (new) |
| W2 | the Deuring normal form at 3-torsion (char ≠ 2,3 and char 2) | 4 | 480 | 436 | `WeierstrassCurve/Automorphism/DeuringForm.lean` (new) |
| W3 | the transcendental `j` and the valuation subring carrying it | 2 | 226 | 183 | `WeierstrassCurve/Automorphism/NormalForm.lean` (insertion) |
| W4 | the division-polynomial point arithmetic | 5 | 231 | 137 | `Elliptic/PointArithmetic.lean` (new, rehomed) |
| T2 | the convergence and q-multiplication identities | 7 | 320 | 262 | `TateCurve/SeriesIdentities.lean` (new) |
| ~~T1~~ | ~~the Tate curve's addition law on the unit locus~~ | ~~2~~ | ~~718~~ | ~~625~~ | **cut**, §7 |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af101_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | 370 / 189,611 |
| ready rows | 24 / 10,139 |
| leaves | 44 / 18,163 |
| withheld (FR-0044 guard) | 4 / 831 |

This is SET-AF100's landing read reproduced exactly. The set cuts from the **leaves** block only, so
the `needed` figure it moves is the terminal count and not the ready block.

## 1. The stories

* **W1 is the cardinality half of the automorphism theory.** The port already holds the *finiteness*
  (`Automorphism/NormalForm.lean`, `finite_stabilizer_variableChange`) and the exceptional
  automorphisms (`Automorphism/{CharTwo,CharThree}.lean`). What was missing is the order: the
  four-case bound and the exact `= 2`. The 496-line pin is a 35-declaration all-public flattened
  file (the largest single pin of the set); the two `= 2` pins are 4 and 26 declarations.
* **W2 is the Deuring normal form**: at a 3-torsion point the curve is `y² = x³ + αx` in a
  3-adic valuation ring with a unit discriminant (`exists_variableChange_eq_deuring_of_isUnit_three`),
  its characteristic-2 analogue (`exists_isUnit_mul_pow_eight_eq_of_charTwo`, where the `j = 0` case
  is a `t = u * μ ^ 8` statement), and the two `variableChange_mk_smul_eq_self` micro-rows that make
  the diagonal automorphisms act trivially on `y² = x³ + B` and `y² = x³ + Ax`.
* **W3 is `j` transcendental**: perturbing `a₄, a₆` by a transcendental `t` makes `j` transcendental,
  and the valuation subring that carries the perturbation exists over any characteristic-0 field.
  Both rows are insertions into the module whose subject is the normal form.
* **W4 is the point arithmetic of the division polynomials**: `n • some x y` has `x`-coordinate
  `Φ n / ΨSq n`, the `ψ`-criterion `n • P = 0 ↔ ψ n = 0`, `ψ n ^ 2 = ΨSq n` on the curve, and the two
  3-torsion/2-torsion addition laws on `y² = x³ + B`. High outbound demand (project fan-in 41, 44,
  51) for 231 silo — the cheapest rows of the set.
* **T1, T2 are the Tate curve.** The addition law states `P(vw) = P(v) + P(w)` for the point
  coordinates of the `q`-series, on two norm regimes; the identities are the absolute convergence of
  `xfun`/`yfun`, their `q`-multiplication invariance, the nodal relation `yfun² + xfun·yfun = xfun³`,
  the Lambert-type `tsum`-over-divisors identity and the annulus lemma that puts any `u` in the
  norm-< 1 annulus by a power of `q`.

## 2. The scaffolds

As SET-AF100: each module exists before its order starts, with its header prose, its `spec-pin:`
wires, a narrow import list and the **headlines** only, at the pins' `solution` statements and the
published names, body `sorry`. The insertion (W3) adds its two headlines to `NormalForm.lean` and its
two wire lines.

The scaffolds, measured before any order starts (`check_port --force`, then `lake build` of all six
modules: 3,133 jobs, `sorry`-only warnings, and the set-level import probe silent):

| module | scaffold `check_port` | engine to land |
|---|---:|---:|
| `TateCurve/SeriesIdentities.lean` (new) | 7 ok | 2 `private` engines (9 + 3 rows) |
| `WeierstrassCurve/Automorphism/StabilizerOrder.lean` (new) | 3 ok | 62 public rows (3 pins) |
| `WeierstrassCurve/Automorphism/DeuringForm.lean` (new) | 4 ok | 12 public rows (4 pins) |
| `WeierstrassCurve/Automorphism/NormalForm.lean` (insertion) | 24 ok | 11 public rows (2 pins) |
| `Elliptic/PointArithmetic.lean` (new, rehomed — see below) | 5 ok | 8 public rows (5 pins) |

**One order's module was rehomed by the manager, and the reason is the finding of the set** (W4):
mathlib v4.34's `DivisionPolynomial/` files never mention `Affine.Point`, so the pin's point-side
division-polynomial engine (`smulEval`, `zsmul_eq_smulEval`, `smul_eq_zero_iff_evalEval_ψ`, the
`evalEval` bridge) is the FLT pin's own `Definitions/Def_WeierstrassCurve_EDSEngine`, which the port
already holds in `FLTForHuman/Elliptic/{MulFormula,JacobianMulFormula,Bridge}.lean`. The order was
written into `WeierstrassCurve/PointArithmetic.lean`, which would have made a `WeierstrassCurve/`
module depend on the `Elliptic/` chain — no cycle, but an inverted layering. The module's subject *is*
the elliptic multiplication-formula layer, so it was moved to `Elliptic/PointArithmetic.lean`
(275 lines, `check_port` 13 ok, silent, the import direction now downward). The four `PortCard.*` rows
and the two `ws13_*` rows stay one module: a division-polynomial point arithmetic split over two
directories would be two theories, not one.

**One order target was wrong for the third time in two sets** (W1): I wrote "65 ok" counting the pins'
62 engine rows *including* their three `private` helpers, but `check_port` skips `private`
declarations, so the module's maximum is **62** = 3 headlines + 59 public engine rows. The rows stay
`private` as the pin has them. The rule, stated once for both sets: **a `check_port` target is the
number of _public_ declarations the module will hold**, and a pin row that is `private` in the source
never contributes to it.

One wire finding at scaffold time: `StabilizerOrder`'s four-case bound is stated in the S_ file with
`WeierstrassCurve.VariableChange` qualified and in the `Theorems/` wrapper short — the content tier
matched neither spelling against the S_ copy, so that module carries the wrapper line as well
(FR-0290's rule: the wrapper is the statement authority).

The pins of this set carry `set_option linter.unusedSectionVars false` and
`set_option linter.unusedVariables false` (the W1-automorphisms precedent, 86 landed modules carry the
first), and one carries `linter.unusedSimpArgs`. Those are **part of the source's declaration
environment** and are transcribed where the pin has them — but a dead *binder* is `_`-prefixed rather
than excused by a linter, and no module carries a `set_option maxHeartbeats`.

## 3. The pricing

| order | raw `S_` lines | dup copies | boilerplate | **net new** |
|---|---:|---:|---:|---:|
| W1 (3 nodes) | 939 | 12 | 44 | **883** |
| W2 (4 nodes) | 480 | 0 | 44 | **436** |
| W3 (2 nodes) | 226 | 0 | 22 | **183** |
| W4 (5 nodes) | 231 | 7 | 87 | **137** |
| T1 (2 nodes) | 718 | 45 | 48 | **625** |
| T2 (7 nodes) | 320 | 5 | 53 | **262** |
| **total cut** | **2,196** | **24** | **250** | **1,901** |

T1's 45 duplicate lines are the two pins' shared prelude (the two headlines differ only in the norm
hypotheses of the points, not in the engine).

## 4. The gates

As SET-AF100 §4, with the engine gate as the `statement_db` pin-vs-module diff for the mostly-private
pins (T1's engine, T2's two engine rows) and for the all-public ones the checker's own count plus the
diff.

## 5. The landing

Every number below was re-measured by the manager on the landed files. The five modules hold
**133 `ok`** (13 + 7 + 62 + 16 + 35), 0 mismatch / 0 missing / 0 unjustified `own`; all five are
silent at the edit loop with no `sorry`; the set-level import probe is silent; a locked wave build of
the five is `Build completed successfully (3161 jobs)` with **no warning line at all**; and
`#print axioms` on all **21 headlines** is a subset of `[propext, Classical.choice, Quot.sound]` with
no `sorryAx`.

| order | module | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| W1 | `Automorphism/StabilizerOrder.lean` (new) | **991** | **62 ok / 0 / 0** | 65↔65 rows, 62 public / 3 private; 62/62 statements match | clean (62) | 2 (pin's own pairs) | 0 / 0 | 6,000 / 5,000 |
| W3 | `Automorphism/NormalForm.lean` (+264) | **846** | **35 ok / 0 / 0** | 11/11 engine rows, statement hashes identical; the 2 headlines re-hash equal | clean (15) | 1 (pin's own pair) | 0 / 0 | 17,000 / 16,000 |
| W4 | `Elliptic/PointArithmetic.lean` (new) | **275** | **13 ok / 0 / 0** | pin 13 ↔ module 13, statement-hash multisets equal | clean (13) | 2 (pin's own pairs) | 0 / 0 | 3,200 / 3,000 |
| T2 | `TateCurve/SeriesIdentities.lean` (new) | **359** | **7 ok / 0 / 0** | 21 pin rows (7 public + 14 `private`) → 18 by hash, 1 by name, 2 folded; 0 unaccounted | clean (7) | 0 | 2 / 22 (pin's own dead privates) | 2,000 / 1,500 |
| W2 | `Automorphism/DeuringForm.lean` (new) | **524** | **16 ok / 0 / 0** | 16 pin rows ↔ 16 module rows, 16/16 statement hashes identical | clean (16) | 2 (pin's own `main`↔`solution` pairs) | 0 / 0 | 8,000 / 7,000 |

## 6. Plan vs actual (the honesty section)

| order | silo (priced) | net new (predicted) | lines landed | ratio |
|---|---:|---:|---:|---:|
| W1 | 939 | 883 | 991 | 1.12 |
| W2 | 480 | 436 | 524 | 1.20 |
| W3 | 226 | 183 | 264 | 1.44 |
| W4 | 231 | 137 | 275 | 2.01 |
| T2 | 320 | 262 | 359 | 1.37 |
| ~~T1~~ | ~~718~~ | ~~625~~ | 0 (cut) | — |
| **total** | **1,978** | **1,718** | **2,413** | **1.40** |

W4's ratio is the set's outlier and the reason is its engine: `port_plan` priced the five pins as 137
net lines, but their point-side engine (`smulEval`, `zsmul_eq_smulEval`, `smul_eq_zero_iff_evalEval_ψ`,
the `evalEval` bridge) is **not in mathlib** — it is the pin's `Def_WeierstrassCurve_EDSEngine`, which
the port already holds in the `Elliptic/` chain, so the module paid for the *bridge statements* it
states (13 public rows) rather than for proofs. That is the predicted non-event the budget could not
see: `port_plan` prices a pin against the *port*, and the reuse it found was a module this set had to
import, not lines it could skip.

**Four brief claims were false, every one caught by a worker, and three of the four were counts:**

1. **The preamble's "there is no definition-layer work in the set"** — false for T1 (the
   `Def_TateCurve_TorsionParametrization` gate, 28 files / 9,859 lines) and half-false for W4 (the
   point-side division-polynomial engine is FLT's `EDSEngine`, not mathlib). The scoping error is
   FR-0298: the readiness test and the wrapper's imports see the *statement's* vocabulary, not the
   `S_` file's `Definitions` imports.
2. **W1's "65 ok"** — 62: `check_port` skips the pins' three `private` helpers.
3. **Order W1 also under-stated where its engine lives** in a smaller way: the pins' normal-form layer
   is mathlib's `EllipticCurve.NormalForms`, not the port's `Automorphism/NormalForm.lean`; the
   worker imported the former and added no dependency edge to the latter.
4. **W4's home was wrong** (mine): `WeierstrassCurve/PointArithmetic.lean` would have made
   `WeierstrassCurve/` depend on `Elliptic/`. Rehomed to `Elliptic/PointArithmetic.lean`; the subject
   is the multiplication-formula layer, and one theory stays one module.

**One `haveI` linter line** is carried, declaration-scoped, in W1 and W2 (`linter.style.haveILetI`,
load-bearing `letI`/`haveI` instance registrations; 40+ landed modules carry it, precedent
`RepTheory/TypeReproducer.lean:656`). No module carries `maxHeartbeats`, and the pins'
`linter.unusedSectionVars`/`unusedVariables` lines are transcribed where the pin has them (W1 measured
that stripping them leaves exactly 10 unused-section-variable warnings and zero dead-binder warnings —
so nothing is excused silently).

## 7. Not cut — named and deferred (FR-0040)

* **The two Tate-curve points-law rows were cut mid-set** (`TateCurve.point_mul_eq_add_of_norm_le_one`
  471, `…_of_norm_eq_one` 247): their order's first report found that the proofs (and seven of the
  engine rows' *statements*) rest on `Definitions/Def_TateCurve_{XMultStructure,XMultAlignment,
  XMultDistinctRouteB,TorsionParametrization}.lean` plus three `Theorems/` rows, a **28-file /
  ≈9,859-line** closure the port does not have. The leaf reads `needed = 1, premises = 0` because the
  readiness test walks the *wrapper's* graph premises and the wrapper imports only
  `Def_TateCurve_PointSeries` (ported) — the `S_` file is where the gate lives (FR-0298). Registered
  whole in [CARRY-FORWARD.md](../../CARRY-FORWARD.md); the row-by-row dossier and the five rows proved
  before the cut are in `lean/tmp/af101/AF101T1-REPORT.md`. **The layer order is not opened in this
  set**: the worker's step 1 (the `OffLattice`/`AddParams` slice) is cheap and its proofs are already
  verified, but it only makes the seven rows *statable* — the two headlines still need the
  `SymAddHyps`/`DiffHyp` stack — and `XMultStructure` is not self-contained either (`QShift`,
  `pointX_inv`, `pointX_zpow_mul` are unported). So it is a definition-layer set, priced and planned
  in four steps in CARRY-FORWARD, not a sixth order here.
* The two definition-gate-free-but-different-story leaves of the WeierstrassCurve group:
  `WeierstrassCurve.stepCurve_stepSubgroup_two_eq` (231) and
  `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` (194) —
  cyclic quotients and reduction, whose definitions (`Velu/CyclicQuotientJ.lean`'s `stepCurve`,
  `stepSubgroup`, `Velu/Defs.lean`'s `veluQuotient`) are ported. A "cyclic quotient" set's rows.
* `WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo`'s sibling and the remaining
  `ValuationSubring` leaves (825 silo, 13 rows: `ringKrullDim_le_ringKrullDim_comap_add_trdeg` 269,
  `exists_smul_mem_of_transcendental_residue` 262, `natDegree_map_eq_card_roots_of_splits` 174,
  `IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83 with fan-in 21, `tensorProduct_exists_primitive_factor`
  78, `exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` 57,
  `charP_residueField_of_liesOverPrime` 37 with fan-in 27) — the valued-field subject, a set of its
  own.
* The `NumberField` leaves: `mixedEmbedding.*` (392, blocked on the definition layer),
  `exists_continuousOn_exp_eq_rayClassLSeries` (684), `ncard_primesOver_…` (233),
  `Units.exists_forall_abs_sub_mult_mul_log_le` (98),
  `InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` (94),
  `summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` (69, fan-in 41), and the
  `MeasureTheory.Lp` leaf (148).
* `M4aTorus.completedRayL_fe` (12,126) — a single giant pin, not cuttable by any set.
* Withheld by the FR-0044 guard: the four rows of §AF100 §7.

## 8. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af101_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 370 / 189,611 | **349 / 187,415** |
| ready rows | 24 / 10,139 | **31 / 12,398** |
| leaves | 44 / 18,163 | **23 / 15,967** |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is exactly the cut — **−21 nodes / −2,196 lines** for the twenty-one rows that landed — and
the two T1 rows are the only ones of the set still on the shelf, which is the check that deleting the
module (rather than leaving it `sorry`-bodied) was the honest move. **Seven rows became ready because
of the set** (2,259 silo), and they are its payoff:

* `WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three` (816) and
  `…_of_order_four` (713) — W1's consumers: the torsion-basis classification at the two exceptional
  `j`-invariants, the next step of the automorphism story;
* `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero` (572) — W2's
  consumer (`three ≠ 0` in the Deuring normal form);
* `TateCurve.sOne_eq_tsum_xfun` (101), `TateCurve.pointX_zpow_mul` (22), `pointY_zpow_mul` (22) and
  `TateCurve.defectCoeff_zero` (13) — T2's consumers, and `pointX_zpow_mul` is **one of the rows
  T1's layer needed** (CARRY-FORWARD): the layer's first step is now cheaper than the dossier priced.

## 9. What the set leaves behind

1. **`Elliptic/PointArithmetic.lean`'s header** — the measured statement that mathlib v4.34's
   `DivisionPolynomial/` files never mention `Affine.Point`, so the point-side division-polynomial
   engine is FLT's `EDSEngine` and lives in the `Elliptic/` chain. That is the fact the next set that
   touches multiplication formulas should read first.
2. **`lean/tmp/af101/AF101T1-REPORT.md`** — the deferral dossier for the Tate-curve torsion
   parametrisation: the 28-file / 9,859-line gate inventory, a 24-row statability table, a four-step
   layer order, and eleven verified proof texts (`tmp/af101/T1-five-rows.lean`,
   `T1-offlattice-rows.lean`).
3. **FR-0298** — the scoping rule this set learned the hard way: a leaves row's real gate is the
   **`S_` file's** `Definitions` imports, not the wrapper's.
4. **The scaffold-table + landing-table pattern**, with the corrected count rule (a `check_port`
   target is the number of *public* declarations; a pin's `private` rows never contribute).
5. **Two registered dedups** for a refactor round: the `unipotentGL2_algebraMap` pair (SET-AF100) and
   the `D0Aux` block of `NormalForm.lean` against `RingTheory/WittVector/Lift.lean` (this set).
