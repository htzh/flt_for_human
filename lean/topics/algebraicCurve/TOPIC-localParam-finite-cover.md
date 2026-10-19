# TOPIC — the local-parameter finite cover (and the `localParam` leaves beside it)

The `AlgebraicCurve` leaf `AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`
— "finitely many parameter discs cover every place" — is one of a **family of six
leaves** the target closure needs for the complex function field's charted-space
structure. This note is the mathematics, the family's shape (which determines the
cut), the landing and its wire, and what remains. The order that produced it is
[WORKORDER-LP1-localParam-finite-cover.md](WORKORDER-LP1-localParam-finite-cover.md);
the landing record is [../../logs/localParam-finite-cover.md](../../logs/localParam-finite-cover.md).

Pin: `anthropics/fermats-last-theorem@aa2d8b3`. mathlib `v4.34.0`.

## 1. The mathematics

Let `F` be a function field in one variable over `ℂ` (`x` transcendental,
`F/ℂ(x)` finite), `IsCurveOver ℂ F`, and `Place ℂ F` its places. For each place `v`
suppose a chart is given: a radius `ρ v > 0`, a local parameter `t v ∈ F` and a map
`γ v : ℂ → Place ℂ F` with

* `γ v 0 = v`, and `ord_{γ v z}(t v - z) = 1` for `‖z‖ < ρ v` — `z ↦ γ v z`
  inverts the parameter `t v` on a disc;
* `u ↦ f(γ v u)` is meromorphic at `z` with `mer`-order `ord_{γ v z} f`, and analytic
  where that order is nonnegative — the reading of `evalAt` along the chart.

Then there are a **finite** set `S` of places and a radius function `r` with
`0 ≤ r v < ρ v` on `S` such that every place `w` is `γ v z` for some `v ∈ S`,
`‖z‖ ≤ r v`. That is, the closed subdiscs `γ v '' closedBall 0 (r v)` form a finite
cover of `Place ℂ F`: the compactness of the Riemann surface attached to `F`.

The proof is the standard one, and it is where the work is:

1. **Separation.** Distinct places are separated by a function `s` (`v`-integral,
   not `w`-integral), and the charts then separate: two charts have disjoint images
   on small discs. This is `Fam.separation`, and it needs the *elementary* place
   calculus (`ord`/`evalAt` against the residue field).
2. **The fibre.** Fix `g ∈ F` with `g ≠ algebraMap ℂ F c` for every `c`. The divisor
   of `g - c` has degree `0`; its *positive* part `Z c` (places where `ord(g-c) > 0`)
   has cardinality-controlled sum, and the negative part is constant in `c`. The
   places above a small disc are exactly `Z c`, and each is the image of the chart
   at its own place.
3. **The local preimage count.** At `w ∈ Z 0`, the reading `u ↦ g(γ w u)` is
   analytic of order `e = ord_w g` at `0`; a local `e`-th root and the inverse
   function theorem give, for any small `a ≠ 0`, exactly `e` preimages — `Fam.fibre`
   via `exists_finset_preimages_of_meromorphicOrderAt_eq` (which is
   `exists_analyticAt_pow_eq` + `HasStrictDerivAt.localInverse` + `nthRoots`).
4. **Compactness.** The fibre statement holds uniformly on a closed disc of values,
   so a finite subcover of the disc gives a finite chart set; `f = t v₀` and its
   inverse `f⁻¹` cover the two cases `f` integral / not integral at `w`.

The pin states step 4 for a bundled family, `structure Fam F` (fields `ρ γ t hρ h₀ ht
hγ`), and derives the cover as `Fam.exists_finset_cover`; the headline instantiates
the bundle.

## 2. The family, and why the cut is two modules

The pin writes the same 24-lemma prelim block into **three** `S_` files of this
subject (the `localParam` leaves), byte-identically:

| leaf | pin lines | what it adds |
|---|---:|---|
| `exists_finset_forall_exists_localParam_eq_complex` | 857 | the finite cover (this cut) |
| `localParam_eventually_eq_comp_evalAt_complex` | 500 | uniqueness of the analytic branch through a place |
| `exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex` | 1,142 | the chart's order-meromorphic-order compatibility |

`port_advise` on the first leaf alone reports **no shared block inside the target
set** — because the block it shares with the *siblings* is not in the target set —
and its substitution table has to be read by shape rather than by text (nine of the
24 prelim lemmas are in the port under other spellings; see §4). Diffing the three
prelim blocks by hand (the corpus makes this cheap: `rg` the file rows of
`tmp/flt-statements/statements.tsv`) splits it into

* **nine** lemmas the port already carries, with the same names and statements up
  to binder spelling — imported, never re-proved:
  `Place.adicValuation_le_one_of_mem`, `Place.adicValuation_eq_exp_neg_ord`
  (`Defs/Repartitions.lean`), `Place.mem_of_ord_nonneg`,
  `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean`), `Place.evalAt_algebraMap`,
  `Place.evalAt_mul` (`Defs/PlaceEvaluation.lean`), `Place.evalAt_zero`,
  `Place.ord_sub_evalAt_pos` (`Defs/PlaceCalculus.lean`), `Place.ord_algebraMap`
  (`Defs/Place.lean`);
* **thirteen** that are new to the port: `not_mem_iff_ord_neg`,
  `ord_pos_of_mem_maximalIdeal`, `residue_eq_zero_of_ord_pos`,
  `isRational_of_isCurveOver`, `residue_algebraMap`, `evalAt_sub_algebraMap`,
  `evalAt_eq_zero_of_ord_pos`, `ord_pos_of_evalAt_eq_zero`,
  `evalAt_eq_of_ord_sub_algebraMap_pos`, `mem_of_ord_sub_algebraMap_pos`,
  `sub_algebraMap_mem_iff`, `ord_sub_algebraMap_of_not_mem`,
  `exists_mem_and_not_mem`. Five appear verbatim in *both* sibling `S_` files
  (`ord_pos_of_mem_maximalIdeal`, `isRational_of_isCurveOver`, `residue_algebraMap`,
  `evalAt_sub_algebraMap`, `ord_pos_of_evalAt_eq_zero`) and two more in the
  `eventually` one only (`residue_eq_zero_of_ord_pos`, `evalAt_eq_zero_of_ord_pos`).
  Eleven are re-proved in 3–40 pin files each (`ord_pos_of_mem_maximalIdeal` 32,
  `residue_algebraMap` 29, `isRational_of_isCurveOver` 21,
  `evalAt_sub_algebraMap` 23, `evalAt_eq_zero_of_ord_pos` and
  `ord_pos_of_evalAt_eq_zero` 40 each, …). One home is therefore a real dedup, not a
  convenience: the remaining six are this leaf's own but are generic place API;
* the subject's own content beyond it (`sum_support_eq_zero`, the two analytic
  lemmas, `Fam`), which belongs to this leaf and to nothing else.

So the landing is **two modules**, and the manager's pre-round *is* the first: the
thirteen generic lemmas are shared ground of the three leaves, not of this silo, and
they are homed once at the natural place-API home.

## 3. The landing

| module | lines | role | declarations | wire |
|---|---:|---|---:|---|
| `FLTForHuman/AlgebraicCurve/Place/OrdCalculus.lean` | 272 | the generic place calculus (manager's pre-round; 19 after the re-home of §3 note) | 19 public | `spec-pin:` two pin `S_` files, 19 ok |
| `FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean` | 654 | the `Fam` engine and the headline | 17 public (16 internal + 1 headline) | `spec-pin:` the wrapper + the `S_` file, 17 ok |

Both are **wired under the new per-module checker** (`spec/check_port.py`, playbook
§4): the `spec-pin:` lines in each module's leading comment block are the whole
wire, every public declaration is diffed against the pin file named there, and
neither module appears in `spec/old_check_stmts.py`'s frozen `PORT_FILES`. So the
old checker's count is *unchanged* by the landing, and the new one reports 30
statements verified — a surface that the frozen list-based wire could only have
recovered by hand-adding two entries and their two `SOURCES` rows.

Measured on the tree the landing leaves: tier-1 build **3,295 jobs, 0 warnings**;
`#print axioms` on the headline and on `Fam.fibre`/`exists_finset_cover`
`[propext, Classical.choice, Quot.sound]`; the frozen `old_check_stmts.py` count
**10473 identical before and after** (the landing adds no registry entry); tier-3
register unchanged. The only proof-side adaptations to mathlib `v4.34.0` were seven
deprecated `if_pos`/`if_neg`/`dif_pos`/`dif_neg` renames to
`ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`; the analytic core
(`meromorphicOrderAt_eq_int_iff`, `HasStrictDerivAt.localInverse`, `map_nhds_eq`,
`nthRoots`, `Complex.isPrimitiveRoot_exp`, `Complex.slitPlane`) transcribed
unchanged.

Two details the new protocol forces, recorded because they differ from the old one:

* **Section variables stay.** A pin `S_` declaration written under
  `variable {K F : Type*} [Field K] [Field F] [Algebra K F]` has the statement text
  `(v : Place K F) {f : F} …`; the port's `Defs/` copies of the same lemmas spell
  the binders out (`{K F : Type*} [Field K] … (v : Place K F) …`). Both are the same
  mathematical statement, but the checker hashes the *text*, so a module that
  restates a pin lemma with explicit binders would report `MISMATCH`. The rule for
  new modules: transcribe the pin's section-variable shape, and import (do not
  restate) the `Defs/` copies.
* **The headline is named at the wrapper.** The pin's `S_` row is `solution` (its
  `p2m` scaffolding name); the wrapper's row `AlgebraicCurve.Place.exists_finset_…`
  carries the same statement (same statement hash). The port declares the headline
  only, at the wrapper's name and text, so the wrapper row matches by name and the
  `S_` row matches by content.

## 4. What the cone gets, and what remains

This leaf's two consumers are `AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`
("the places of a complex function field form a compact Riemann surface") and
`exists_strictMono_forall_tendsto_evalAt_complex` (sequential compactness of the
place space). They sit in the same `AlgebraicCurve.Place` family and need, besides
this cover, the other `localParam` leaves, `exists_forall_ord_eq`, `exists_ord_eq_one`
and `connectedSpace_of_chartedSpace_…`. None of those is ready yet; the charted-space
leaf is the family's capstone. The subject is **not** the D-S column's prunable
complex-analytic one (`CellDissection` / `pathIntegral` / `abelJacobi` /
`pathPeriodLattice`): it is on the demand `--ds` still shows.

Shelf after the landing (the `--include-leaves` view of §2 of
[PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md)): the two sibling `localParam`
rows remain, each now shorn of the prelim block and therefore cheaper by the 13
lemmas landed in `OrdCalculus.lean`.

**The family is being finished** (2026-10-19). `localParam_eventually_eq_comp_evalAt_complex`
(the branch-uniqueness leaf, 500 pin lines) landed as `Place/BranchUniqueness.lean` —
429 lines, 43 statement-checked declarations, one headline, 15 prelim lemmas imported
([WORKORDER-LP2-branch-uniqueness.md](WORKORDER-LP2-branch-uniqueness.md)). The third
leaf, `exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex` (1,142 lines, 111
declarations, 110 of them public), is **not ready**: it needs three further leaves —
`Place.exists_algHom_laurentSeries_of_deg_eq_one` (523),
`Place.transcendental_of_ord_ne_zero` (41) and
`AlgebraicCurve.finiteDimensional_adjoin_of_transcendental` (91), plus the analytic
`PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex` (455) — before its
statements can be written. They landed on 2026-10-19 in the two sets
[WORKORDER-LP3a-laurent-and-generator-transfers.md](WORKORDER-LP3a-laurent-and-generator-transfers.md)
(three modules, 6 statement-checked declarations) and
[WORKORDER-LP3b-power-series-growth.md](WORKORDER-LP3b-power-series-growth.md) (one
module, 24 statement-checked declarations); the third leaf itself is
[WORKORDER-LP4-meromorphic-order-dictionary.md](WORKORDER-LP4-meromorphic-order-dictionary.md),
two modules — a 60-declaration `MeroRealize` engine and the `LocalParam.Datum` façade —
whose 110 public declarations the new checker diffs.

**The family is complete (2026-10-19).** Six further modules, 2,653 lines and **167
statement-checked declarations** cover the two remaining leaves and their four
premises: `Place/BranchUniqueness.lean` (37 ok), `Place/LaurentSeriesModel.lean` (1),
`Place/TranscendentalOfOrdNeZero.lean` (2),
`IsCurveOver/FinitenessTransfer.lean` (3),
`Analysis/PowerSeries/EisensteinAlgSeries.lean` (24), `Place/MeroRealize.lean` (60) and
`Place/LocalParamDatum.lean` (40) — the column's largest wired surface, and the largest
`localParam` set. The six generic prelim lemmas the second leaf first homed now sit
where they belong, in `Place/OrdCalculus.lean` (19 declarations), and every repeated
prelim block in the pin is imported rather than reproduced: the port keeps one copy of
the mathematics, at its theory home. Record: [logs/localParam-family.md](../../logs/localParam-family.md).
The charted-space capstone is now missing only its own assembly and
`Place.exists_forall_ord_eq_finset`. One of those four is a **frontier blind spot worth recording**:
`AlgebraicCurve.finiteDimensional_adjoin_of_transcendental` is priced as ported because
the port declares that last name in `ModularCurve/X1/FunctionFieldResidue.lean` under a
*different statement* (the finiteness as an argument, not an instance) — §9's
last-name blindness, caught here and now ported properly.

`AlgebraicCurve.Place.exists_forall_ord_eq_finset` (291 silo lines, ready) and
`AlgebraicCurve.Place.exists_ord_eq_one` (a premise of the charted-space capstone)
are the natural next cut after the family.

Recorded negatives, so a later run does not redo them:

* `port_advise` priced the whole pin file at `0` already-in-port declarations, all
  857 lines new. That was a **binder-text artefact**, not a fact: nine of the 24
  prelim lemmas were in the port and had to be imported. The tool now reports the
  reuse by **shape** as well as by text (same conclusion, same hypothesis multiset
  once section variables, instances and bound names are normalised) and lists the
  pairs whose binder skeletons do not line up as a **residue** pointer; on the tree
  before this landing it finds 6 + 1 `private` of the nine, and names the other
  three. Read the reuse question by shape, and restate nothing the shape tier finds.
* `port_plan.py` reads `NET NEW MATH LINES 832` for the file; the true cost of this
  landing is ≈590, after the nine imports and the manager's 13-lemma module.
* The pin's `Fam` is a `structure`, and the checker hashes a structure as its header
  plus ordered field names plus field-type text. Keep the pin's field order.
