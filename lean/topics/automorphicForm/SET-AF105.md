# SET-AF105 — the Euler product, the level-spherical eigenvectors, the regular prolongations, the semisimple criterion, and the dictionary's points

**Status: LANDED (2026-11-27).** Five orders, twelve rows, 4,413 silo, seven new modules plus the
definition-layer module, **170 checked declarations, none `sorry`-bearing, and no edit-loop gap at all**
(§6.1); the shelf re-read (§7) shows the set consumed its twelve rows and made **8 new rows ready** while
taking **2 leaves out of the leaves block**. What follows is the brief as it was cut. The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. **Five orders, twelve rows, 4,413 silo**, **seven new modules plus one
definition-layer module** (the manager's, already landed). It is the shelf's head after SET-AF104:
the four rows this set's predecessors made ready are *inside* it, plus the `AlgebraicCurve`
regular-prolongation block and the `GaloisRep` criterion the last three sets kept deferring.

| # | order | rows | silo | module(s) |
|---|---|---|---:|---|
| A | the Euler product for the Rankin–Selberg quotient integral | 1 | 1,381 | `AutomorphicForm/Adelic/RankinSelbergEulerProduct.lean` (new) |
| B | level-spherical eigenvectors and the cut projector | 2 | 523 | `AutomorphicForm/Adelic/Cusp/LevelSphericalEigenvector.lean` (new) |
| C | regular prolongations and the `P¹` place-∞ formula | 4 | 1,184 | `AlgebraicCurve/RegularProlongationRetraction.lean` (new), `AlgebraicCurve/P1/PlaceInftyReduction.lean` (new) |
| D | the semisimple-representation criterion, and the two `LiesOverPrime` leaves | 3 | 615 | `GaloisRep/SemisimpleCriterion.lean` (new) |
| E | the complex place dictionary's points, and integrality from a regular differential | 2 | 710 | `ModularCurve/ComplexPlaceDictionaryPoint.lean` (new), `ModularCurve/X1/IntegralityDifferential.lean` (new) |
| **total** | | **12** | **4,413** | 7 new modules |

Twelve rows (ten from the ready block and the two leaves of D), 4,413 silo. The set is deliberately smaller than SET-AF103/104 (~4,400 against ~5,600): two of its rows are
single rows with 15 and 19 premises (A, E's second), D's three are one 31-declaration engine plus
two one-line leaves, and B's 435-row is a 12-premise consumer. The measured shape risk is **premise
count**, not size, and the plan-vs-actual table in §6 will say whether that was the right unit.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af105_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **314 / 170,417** |
| ready rows | 22 / 6,379 |
| leaves | 18 / 15,127 |
| withheld (FR-0044 guard) | 4 / 831 |

SET-AF104's landing read, reproduced exactly (`lean/tmp/af104/shelf_af104_landed.json`), so nothing
has landed since. The 21 `--selfcheck` false ported markers are the same set; of them only
`ModularCurve.ModularPolynomialData.eq_all` is on the needed path (75 lines).

**Four of the set's rows are the last set's payoff** — `exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion`
(1,381, order C's consumer), `exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType` (435)
and `exists_idempotent_cutProjector_of_isCompact` (88) (orders B/A's consumers), and
`isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC` (340) (order E's
consumer). The rest is the shelf's own head: the `AlgebraicCurve` regular-prolongation block
(1,184 over four rows), the `GaloisRep` criterion (495) with the two `ValuationSubring` leaves
(83 + 37) that SET-AF103 §5 deferred, and the complex place dictionary's point row (370, deferred by
both AF103 and AF104).

## 1. The stories

### A — the Euler product

`AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion`
(**1,381** silo, **19 premises**, 55 pin declarations). For a number field `K` and a pair of cuspidal
forms `x y` that satisfy a Hecke **recursion** at every place outside a finite `S` (the pin's `_hP`:
the product of the two Whittaker coefficients at `gen v ^ m * g` factors through the two recursion
sequences), the quotient integral is the Euler product of the local factors times the `s`-part
integral. This is the row that turns SET-AF104C's analyticity result into an `L`-function: the
positivity/analyticity half is landed, the product half is here.

* **Definition layer**: seven pin `Def_` modules, all ported — and one that was **not**, and that this
  set had to port first: `Def_AutomorphicForm_HeckeEigenfunction`, see §2.
* **Premises**, all ported: `Adelic/{FiniteIntegralConjugation,IdeleNormDet,IwasawaShellInvariance,
  RationalCentreHaar,RationalUnipotentClosed,RationalUnipotentHaar,WhittakerCoefficient}.lean`,
  `LanglandsTunnell/RankinSelberg/{Euler,EulerPolyProduct}.lean`, `MeasureTheory/HaarQuotientNormalizer.lean`
  (SET-AF104D), `NumberTheory/AdelicLevel/Countability.lean`,
  `NumberTheory/LSeries/DedekindZetaEulerProduct.lean`, `NumberTheory/NumberField/GlobalAddChar/Circle.lean`,
  `NumberTheory/NumberField/TateGlobal{IdeleNormValues,ContinuousIdeleNorm,NormSection}.lean`,
  `RepTheory/LocalLanglands/WhittakerRecursion.lean`.
* **Home**: `AutomorphicForm/Adelic/RankinSelbergEulerProduct.lean`, in the flat `Adelic/`
  rankin-selberg family, above `RankinSelbergQuotientIntegral`/`RankinSelbergTorusIntegral`/
  `RankinSelbergShellIndicator`/`RankinSelbergAnalyticity`.

### B — level-spherical eigenvectors and the cut projector

Two rows, **523** silo: `exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType` (435, 12
premises) — a cuspidal form that is an eigenfunction of right convolution by every level-spherical
test function of type `tys` has a **real** eigenvalue, common to all such test functions; and
`exists_idempotent_cutProjector_of_isCompact` (88, 2 premises) — the level-average and arch-type
projectors of SET-AF104 compose to one idempotent cutting the carrier onto the `U`-invariant
`archCut` piece.

Home `AutomorphicForm/Adelic/Cusp/LevelSphericalEigenvector.lean`, beside `ArchTypeProjector.lean`
and `SpectrumDensity.lean` (its two premises) and `Constituent.lean`.

### C — regular prolongations, and the `P¹` place-∞ formula

Four rows, **1,184** silo, two modules by subject:

* `AlgebraicCurve/RegularProlongationRetraction.lean` (580): the retraction of the
  regular-prolongation map onto the constant field's valuation subring (300), the adjoin criterion
  `RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic` (221), and the place-map/order
  agreement at good constant reduction (59);
* `AlgebraicCurve/P1/PlaceInftyReduction.lean` (604): the `P¹` degree formula
  `ord_placeInfty = ord_placeInfty + ∑ ord_placeOfPoint`, obtained by reducing each point place, with
  SET-AF103E's root-count lemma as the engine.

The two modules are one story — *places over a constant field extension, and how they compute* — but
two subjects: the prolongation construction is `AlgebraicCurve/RegularProlongation*` and the `P¹`
formula is `AlgebraicCurve/P1/`.

### D — the semisimple-representation criterion

Three rows, **615** silo. `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`
(495, 3 premises, 31 pin declarations): an `Ω`-representation of `Γ_ℚ` whose Frobenius traces and
determinants lie in a residue field `κ ↪ Ω` descends to a semisimple `κ`-model with the same kernel
and the same characteristic polynomials. Plus the two `ValuationSubring` leaves SET-AF103 §5 deferred
(`IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83, `charP_residueField_of_liesOverPrime` 37), whose
vocabulary `A.LiesOverPrime q`/`A.IsFrobeniusAt σ q` lives in `GaloisRep/Defs/`.

Home `GaloisRep/SemisimpleCriterion.lean`, beside `SemisimpleDescent.lean` (its premise) and
`Defs/`.

### E — the dictionary's points, and integrality from a differential

Two rows, **710** silo, two modules:

* `ModularCurve/ComplexPlaceDictionaryPoint.lean` (370): every place of the complex place dictionary
  is the point it was built from (`exists_pt_eq_of_mem`) — the injectivity the dictionary needs, and a
  row deferred by both SET-AF103 and SET-AF104;
* `ModularCurve/X1/IntegralityDifferential.lean` (340, **15 premises**): a differential on the `X₁`
  function field whose `q`-expansion is that of a weight-2 cusp form is regular (and the element it
  comes from is integral) — the inverse of "a cusp form gives a regular differential", and SET-AF104E's
  consumer.

## 2. The scaffolds, and the definition layer this set had to port first

**The definition-layer item, landed by the manager before any order was written.**
`Definitions/Def_AutomorphicForm_HeckeEigenfunction` (120 pin lines) was **not** in the port —
`rg IsHeckeEigenfunctionOf` over `lean/FLTForHuman` returned nothing, while the Euler-product pin's
`S_` file names the predicate and its companions 20 times. So the port needed
`AutomorphicForm/Adelic/HeckeEigenfunction.lean`: `RightTranslationGroup`, `rightTranslationEmbed`,
`rightTranslationEmbed_smul_apply`, `levelRT`, `IsHeckeEigenfunctionOf`,
`agreesAwayFromFinite_of_level_eq` and `isHeckeEigenfunctionOf_zero_inhabitant`, at the pin's
statements. **7 ok / 0 / 0 / 0**, silent at the 200 k cap, built clean.

Two findings from that port, both worth carrying:

* **a `Definitions` module can collide with a declaration the port already has.** The pin's
  `uniformizerIdele` is already public at `NumberTheory/NumberField/TateGlobal/Defs.lean` with the
  pin's definition verbatim, so the module **imports** it (7 rows declared, the eighth substituted) —
  and the collision only surfaced because the Euler-product module imports *both* files:
  `environment already contains 'AutomorphicForm.uniformizerIdele'`. Two modules declaring one public
  full name are unimportable together and **no per-module gate sees it** (FR-0274); the collision
  probe is what catches it, and it caught this one before an order was written.
* **a pin wrapper's `open` list is pin plumbing.** The `charP_residueField` wrapper opens
  `AlgebraicGeometry`, `NeronModelInfra`, `GoodReductionJacobian`, `ModularCurve.IgusaScheme` … none of
  which exist in the port (`unknown namespace AlgebraicGeometry`). The statement needs none of them;
  only `IsLocalRing` (for `ResidueField`). So a scaffold carries the wrapper's statement and its
  *mathematical* opens, never its whole `open` line.

Seven scaffolds, all silent but for their `sorry`s:

| order | module | scaffold `check_port` | first-compile |
|---|---|---:|---:|
| A | `AutomorphicForm/Adelic/RankinSelbergEulerProduct.lean` | **1 ok** | 5 s |
| B | `AutomorphicForm/Adelic/Cusp/LevelSphericalEigenvector.lean` | **2 ok** | 4 s |
| C | `AlgebraicCurve/RegularProlongationRetraction.lean` | **3 ok** | 4 s |
| C | `AlgebraicCurve/P1/PlaceInftyReduction.lean` | **1 ok** | 3 s |
| D | `GaloisRep/SemisimpleCriterion.lean` | **3 ok** | 5 s |
| E | `ModularCurve/ComplexPlaceDictionaryPoint.lean` | **1 ok** | 4 s |
| E | `ModularCurve/X1/IntegralityDifferential.lean` | **1 ok** | 5 s |
| **total** | (+ `Adelic/HeckeEigenfunction.lean`, the definition layer: **7 ok**) | **12 ok / 0 / 0 / 0** | |

## 3. The pricing

`port_plan` on the twelve rows:

| figure | value |
|---|---:|
| raw `S_` lines | 4,413 |
| declaration lines | 4,112 |
| duplicate copies | 80 |
| boilerplate | 301 |
| distinct declaration groups | 205 |
| **already in the port (vetted)** | **282** |
| **net new math lines** | **3,750** |
| substitutions | 30 trusted / 2 suspect |

**The substitutions are real this time, and the tool found them.** Unlike SET-AF104 (where the "already
in the port" lines were mostly pin-private twins), 32 of this set's declarations are already public in
the port at hash-identical statements, and they cluster in two places: **twelve rows of the `P¹`
place-∞ pin are `AlgebraicCurve.DeuringNormResidue`'s** (`sigma`, `constEmb`, `sigmaFun`, the
`const_unique` block — 111 lines, byte-identical), and three of the `GaloisRep` pin's engine rows are
`DeligneSerre`'s (`isSemisimpleRepresentation_of_forall_exists_isCompl` 33, `charpoly_fin_two` 22,
`finrank_eq_one_of_ne_bot_of_ne_top` 16). The rest are small: 5 in the Euler-product pin, 7 in the
dictionary pin, 3 in the integrality pin.

The **two suspect substitutions** are `G`/`H` → `ModularCurve.JOneES.JOneESRat.A12` in the dictionary
pin (3 lines each) — the FR-0266 type-only `def` match, three separate `abbrev`s in the pin that the
parser reads as one. Read the bodies.

**A warning specific to this set**: A's and E's-second are pins whose *statements* are ~60–100 line
telescopes over 15–19 premise modules, so the `port_advise` "drags" and the `--with-defs` view are the
pricing instruments, not the silo. The silo prices the *proving*; the statements are the scaffolding
cost, and this set's are large.

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` **0 mismatch / 0 missing / 0 own** with every declaration `ok`; the engine gate as
the `statement_db` pin-vs-module declaration diff; `#print axioms` on every headline; the module's own
silent `lake env lean` loop and one locked `lake build`; `dedup.py --within`; `move_dead.py --dry-run`;
a heartbeat probe pair recorded and **not installed**.

Two policies carried from SET-AF104, both now house rules rather than this set's discoveries:

* **the heartbeat fix is the playbook's probe ladder at the low cap** (§3.5): module floor → statement
  vs proof → `one:<line>`/`keepafter:<line>` → `diagnostics`/`trace.Meta.isDefEq`; the cap is a
  bisector, never a budget; the 4 M lakefile bound is where a *residual* is accepted after the ladder,
  registered in CARRY-FORWARD, never as a `set_option` and never as a `sorry`. Two of this set's rows
  are in the same family as AF104E's (A's 55-declaration engine over a 19-premise statement, E's
  15-premise row), so expect at least one ladder.
* **the surface gate is run at review, by the manager**, on any module whose pin is mostly `private`:
  strip `private`, re-check, and read the three numbers (B's SET-AF104 counterpart went 16 → 29 this
  way). Do it for D, whose two leaves are one-line pins.

The set-level gates: the collision probe over all eight modules
(`lean/tmp/af105/collision-probe.lean`, which **already earned its keep** on the definition layer),
the wave build of the eight, a consumer zone per story that has one, and the shelf re-read.

## 5. Not cut — named and deferred (FR-0040)

* **`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` (951)** — the last single-row
  `ModularForm` story on the shelf; its premise set is the modular-forms integrality machinery, so it
  is an order of its own, not a shared set.
* **`ModularCurve.StarBank.hassePolyDescent` (407)** and
  **`ModularCurve.card_quotient_gamma0_le_dedekindPsi` (318)** with `ModularPolynomialData.eq_all`
  (75), `exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36), `rep_tateModule_jOne_comm` (24) — the
  modular-polynomial / `Γ₀`-index cluster; it splits by subject into two ~400-line orders, neither of
  which is worth a dispatch alone, so it waits for a set that wants the whole cluster.
* **The `TateCurve` rows** (`sOne_eq_tsum_xfun` 101, `pointX/pointY_zpow_mul` 22 + 22,
  `defectCoeff_zero` 13, and the two points-law leaves 471 + 247) — one subject, and the points-law
  pair carries the deferred definition layer SET-AF101 §7 named.
* **`ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem`'s neighbour** is not deferred any
  more (it is order E1); what remains of that family is the dictionary's *action*
  (`ComplexPlaceDictionaryAction`) if a later set needs it.
* The `NumberField.*` leaves (ten rows, ~1,600), `WeierstrassCurve.{stepCurve_stepSubgroup_two_eq}`
  (231) and `…veluQuotient…` (194), `MeasureTheory.Lp` (148), `M4aTorus.completedRayL_fe` (12,126) —
  unchanged from SET-AF104 §5.
* Withheld by the FR-0044 guard: the same four rows (327 / 283 / 126 / 95), each citing a pruned-set
  premise.

## 6. The landing

**A landed (2026-11-27).** `AutomorphicForm/Adelic/RankinSelbergEulerProduct.lean`, **1,462 lines**,
**50 declarations, 0 `sorry`** — the pin's 1,381-line, 55-row engine in the subject namespace
`AutomorphicForm.RankinSelberg.EulerUnfold`, the row at the scaffold's name with proof
`EulerUnfold.main K`. **50 ok / 0 / 0 / 0**; engine diff 55 → 50 (the five `port_plan` substitutions,
verified against the pin's text, plus the pin's `solution`, which is the published row); axioms clean on
50/50; silent at the 200 k cap; locked build 21 s with 0 warnings from the file; `dedup` 0; `move_dead`
0/0. Heartbeat probe **silent 80,000 / fails 40,000** — and the statement-vs-proof rung is the
interesting number: with `main`'s proof `sorry`'d the module reads at **20,000**, so the whole cost is
one `isDefEq` at the `multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one`
application in the *proof*, not the 78-line telescope. No residual; nothing installed.

The one policy item: the module carries `set_option linter.style.haveILetI false` in its header. Its
pin binds seven *real* local instances with `haveI`/`letI` (`SecondCountableTopology`, `IsHaarMeasure`,
the two `rationalCentreUnipotentHaar` ones, `Countable (HeightOneSpectrum)`, `Countable (Ideal)`,
`pins.nS`) and the linter's rewrite would drop them, so this is the AF103B/AF104A house practice and it
stays — but note the contrast with order B, whose worker scoped the same option to the *one* helper that
needs it: where the sites are few, scope; where the pin's whole proof style is instance-local, the
header is the honest place.

**B landed (2026-11-27).** `AutomorphicForm/Adelic/Cusp/LevelSphericalEigenvector.lean`, **589 lines**,
**19 declarations (2 public + 17 `private`)**, 0 `sorry`; **2 ok / 0 / 0 / 0**; engine diff over the four
wires 23 pin rows → 19 declarations, **19 by hash, 0 unaccounted**; axioms clean; silent with **8.3×
headroom** (fails at 23,000); locked build clean; `dedup` 0; `move_dead` 0/0; the two substitutions
(`eq_of_glArch_eq_of_glFin_eq`, `commute_of_glArch_eq_one_of_glFin_eq_one`) read against the pin.

**The surface gate ran and declined to promote, which is the decision worth recording.** With `private`
stripped the module reads **19 ok / 0 / 0 / 0**, but the block is this one pin's private prelude
(`shiftRange` and its membership lemmas, the coset-sum and adjoint steps,
`exists_real_of_cuspKFiniteSubmodule_le`) with **no second consumer** in the pin or the port — so the
pin's `private` is the faithful visibility and the 19/19 engine diff is the completeness evidence.
Contrast SET-AF104B, where the engine was the shared prelude of *three* pins and promotion was §5's
"written once, importable". The distinction is the sharing, not the count; it is recorded in the module
header so a later reader sees a decision rather than an omission.

**D landed (2026-11-27).** `GaloisRep/SemisimpleCriterion.lean`, **603 lines**, **29 declarations,
0 `sorry`**, **29 ok / 0 / 0 / 0**; engine diff over the three `S_` pins 33 → 29 (26 by hash, 3
unaccounted = the two leaves and the headline, all three `ok` against the wrappers); axioms clean on
29/29; silent at 200 k with the module floor between 10 k and 20 k; locked build clean; `dedup` 0;
`move_dead` 0/0. The pin has **no `private` rows**, so the surface gate is vacuous here.

D found a **fourth substitution** the order did not name, and the right response was to keep it:
`finite_range_of_factorsThroughFiniteLevel` is already public in `GaloisRep/Prelude.lean`, but stated
`Finite (MonoidHom.range ρ)` against the pin's `S_` copy's `linRep` spelling, so the module declares the
`S_`-shaped row under the rectified name `GaloisRep.finite_range_linRep` — and `check_port` reads it
**`ok` by content hash** against `S_…:241`. FR-0274 is why the pin's name could not be reused; the
rectified name is why both statements can live.

Adding the *record* of that rename turned out to be the day's instrument lesson (**FR-0308**): a `pin:`
row in `spec/decl_markers.tsv` routes the declaration through the **direct** diff, which re-compares the
text as spelled, and the module went from `29 ok` to `28 ok / 1 mismatch` for a row the content tier had
already placed. Markers are for rows the checker cannot place; a row it has placed needs no marker, and
the rename is recorded in the module header where a reader looks. Row removed, `--strict-markers` back to
29 ok.

**C landed (2026-11-27).** `AlgebraicCurve/RegularProlongationRetraction.lean` (**631 lines**, 16
declarations, **16 ok / 0 / 0 / 0**) and `AlgebraicCurve/P1/PlaceInftyReduction.lean` (**531 lines**, 23
declarations, **23 ok / 0 / 0 / 0**); both `sorry`-free, silent at 200 k, locked builds clean with 0
warnings, axioms clean on 39/39, `dedup` 0, `move_dead` 0/0, collision probe (both modules together)
silent. Engine diffs: 19 pin rows → 16 (16 by hash) and 35 → 23 (23 by hash), **0 unaccounted** in both.

This order is the set's **substitution win**, and it is the one to read before pricing a `P¹` pin again:
**11 of the 12 `DeuringNormResidue` rows the order named are imported verbatim**, so a 604-line pin
lands at 531 lines with 23 declarations. Two further port rows were found by `rg` and kept as one-line
aliases (`ord_placeInfty_eq_neg_intDegree`, `ord_placeInfty_algebraMap` →
`RationalFunctionField.ord_placeInfty*`).

**The twelfth is the set's one deviation, and it is a new failure mode of the substitution tooling**:
`polyEmb`'s statement in the port is a bare `A[X] →+* O`, so `port_advise` prices it as a match — but the
ported *body* is built through the general reduction's `hX` and needs an `Algebra (RatFunc K) (RatFunc E)`
instance that mathlib v4.34 does not provide (verified: `inferInstance` fails, nothing in the port
supplies it). So the pin's three lines are transcribed, and the phrase to carry is **"statement matches,
body not instantiable at these parameters"** — FR-0266's read-the-body rule has a second half, and the
tool cannot see either of them.

Two proof-side drifts that no statement gate can see went into the friction log: **FR-0309** (a
`Commute`-shaped proof argument — `(fun f a ↦ mul_comm _ _)` — is only `defeq` at default transparency,
so `rw`/`simp` report "pattern not found" in a goal that *is* the pattern; cure `Commute.all`) and
**FR-0310** (inside a subject namespace named after the theory, a bare `residue_eq_zero_iff` resolves to
the port's own index-named lemma before `IsLocalRing`'s — qualify the mathlib name).

The 300-row is the set's **predicted non-event**: its pin carries `set_option maxHeartbeats 6400000`,
and the port needs under 200 000 — the module is silent at 80 000, so the pin's ceiling was ~32× its
need on the port's import graph. No ladder was needed and none was run.

**E landed (2026-11-27).** `ModularCurve/X1/IntegralityDifferential.lean` (**427 lines**, 5
declarations, **5 ok / 0 / 0 / 0**) and `ModularCurve/ComplexPlaceDictionaryPoint.lean` (**460 lines**,
38 public + 2 `private` + 9 scoped instances, **38 ok / 0 / 0 / 0**); both `sorry`-free, silent, one
locked build of both, axioms clean on 43/43, `dedup` 0, `move_dead` 0/0.

E's heartbeat work is the set's second **predicted non-event** and the better half of the two: the
integrality pin carries `synthInstance 1600000` + `maxHeartbeats 6400000`, and the port retires both
**by two direct terms, not by a bound** — `Algebra.IsAlgebraic.isSeparable_of_perfectField` for the
`hSEP := inferInstance`, and `DivisionSemiring.to_moduleIsTorsionFree` for the `IsTorsionFree` search
behind `Module.finrank_pos`. Measured: the pin's text times out at the default 20,000, passes at 40,000
and at 1.6 M; the port's terms are silent at the default and the module is silent at the 200 k edit
loop. The brick recipe did the whole job, and nothing is installed.

**The `G`/`H` suspect pair was a real FR-0266 catch, and the half that was right is the interesting
half.** `port_advise` matched *both* to `JOneES.JOneESRat.A12`: `G` is the pin's restricted `E₄³`,
which *is* `A12` — a genuine body-only substitution (a one-line body was enough, since the statement
matched). `H` is `restrict (le_SL Γ) Δ`, the **discriminant**, and the pin's `coe_H` is `rfl` for it and
would be **false** for `A12` — so `H` is transcribed from the pin's body. A name-anchored tool cannot
tell a two-object pair from one, and this is the sharpest instance the project has: the same advice was
right for `G` and wrong for `H`, on adjacent lines.

## 6.1 The landing table

| order | module(s) | lines | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---:|---|---|
| def | `Adelic/HeckeEigenfunction.lean` (manager) | **172** | **7 ok / 0 / 0** | 7 clean | — | — | silent at 200,000 |
| A | `Adelic/RankinSelbergEulerProduct.lean` | **1,462** | **50 ok / 0 / 0** | 50 clean | 0 | 0 / 0 | 80,000 / 40,000 (proof-side, one `isDefEq`) |
| B | `Adelic/Cusp/LevelSphericalEigenvector.lean` | **589** | **2 ok / 0 / 0** (19 on the surface, **not** promoted) | 2 clean | 0 | 0 / 0 | 200,000 / 23,000 (8.3×) |
| C | `AlgebraicCurve/RegularProlongationRetraction.lean` | **631** | **16 ok / 0 / 0** | 16 clean | 0 | 0 / 0 | 80,000 / 60,000 |
| C | `AlgebraicCurve/P1/PlaceInftyReduction.lean` | **531** | **23 ok / 0 / 0** | 23 clean | 0 | 0 / 0 | 40,000 / 20,000 |
| D | `GaloisRep/SemisimpleCriterion.lean` | **603** | **29 ok / 0 / 0** | 29 clean | 0 | 0 / 0 | 20,000 / 10,000 |
| E | `ModularCurve/X1/IntegralityDifferential.lean` | **427** | **5 ok / 0 / 0** | 5 clean | 0 | 0 / 0 | silent at 200,000 (terms, never a bound) |
| E | `ModularCurve/ComplexPlaceDictionaryPoint.lean` | **460** | **38 ok / 0 / 0** | 38 clean | 0 | 0 / 0 | silent at 200,000 |
| **set** | **7 new modules + 1 definition layer** | **5,075** | **170 ok / 0 / 0 / 0** | 170 clean, no `sorryAx` | 0 | 0 / 0 | **0 recorded edit-loop gaps** |

The set-level gates, run by me on the landed tree: **wave build** `Build completed successfully (5292
jobs)` with no warning line from any of the eight modules; the **collision probe** over all eight
silent; `spec/SetAF105Consumer.lean` with four zones, each a real executed consequence (A+B composed —
both projectors fix the level-invariant `archCut` vectors; E1's dictionary surjectivity; C1's
prolongation with prescribed integers; D's semisimple model with the same kernel).

**This is the first set in the column with no edit-loop gap at all**: every module is silent at the
200 k detector, the worst headroom being B's 8.3×, so nothing was registered in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) and no ladder had to be accepted — the two pin ceilings
(C's 6.4 M and E's 6.4 M + 1.6 M `synthInstance`) were retired by direct terms and by an import graph
that simply needs less. That is the outcome the last set's policy was written for.

## 6.2 Plan vs actual

| figure | plan (§0/§3) | actual |
|---|---:|---:|
| rows / orders | 12 / 5 | 12 / 5 |
| silo | 4,413 | 4,413 |
| written lines | net-new 3,750 | **5,075** (+35%) |
| modules | 7 (+1 definition layer) | 7 (+1) |
| checked declarations | ≈206 (from the WOs' per-order estimates) | **170** |
| recorded edit-loop gaps | 0 predicted, ≥1 expected | **0** |

Two honest corrections:

* **the `port_plan` net-new figure under-predicted the writing by 35%, for the third set running** —
  and this time not because the substitutions were fake (they were real: 30 of them) but because the
  *statements* are the cost in this set: A's 55-row pin is a 1,462-line module whose declaration
  bodies are mostly the pin's own, and the Def layer (172 lines) was not in the estimate at all. The
  silo, again, was the accurate predictor (4,413 against 5,075 written, 15%).
* **the `check_port` predictions ran ~20% high** because each order's "expected size" was computed as
  "pin rows less what the pins share", and the substitution pass removed more than that: C's `P¹` pin
  lost 11 rows to `DeuringNormResidue`, A lost 5, D lost 4, E lost 10. The lesson is the one the last
  set recorded from the other direction: **a `check_port` size is a measurement, never a prediction** —
  so the brief's per-order estimates should be read as "report the exact diff", which is what they say.

One prediction that *did* hold, and it is the reason this set is worth its size: **8 rows became ready
(4,309 silo)** and **two leaves left the leaves block** — the first time since SET-AF103 that a set has
taken rows *out of* the leaves, and here it was D's two one-line `ValuationSubring` leaves, exactly as
SET-AF103 §5 predicted when it deferred them.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af105_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` (corrected read) | 314 / 170,417 | **302 / 166,004** |
| ready rows | 22 / 6,379 | **20 / 6,395** |
| leaves | 18 / 15,127 | **16 / 15,007** |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is **−12 nodes / −4,413 lines**: the twelve rows are the whole line delta, and the twelfth
node is the **definition-layer module** (`Def_AutomorphicForm_HeckeEigenfunction`), which carries no
silo. The leaves block moved for the first time in two sets: −2 rows / −120 lines, D's two
`ValuationSubring` leaves.

**Eight rows became ready (4,309 silo), and they are this set's payoff:**

* `ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq` (**1,236**, 8 premises) — C's
  consumer;
* `ModularCurve.exists_frickeAlgEquiv_xHFunctionFieldBar` (**1,105**, 5) — C's other consumer;
* `AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent`
  (**650**, 8) — B's consumer (the eigenvector result applied to a cusp constituent);
* `AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction` (**629**, 15) — C's;
* `AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed`
  (**232**, 5) and `…exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials`
  (**227**, 6) — B's and E's;
* `AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed`
  (**196**, 2) and `AlgebraicCurve.exists_valuationSubring_section_of_constantField_valuationSubring`
  (**34**, 1) — C's.

## 8. What the set leaves behind

The definition layer is now in the port for any future eigenfunction argument
(`AutomorphicForm/Adelic/HeckeEigenfunction.lean`, 7 rows at the pin's statements), and seven subject
homes: the Euler product beside the Rankin–Selberg family, the level-spherical eigenvector beside the
two projectors, `RegularProlongationRetraction.lean` and `P1/PlaceInftyReduction.lean` for the
`AlgebraicCurve` place calculus, `GaloisRep/SemisimpleCriterion.lean` for the `κ`-model descent, and
the two `ModularCurve` rows the last two sets deferred.

Four things worth carrying beyond the files: **the substitution tool has two failure modes, not one**
(FR-0266's type-only `def` match, and E's "statement matches, body not instantiable at these
parameters"); **a `pin:` marker re-diffs a statement the content tier had already placed** (FR-0308,
found by trying to document a rename); **`Commute`-shaped proof arguments are only defeq at default
transparency** (FR-0309) and **a subject namespace named after the theory shadows mathlib's lemmas**
(FR-0310); and **the surface gate is a decision, not a rule** — SET-AF104B promoted its engine because
three pins shared it, SET-AF105B kept its block private because one pin owns it, and both are recorded
in their module headers.
