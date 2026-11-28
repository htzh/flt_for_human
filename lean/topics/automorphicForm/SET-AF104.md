# SET-AF104 — the carrier's projectors and density, the Rankin–Selberg `s`-part integral, the Iwasawa quotient integral, and the genus of `X₁`

**Status: LANDED (2026-11-26).** Five orders, eleven rows, 5,669 silo, six new modules, **208 checked
declarations, none `sorry`-bearing, one recorded edit-loop gap** (§6, §6.1); the shelf re-read is §7 and
the plan-vs-actual §6.3. The set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. It takes the
**whole AF-subject head of the post-SET-AF103 shelf** — the two projector/density stories that
SET-AF103C/D made ready, the Rankin–Selberg row SET-AF103 §5 deferred as "a set of its own", and the
two quotient-integral rows — plus the `ModularCurve` `X₁` block that SET-AF103B's ramification bound
made ready.

| # | order | rows | silo | module(s) |
|---|---|---|---:|---|
| A | the arch-type projector on the carrier | 1 | 1,219 | `AutomorphicForm/Adelic/Cusp/ArchTypeProjector.lean` (new) |
| B | the level-invariant `archCut` vectors generate the carrier | 4 | 1,221 | `AutomorphicForm/Adelic/Cusp/SpectrumDensity.lean` (new) |
| C | analyticity and positivity of the Rankin–Selberg `s`-part integral | 1 | 1,194 | `AutomorphicForm/Adelic/RankinSelbergAnalyticity.lean` (new) |
| D | two quotient-measure computations (Iwasawa; a normalizer translate) | 2 | 714 | `AutomorphicForm/Adelic/IwasawaQuotientIntegral.lean` (new), `MeasureTheory/HaarQuotientNormalizer.lean` (new) |
| E | the genus of `X₁`, its `j`-ramification over `ℚ̄`, its regular differentials | 3 | 1,321 | `ModularCurve/X1/GenusBound.lean` (new) |
| **total** | | **11** | **5,669** | 6 new modules |

A is the single biggest ready row of the shelf and C the second, so two of the five orders carry one
row each; B is the four-row consumer block of SET-AF103C/D; D is the two quotient-measure rows; E is
the three-row `X₁` invariant block.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json --selfcheck
# then the corrected read, with the 21 false ported markers subtracted:
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json $(printf -- '--unport %s ' <the 21 selfcheck names>)
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **325 / 176,086** |
| ready rows | 29 / 9,804 |
| leaves | 18 / 15,127 |
| withheld (FR-0044 guard) | 4 / 831 |

This is SET-AF103 §7's after-the-landing read reproduced exactly, so nothing has landed since; the 21
`--selfcheck` false ported markers (MD-005's phi-refactor block and MD-007) are the same set, and every
row below is on the **corrected** shelf. Raw JSON: `lean/tmp/af104/shelf_af104_read.json`.

The shelf's head is a chain of consumers of the last three sets: A, B's four rows, E's three rows and C
all became ready because of SET-AF101/102/103. That is why this set is cut from the head rather than
from the leaves; the leaves block is untouched (18 / 15,127) and is named in §5 where it is deferred.

## 1. The stories

### A — the arch-type projector on the carrier

`AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector` (**1,219** silo, 8 premises,
100 pin declarations): for a number field `F`, a slab fundamental domain `Φ₀`, a modulus `σ` and a
Hecke character `ξ` of modulus `σ`, and an archimedean type family `tys`, there is
`E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)` with `E.comp E = E` which fixes
the `archCut tys` vectors, sends every carrier vector to a finite-level translate of an `archCut tys`
vector, leaves every closed cuspidal subrepresentation invariant, and commutes with every cusp lift
(`IsCuspLift` for a right translate by a row isometry, and for a right translate by
`g ∈ finiteAdelicGL2Subgroup F`).

* **Definition layer**: `Definitions/Def_AutomorphicForm_CuspidalSpectrumSubrep` only, ported
  (`Cusp/{SpectrumCarrier,SpectrumSubrep,SpectrumLift,SpectrumCarrierAPI}.lean`).
* **Premises**, all ported: `Cusp/SpectrumApproximation.lean` (SET-AF103C),
  `Analysis/Group/AverageOperator.lean`, `MeasureTheory/IsotypicConvolution.lean`,
  `Cusp/SpectrumTranslation.lean`, `ArchCutSpan.lean`, `MaximalCompactFactors.lean`,
  `IsotypicArchType.lean`, `Cusp/SpectrumCarrierAPI.lean`.
* **Home**: `AutomorphicForm/Adelic/Cusp/` — the subject is the carrier's own endomorphism algebra,
  beside `SpectrumApproximation.lean` and `SpectrumSubcarrier`'s other consumers, and above every
  premise.

The pin's `S_` file is a **flattened public engine** (100 declarations, 98 of them public) whose first
half is a copy of `ArchInfra`'s `Kw`/`Kprod`/`inclArch` block — see §3.

### B — the level-invariant `archCut` vectors generate the carrier

Four rows, one story, **1,221** silo:

| row | silo | premises | def modules |
|---|---:|---:|---|
| `exists_idempotent_levelAverage_of_isCompact` | 274 | 6 | `CuspidalSpectrumSubrep` |
| `exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero` | 483 | 7 | `CuspidalSpectrumSubrep` |
| `exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt` | 363 | 7 | `CuspidalSpectrumCarrier`, `CentreCutSiegelSetAmple` |
| `CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent` | 101 | 1 | `CuspidalSpectrumCarrier`, `FactorizableTestFn` |

* the level average over a compact open `U = O ⊓ finiteAdelicGL2Subgroup F` is an idempotent that fixes
  the `U`-invariants, produces `U`-invariants, respects the closed cuspidal subrepresentations and
  commutes with the cusp lifts;
* every nonzero carrier vector pairs nontrivially with a `U`-invariant `archCut tys` vector
  (**separation**);
* under a Siegel-ample cover, a cuspidal vector in a cuspidal subrepresentation is approximated by one
  that is simultaneously level, `archCut tys` and in the subrepresentation (**density**);
* a cusp constituent meets the level `∩` `archCut` `∩` `M` piece trivially or sits inside `M`
  (**the constituent cut**).

**Home**: `AutomorphicForm/Adelic/Cusp/`, beside `SpectrumApproximation.lean` (its approximation
engine), `SpectrumIntegration.lean`, `SpectrumLift.lean` and `ConstituentSpine.lean`. It is the level
twin of A: same carrier, same conclusion shape, the projector built from `U` rather than from `tys`.

### C — the Rankin–Selberg `s`-part integral

`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery` (**1,194** silo,
13 premises, 36 pin declarations, **no private helpers**): there is `a < 1/2` such that on
`{s | a < s.re}` the defining double integral of the `s`-part integral is finite, the map
`s ↦ RankinSelberg.sPartIntegral K S pins x x (φ s) w e₁ e₂` is analytic, and on the real axis its value
is real and positive.

* **Definition layer**: 13 `Definitions/Def_*` modules, **all ported** —
  `AutomorphicForm/{RankinSelbergQuotientIntegral,ProductionPinsGeneral,AdelicMaximalCompact,
  InducedSection,EtaFamily,RowIsometryInvariance,ArchDerivCasimir}.lean`-equivalents in
  `AutomorphicForm/Adelic/`, `NumberTheory/NumberField/IdeleProductMeasure.lean`,
  `NumberTheory/NumberField/IdeleClass/Vocab.lean`, `NumberTheory/NumberField/AdelicTraceFin.lean`,
  `NumberTheory/AdelicDock/LocalEmbedding.lean`, `RepTheory/LocalLanglands/UnramifiedWhittaker.lean`.
  Verified by import: the scaffold compiles against them.
* **Premises**, all ported: `RankinSelbergTorusIntegral`, `NumberField/IdeleSPartIntegral` (×3),
  `StandardAddChar/GlobalAndInfinite`, `WhittakerCoefficient`, `TateGlobal/FujisakiC3`,
  `AdelicLevel/Countability`, `AdelicModulus`, `RankinSelbergShellIndicator`,
  `Analysis/SpecialFunctions/Pow/Decay`, `MeasureTheory/ParametricIntegral`.
* **Home**: `AutomorphicForm/Adelic/RankinSelbergAnalyticity.lean`, in the flat
  `AutomorphicForm/Adelic/` rankin-selberg family (`RankinSelbergQuotientIntegral`,
  `RankinSelbergTorusIntegral`, `RankinSelbergShellIndicator`, `RankinSelbergSection`), above all of
  them. SET-AF103 §5 called this row "a set of its own — one order, one module"; it is taken here as
  one order with that full wall time.

The statement is a **~100-line binder telescope** with one leading `let α := …`; it is transcribed
verbatim from the wrapper (the scaffold compiles it in 6.5 s at the 200 k cap, so the *statement* is
cheap — the cost is the proof).

### D — two quotient-measure computations

**D1** `AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa`
(**453** silo, 8 premises, 26 pin declarations, no private helpers): the Haar-quotient measure of
`rationalCentreUnipotent K` is a constant times the Iwasawa-coordinate iterated integral
`∫⁻ z in D, ∫⁻ t, ∫⁻ k, f (z·t·k) * ‖t‖⁻¹`, for `f` right-invariant under the subgroup and `D` a
fundamental domain of the principal idèles. Home
`AutomorphicForm/Adelic/IwasawaQuotientIntegral.lean`, beside `RationalCentreHaar`,
`RationalUnipotentHaar`, `UnipotentQuotient`, `BorelHaarDisintegration`; premises are
`BorelHaarDisintegration`, `RationalUnipotent{Closed,Haar}`, `MeasureTheory/HaarQuotient{Fubini,Density}`,
`AdelicLevel/Countability`, `TateGlobal/FujisakiC3`.

**D2** `HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer`
(**261** silo, 2 premises, 16 pin declarations, no private helpers): for `b` in the normalizer of a
closed subgroup `H` with conjugation scaling the Haar measure by `D`, the quotient integral of
`h q.out * Φ (m q.out)` is `(∑' n, Dⁿ Φ n) * ∫_{m = 0} h q.out`, where `m` is the `ℤ`-valued cocycle
with `m (b * g) = m g + 1`. Home `MeasureTheory/HaarQuotientNormalizer.lean` — a **`MeasureTheory`**
module, because the statement is about `HaarQuotient.measure` alone: putting it in an
`AutomorphicForm` module would invert the layering (SET-AF101W4's lesson). Its two premises both live in
`MeasureTheory/HaarQuotient.lean`.

The two rows are one story — *the quotient measure is an iterated integral in adapted coordinates* —
which is why they share D; they are two modules because the second is `MeasureTheory`-layer.

### E — the genus of `X₁`, its `j`-ramification over `ℚ̄`, its regular differentials

Three rows on `F = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)`:

| row | silo | premises |
|---|---:|---:|
| `ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_…_algebraicClosure` | 346 | 9 |
| `two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le` | 812 | **26** |
| `mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion` | 163 | 15 |

* the `jq`-ramification over `ℚ̄` — `P.ord y ≤ 3`, `P.ord (y - 1728) ≤ 2`, `P.ord (y - a) ≤ 1`
  (`a ∉ {0, 1728}`) at every place — which is SET-AF103B's `ℂ`-statement pushed through the constant
  field extension;
* the Riemann–Hurwitz count `2·genusFF + (fibre counts over 0, ∞, 1728) ≤ [F : ℚ̄(y)] + 2`;
* a regular differential recognised from its `q`-expansion.

**Home**: `ModularCurve/X1/GenusBound.lean`, beside `JqRamification.lean` (its premise) and the
`X1/FunctionField*` covers. The **26-premise** genus row is the set's shape risk: it is the largest
premise count on the shelf and it is why the order is sized at 1,321 rather than split.

## 2. The scaffolds

Six modules exist before any order starts, each with its header prose, its `spec-pin:` wires (the
`Theorems/` wrapper and the `P2M/Sol/S_` file of every row), a narrow import list, and the **headline
declarations only**, at the wrapper's statement and the published name, body `sorry`. All six
elaborate at the 200 k cap, silent but for their `sorry`s:

| order | module | scaffold `check_port` | first-compile cost |
|---|---|---:|---:|
| A | `AutomorphicForm/Adelic/Cusp/ArchTypeProjector.lean` | **1 ok** | 3 s |
| B | `AutomorphicForm/Adelic/Cusp/SpectrumDensity.lean` | **4 ok** | 5 s |
| C | `AutomorphicForm/Adelic/RankinSelbergAnalyticity.lean` | **1 ok** | **6.5 s** (the 100-line telescope) |
| D1 | `AutomorphicForm/Adelic/IwasawaQuotientIntegral.lean` | **1 ok** | 4 s |
| D2 | `MeasureTheory/HaarQuotientNormalizer.lean` | **1 ok** | 2 s |
| E | `ModularCurve/X1/GenusBound.lean` | **3 ok** | 6 s |
| **total** | | **11 ok / 0 / 0 / 0** | |

Two scaffold findings worth carrying:

* **`FLTForHuman.Analysis.SpecialFunctions.Pow.Decay` had no `.olean`** (only `.olean.hash`/`.trace`
  — the FR-0301 signature of a killed build). A `lake env lean` of any module importing it dies with
  `object file … does not exist`, which reads like a wrong module name and is not: the source is
  right, the artefact was missing. `flock`ed `lake build` of the module fixed it (11 s). Check
  `.olean` existence before believing an import error on a module that has always built.
* Building a scaffold from the **wrapper** rather than from the `S_` file is what made C cheap: the
  wrapper is the pin's own statement copy (165 lines) and the `S_` file's 1,194 lines are the proof.
  The generator is `lean/tmp/af104/scaffold.py`; it strips the pin's `attribute [-instance]` /
  `[-simp]` walls and rewrites the `:= by p2m_exact_reverting …` tail to `:= by sorry`, nothing else.

## 3. The pricing

`port_plan` on the eleven rows:

| figure | value |
|---|---:|
| raw `S_` lines | 5,669 |
| declaration lines | 5,220 |
| duplicate copies | 227 |
| boilerplate | 449 |
| distinct declaration groups | 263 |
| **already in the port (vetted)** | **615** (608 tier 1 / 7 tier 3) |
| **net new math lines** | **4,378** |
| substitutions | 69 trusted / 5 suspect |

Unlike SET-AF103 (2,060 of 5,203 already in the port), this set is **mostly new**: the AF rows are
pins whose engines are earlier pins' *conclusions*, not their private preludes. The in-port 615 is
concentrated in E (`mem_of_ord_nonneg` 62, `degree_eq_sum_support` 50) and the two cusp-lift engine
rows (`inclArch_entry` 33, `exists_mem_norm_sub_lt` 18).

**The set's one real dedup block** is the 9-name / 167-line prelude shared by A's pin and
`exists_mem_archCutSubmodule_…`'s pin (`Kprod`, `inclArch`, `inclArch_mulSingle`, `inclArch_entry`,
`archComponent_inclArch`, `continuous_inclArch`, `continuous_adelicArchGLIncl`,
`commute_archRowIsometryInclAt₀`, `injective_rowIsometryInclAt₀`) — **every one of them is already
public in `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean`** (A: 4 copies across 3 pin
files; `port_advise` prices 98 lines of A as in-port for this reason). The pin's copies are
transcribed only where the port's statement differs (`commute_of_glArch_eq_one_of_glFin_eq_one` in A
vs the port's `…_of_glFin_eq_one` in `Cusp/ConstituentSpine.lean`: same conclusion, binder spelling —
take the wrapper's); everything else is an import.

The 13-line `continuous_diagOne` is shared by C's and D1's pins and is **public in the port**
(`AutomorphicForm.SPart.continuous_diagOne`, `AutomorphicForm/Adelic/ShellMeasureIntegral.lean`) — the
two orders import it.

**A sixth false-positive shape, found on this set and worse than the five suspects**: E's pin writes
its Riemann–Roch hypotheses as `_pkg` rows of the shape `haveI := …; FunctionFieldRiemannRoch k F ∧
ConstantsAreBase k F`, and `port_advise` offers them as *already in the port* against
`DegreeOnePrimes.finiteDimensional_fractionRing` — because the parser's statement view collapses the
`haveI` prefix, so any `haveI _; (…)`-shaped port theorem matches. There is no shared mathematics
there: each `_pkg` row is a genuine one-line call of an `AlgebraicCurve` assembly and must be declared
(the `RiemannHurwitzCount.Package` block is 812's own API prelude). Read every `haveI`-headed
substitution's pin body.

The **five suspect substitutions** are the parser's type-only `def` matches, and FR-0266 applies:
`iota → complexEmbedding` (6 lines), `Kprod → GroupTheory.BassSerre.Gp` (3 × 3 lines — the same
`abbrev` name as a `def … : Prop`-shaped match, not the same object), `pinsOn →
AutomorphicForm.CuspidalSpectrum.fdPins` (3). Read the body before believing any of them; `Kprod`
in particular is `∀ w : InfinitePlace F, Kw F w`, which the port has as `ArchInfra.Kprod`.

**`check_port` sizes are not the order sizes** and are measured at landing (§6), never estimated: a
pair of pins sharing one engine gives `check_port` = distinct engine rows + headlines, and a mostly
`private` pin gives its public rows only. Expected shapes: A ≈ 98 (its pin is a flat public engine),
B ≈ 15–20, C ≈ 36, D1 ≈ 26, D2 ≈ 16, E ≈ 40 + 13 + 9.

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` **0 mismatch / 0 missing / 0 own** with every declaration `ok`; the engine gate as
the `statement_db` pin-vs-module declaration diff; `#print axioms` on every headline; the module's own
silent `lake env lean` loop and one locked `lake build`; `dedup.py --within`; `move_dead.py --dry-run`;
a heartbeat probe pair recorded and **not installed**.

The set-level gates, run by the manager after all five orders land:

* **the name-collision probe** `lean/tmp/af104/collision-probe.lean` (imports all six new modules;
  must print nothing) — FR-0274: no two modules may declare the same public full name, and no gate
  sees it;
* a shelf re-read (§7);
* one consumer zone in `spec/` with a real cross-module composition per story that has one.

The review harness from SET-AF102 (`lean/tmp/af102/review.py`) takes any module path and runs all the
per-module gates but the build; copy it to `lean/tmp/af104/review.py` and use it.

**The heartbeat policy this set had to settle (E, 2026-11-26).** Two of E's pins carry the option the
port never carries — 346's `solution` and `ord_sub_algebraMap_le_one_algebraicClosure` sit under
`set_option maxHeartbeats 6400000` + `synthInstance.maxHeartbeats 1600000`, 812's file under
`3200000` + `1600000` — and with the options dropped the declarations exceed the 200 k edit loop even
after the pin's `have`-blocks are hoisted into `private` helpers. The decision, recorded here because it
is the set's one policy call:

* **no `set_option maxHeartbeats`, no `set_option synthInstance.maxHeartbeats`, no `sorry`.** The
  pin's number is a *ceiling*, not a usage; and a headline with a `sorry` defeats the set (the tree is
  `sorry`-free and `#print axioms` is the gate that proves it).
* **the shipping bound is the lakefile's 4 M**, not the 200 k detector: `lean/lakefile.lean:7-12`
  ships `⟨`maxHeartbeats, (4000000 : Nat)⟩`, so `lake build <module>` gives every declaration 4 M. A
  declaration that passes 4 M and fails 200 k is a **recorded discipline gap**, not a build failure —
  SET-AF103A's `main` (silent at 2 M) is the standing precedent, and its entry in
  [CARRY-FORWARD.md](../../CARRY-FORWARD.md) is the shape this set's gaps take.
* **the fix is run on the playbook's probe ladder at the low cap, not by escalating caps**
  (playbook §3.5). **Superseded 2026-11-27 (FR-0337):** the playbook now opens §3.5 with *never measure a
  blow-up* — the *downward* ladder below is withdrawn, and only the two isolation probes (stub one proof;
  stub the module floor) remain. The text is kept as the record of what this set did.
  The old practice was: the *downward* ladder `40000 / 20000 / 10000 / 5000 / 1000` one run per value to
  localise the stuck step; the **module floor** (every theorem proof `sorry`, statements/`def`s/
  instances verbatim) to decide in one run whether the cost is in the types at all; then
  statement-vs-proof on the suspect, then the `one:<line>`/`keepafter:<line>` isolation pair (the
  module's `.olean` exists, so no scratch is needed), then `diagnostics true` / `trace.Meta.isDefEq` at
  a tiny cap to name the subterm. The classification decides the fix: instance *search* → the brick
  recipe (`FiniteDimensional ↥ℂ⟮t⟯ K`, `Finite (K ≃ₐ[↥ℂ⟮t⟯] K)` are search goals — bind them with
  `haveI : <goal verbatim> := inferInstanceAs (…)`); instance *terms* compared by an argument check →
  one syntactic form, which changes the statement and is therefore my decision (a registered `own:`
  deviation), not the worker's; a genuine proof cost → the pin's own `have`-blocks cut into private
  lemmas, each **silent at the low cap** and summing below the removed one.
* **the cap is a bisector, never a budget** *(also superseded, FR-0337: a report carries no ladder at
  all)*: the acceptance test is "does it fit `timeout N` at cap
  N", so what the report carries is the ladder *both ways* (which values fail, which first passes),
  the `-- PROBE` label → attribution and the counter's named subterm — never an ascending search for
  the minimum passing cap, which measures a number nobody needs. Only a residual that survives steps
  1–5 is accepted against the 4 M shipping bound, and then as a recorded gap.

## 5. Not cut — named and deferred (FR-0040)

* **`ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem` (370)** — deferred a second time (it
  was SET-AF103 §5's deferral too): its subject is the complex place dictionary's point
  identification, and a set that takes it should take the dictionary's remainder. It does not belong
  to any of the five stories here.
* **`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` (951)**,
  **`ModularCurve.StarBank.hassePolyDescent` (407)**,
  **`ModularCurve.card_quotient_gamma0_le_dedekindPsi` (318)**,
  **`GaloisRep.exists_isSemisimpleRepresentation_…` (495)**,
  **`ModularCurve.ModularPolynomialData.eq_all` (75)**,
  **`ModularCurve.rep_tateModule_jOne_comm` (24)**,
  **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36)**,
  **`AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` (59)**,
  **`AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_…_of_reduction` (604)**,
  **`AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring` (300)**,
  **`AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic` (221)**,
  **`AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector`'s siblings in the
  `TateCurve` leaves** — each is a story of its own (the `StarBank`/`dedekindPsi` pair is modular-
  polynomial descent, the `GaloisRep` row is the semisimple-representation criterion, the
  `AlgebraicCurve` three are the regular-prolongation/place-map family that a `RegularProlongation`
  set should take whole).
* **`M4aTorus.completedRayL_fe` (12,126)** — the largest leaves row and an analytic class-field-theory
  subject of its own; not an AF-column row.
* The `NumberField.*` leaves (684 + 237 + 233 + 98 + 94 + 71 + 69 + 67 + 20 + 17), the `TateCurve`
  points-law pair (471 + 247) with its deferred definition layer, `WeierstrassCurve.{stepCurve_…}`
  (231) and `…veluQuotient…` (194), `MeasureTheory.Lp` (148) — unchanged from SET-AF101 §7 /
  AF102 §7 / AF103 §5; they are leaves, and this set does not touch the leaves block.
* **`ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` (83)** and
  **`charP_residueField_of_liesOverPrime` (37)** — still deferred to a `GaloisRep`-layer order
  (SET-AF103 §2): their vocabulary is `A.LiesOverPrime ℓ`, which would invert the layering inside a
  `FieldTheory` module.
* Withheld by the FR-0044 guard: the four rows of SET-AF103 §5 (`moduleFinite_and_free_padicInt_
  tateModule_jH` 327, `moduleFinite_padicInt_tateModule_jOne` 283,
  `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` 126,
  `Pic0.finite_torsion_of_isAlgClosed_of_charZero` 95) — each cites a pruned-set premise, so each is
  the prunable subject's work, not this column's.

## 6. The landing

*(to be filled as the orders land: per-order lines / checker / engine diff / axioms / dedup /
move_dead / probe, the set's `check_port` sizes, and the plan-vs-actual honesty section.)*

**A landed (2026-11-26).** `AutomorphicForm/Adelic/Cusp/ArchTypeProjector.lean`, **1,141 lines**
(scaffold 86), **74 ok / 0 / 0 / 0**; silent at the 200 k cap; 0 warnings under the build lock;
axioms clean on 74/74; `dedup` 0 clusters; `move_dead` 0/0. Engine diff: 101 wire rows → 75 module
declarations, **74 by hash + 1 by alpha**, 0 unaccounted; the 26 wire rows not declared are 24
substitutions (the `ArchInfra`/`EntryBall`/`ArchCompactOrbit`/`CuspSubcarrierDense` copies — the set's
one dedup block, as priced), 1 **inside-pin dead duplicate** (`ParchProof34.commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup`,
pin 660: a binder-permuted twin of pin 153 that no pin proof uses — I verified the three occurrences in
the pin are its definition, pin 153's definition, and a single call of the *153* shape, so it is a
§2.4 dedup, not a dropped node) and the `solution` row.

Two things the manager had to decide on A:

* **`set_option synthInstance.maxHeartbeats 480000` was load-bearing in one place** — `IsUniformAddGroup
  ↥W` before `FiniteDimensional.complete` — and the fix is the brick recipe mathlib itself uses
  (`haveI : IsUniformAddGroup ↥W := W.toAddSubgroup.isUniformAddGroup`), not an exemption. That
  declaration (`mem_of_apply_toCuspSubcarrier_eq`) is the module's only one without 2× headroom: silent
  at 200 k, fails at 180 k. Recorded, not installed.
* **review fix (mine)**: the worker had put `set_option linter.deprecated false` **file-wide** for two
  `|`-clause list lemmas whose statement slice covers their body (so the pin's deprecated
  `ContinuousLinearMap.one_apply`/`mul_apply` spellings cannot be renamed). A file-wide disable would
  hide a deprecated name used in *any* of the module's 1,100 proof lines, so I scoped it into the
  `section Lists` that holds the two lemmas: the module stays silent (so nothing else in it used a
  deprecated name), `check_port` re-reads 74 ok, and the two narrow options the pin's own style forces
  (`defProp` for the pin's `def avgOp`, `style.haveILetI` for its `letI`/`haveI` binders — the
  AF103B precedent) stay file-wide with their reasons in the header.

**B landed (2026-11-26).** `AutomorphicForm/Adelic/Cusp/SpectrumDensity.lean`, **1,198 lines**, 30
declarations (16 public + 14 private in the worker's cut, **29 public** after the surface gate below);
silent at the 200 k cap, 0 warnings under the build lock (18 s); axioms clean; `dedup` 0 clusters;
`move_dead` 0/0. Engine diff over 8 pin files: 50 pin rows, 30 module declarations → **28 by hash, 2 by
name, 0 unaccounted**; over the four `S_` pins alone, 46 rows = 30 written + 16 imported (274: 2, 483:
13 — the whole `ArchInfra` prelude plus `RowIsometryMonoidHom.{eq_inclArch,ideleNorm_det_eq_one}` and
`continuous_finEmbed` — and 363: 1).

**The set's one surface-gate promotion, and it moved the checked count 16 → 29.** The worker left the
pin's 14 `private` engine rows `private` (correct as a local default) and reported `check_port` 16,
offering the promotion as my decision. I ran the scoping recipe's §5 experiment — strip `private` from
the module's declarations and read the three numbers: **29 ok / 1 mismatch / 0 missing**, the single
`MISMATCH` being exactly the row the v4.34 `eLpNorm` drift forces
(`eLpNorm_weightedMeasure_sq_le` carries an added `AEStronglyMeasurable` hypothesis, so its statement
cannot be the pin's). So 13 rows were promoted — pin-faithful statements, and the block is the *shared*
engine of three pins (274, 483, 363 each carry a copy), which is §5's "written once, importable"
argument rather than a checker trick — and the one drifted row stays `private`, because a drifted
statement is a local spelling and not public API. Re-read: **29 ok / 0 mismatch / 0 missing / 0 own**,
module still silent. (This is the AF102-SET4 `Place/EvalAtNorm` 2 → 27 pattern, on a pin whose 46 rows
are half `private`; a mostly-`private` pin is where `check_port`'s count most understates the port, and
`scaffold_audit`/the engine diff — not the checker — is the completeness evidence, as at AF103C.)

**C landed (2026-11-26).** `AutomorphicForm/Adelic/RankinSelbergAnalyticity.lean`, **1,282 lines**,
**35 ok / 0 / 0 / 0**; silent at 20–23 s; 0 warnings; axioms clean on 35/35 (7 of them
`[propext, Quot.sound]`); `dedup` 0 clusters; `move_dead` 0/0. Engine diff 39 pin rows → 36 module
rows: 32 by hash, 3 by name (`_hr`/`_hB`/`_hd` — the pin's unused hypotheses `_`-prefixed, the
preamble's own cure, and the pin has no `linter.unusedVariables` option to transcribe), 1 unaccounted
(the invented `private prod_le_prod_of_nonneg`, forced by `Finset.prod_le_prod` losing its
nonnegativity argument in v4.34).

The order's condition for carving the pin's 437-line `dominated` (**"if the 200 k cap bites"**) does
not hold: it fits in 20 s at the default with a 2× deterministic margin, and the low-cap ladder fails
on four *different* `have`s (80 k / 50 k / 40 k), i.e. the cost is spread across the pin's 23
occurrences of the ~5-line `whittakerCoefficient K (productionPinsOf K D₀ …)` term, not an
instance-inference defect. Recorded and not installed, with the four cut sites (and the ~15 parameters
each cut would need) named in `lean/tmp/af104/AF104C-REPORT.md` if a later order must lower the cap.
This is the case the playbook's "fix what exceeds the bound" gets *right* by not firing: a
`dominated`-sized declaration that fits is not a defect.

**D landed (2026-11-26).** `MeasureTheory/HaarQuotientNormalizer.lean` (233 lines, **1 ok**) and
`AutomorphicForm/Adelic/IwasawaQuotientIntegral.lean` (508 lines, **19 ok**); both silent at the 200 k
cap, both clean at 16 s / 3.9 s under the build lock, axioms clean on 20/20, `move_dead` 0/0,
`dedup` 1 cluster = the pin's own `main` ↔ `solution` pair (the `Adelic/BorelHaarDisintegration.lean`
precedent). **The order's predicted `check_port` sizes (≈26 and ≈16) were wrong in the
substitute-first direction**, and the measurement is the more interesting number:

* **D2 declares one declaration because the pin already was ported.** Its 15 `PeelC` engine rows are
  public in its own premise module `MeasureTheory/HaarQuotient.lean` (§ "The orbit decomposition under
  a normalizing element"), **15/15 hash-identical to the pin's statements**; re-declaring them would
  be an FR-0274 duplicate. So `1 ok` is the whole remaining surface, and the node was a *one-row*
  node whose engine the port had already paid for — a case the frontier's file-granularity cannot see.
* **D1 declares 18 of its 25 named engine rows and imports 7** (5 hash-identical:
  `continuous_diagOne` → `SPart.continuous_diagOne`, the `ratCentral` block and
  `lintegral_rationalCentreUnipotentHaar` → `Adelic/RationalCentreHaar.lean`; 2 generalisations:
  `continuous_unipotentGL2` → `Adelic/ConstantTerm.lean`, `centralScalar_mul_comm` →
  `Adelic/Basic.lean`). Engine diff: 20/20 last-name keys **by hash**, 0 unaccounted.

Two deviations from the order, both correct on inspection: `unipotentGL2_mem` is **not** a
substitution — the port's row proves membership in `torusUnipotentSet K`, a different subgroup from
the pin's `rationalCentreUnipotent K` (a look-alike, and the pin's one-line
`Subgroup.mem_sup_right` was transcribed); and `centralScalar_mul_comm` came from
`Adelic/Basic.lean` (the one home) rather than the `Cusp/GenuineRealization.lean` restatement the
order named.

**One port gap, worked around without a declaration**: `tsum_lintegral_density` needs injectivity of
`algebraMap K (AdeleRing (𝓞 K) K)`, and `NumberField.AdeleRing.algebraMap_injective` has no public
port counterpart (it is `private` in `Adelic/RationalUnipotentBoxSheet.lean:192`); D1 proved it
inline. Promote it if a second consumer appears, do not copy the seven lines again.

**E landed (2026-11-26), with the set's one recorded gap.** `ModularCurve/X1/GenusBound.lean`,
**1,429 lines**, 54 declarations (50 public + 4 `private` carves), **50 ok / 0 / 0 / 0**, axioms clean on
50/50, `move_dead` 0/0, one locked build clean (`Build completed successfully (4729 jobs)`, 53 s, 0
warnings from this file). The `_pkg` false positive the order warned about came back twice more: four of
its rows are transcribed, not substituted (the `RiemannHurwitzCount.Package` block), and `dedup` reports
**one** cluster at 34 lines — the same three `haveI`-headed `_pkg` rows, which `dedup`'s *shape* tier
collapses because it normalises the `haveI := …` prefix. That is FR-0306's blind spot in `dedup`, now
recorded there; the three bodies are three different `AlgebraicCurve` assemblies.

The gap is the 346 headline. After the playbook's ladder was worked properly — four `private` carves of
the pin's `have`-blocks (`natCard_fibre_le` 33 L, `ord_le_of_ord_pos` 13 L,
`finiteDimensional_adjoin_singleton` 22 L, `isIntegral_of_algHom_apply_eq` 24 L), and the brick fixes on
the two search goals (`IntermediateField.finiteDimensional_left E₂` for `FiniteDimensional ↥ℂ⟮t⟯ ↥E₂`,
`haveI := hfin` at the lemma head for `Finite (K ≃ₐ[↥ℂ⟮t⟯] K)`, and `Algebra.IsAlgebraic.of_finite` in
812's `main`) — **nine of the ten bounded pin declarations are silent at 200 000**, and the residual is
**one command**: the module at 200 000 reports exactly one timeout (downward ladder 200 000 → 1;
40 000 → 5; 20 000 → 8; 10 000 → 8; 5 000 → 15; 1 000 → below the module floor). It is silent at the
lakefile's 4 M, which is the shipping bound, so the module builds and the tree is green; the gap is a
**discipline gap in the edit loop**, registered in [CARRY-FORWARD.md](../../CARRY-FORWARD.md) for a
refactor round in the AF103A shape. Nothing is installed: no `maxHeartbeats`, no `synthInstance.*`, no
`attribute [-]` wall, no `sorry`.

## 6.1 The landing table

| order | module(s) | lines | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---:|---|---|
| A | `Cusp/ArchTypeProjector.lean` | **1,141** | **74 ok / 0 / 0** | 74 clean | 0 | 0 / 0 | 200,000 / 180,000 |
| B | `Cusp/SpectrumDensity.lean` | **1,202** | **29 ok / 0 / 0** (16 before the surface gate, +13 promoted) | 29 clean | 0 | 0 / 0 | 200,000 / 175,000 |
| C | `Adelic/RankinSelbergAnalyticity.lean` | **1,282** | **35 ok / 0 / 0** | 35 clean | 0 | 0 / 0 | 100,000 / 50,000 |
| D1 | `Adelic/IwasawaQuotientIntegral.lean` | **508** | **19 ok / 0 / 0** | 19 clean | 1 (the pin's `main` ↔ `solution`) | 0 / 0 | 13,000 / 12,000 |
| D2 | `MeasureTheory/HaarQuotientNormalizer.lean` | **233** | **1 ok / 0 / 0** | 1 clean | 0 | 0 / 0 | 8,000 / 7,500 |
| E | `ModularCurve/X1/GenusBound.lean` | **1,429** | **50 ok / 0 / 0** | 50 clean | 1 (the `_pkg` shape false positive, FR-0306) | 0 / 0 | **4,000,000 / 200,000 — §6's gap** |
| **set** | **6 new modules** | **5,795** | **208 ok / 0 / 0 / 0** | 208 clean, no `sorryAx` | 2, both recorded | 0 / 0 | |

The set-level gates, run by me on the landed tree: the **collision probe**
(`lean/tmp/af104/collision-probe.lean`, importing all six) is **silent** → FR-0274 clean across the six
modules; the **wave build** (`flock`ed, six modules) is `Build completed successfully (5191 jobs)` with
**no warning line from any of the six**; `#print axioms` re-checked by hand on the three headlines of E
and B (the two modules the wave touched after their workers finished) → `[propext, Classical.choice,
Quot.sound]`; and `spec/SetAF104Consumer.lean` compiles with three zones that each exercise a
cross-module composition (A+B, D1 at `K = ℚ`, E's three bounds at a place). C and D2 have no zone and
that is deliberate: C's only consumer is its own 100-binder telescope, and D2's hypotheses force a
normalizer of infinite order, so a concrete instance would be a second development rather than a test.

## 6.2 The set's `check_port` sizes, and the two that were wrong

**208 checked declarations, not the ~227 the brief's §3 predicted** — and the two misses are the
interesting ones:

* **D2: 1, not 16.** The pin's 15 `PeelC` engine rows were *already* public in the pin's own premise
  module `MeasureTheory/HaarQuotient.lean` (§ "The orbit decomposition under a normalizing element"),
  15/15 hash-identical. Re-declaring them would be an FR-0274 duplicate, so the node was a **one-row**
  node whose engine the port had already paid for. This is a case the frontier's file-granularity cannot
  see, and it is why a row's `silo` is not its cost.
* **B: 16 → 29 by the surface gate.** The worker's cut (16) was right about what it *declared*; the
  scoping recipe's §5 experiment (drop `private`, re-check, read the three numbers) showed 29 of the 30
  rows were pin-faithful statements, so 13 were promoted (the engine of three pins, §5's "written once,
  importable") and the one drifted row stayed `private`. Without the experiment the set's checked surface
  would have under-reported this order by 81%.
* **A: 74 against ≈98 predicted**, because its pin is a flat public engine half of which is the
  `ArchInfra` prelude (24 rows substituted, 1 inside-pin dead duplicate dropped).
* **E: 50 against ≈62 predicted** (12 rows substituted, 11 distinct port declarations).

## 6.3 Plan vs actual, honestly

| figure | plan (§3) | actual |
|---|---:|---:|
| rows / orders | 11 / 5 | 11 / 5 |
| silo | 5,669 | 5,669 |
| **written lines** | net-new 4,378 | **5,795** (+32%) |
| modules | 6 | 6 |
| checked declarations | ≈227 | **208** |
| scaffolds | 11 ok | 11 ok |
| recorded edit-loop gaps | none predicted | **1** (E's 346 headline) |

**The `port_plan` net-new figure under-predicted the writing by a third, and it did so for the reason
SET-AF103 recorded**: of the 615 lines it priced as "already in the port", most are *pin-private* copies
(not importable) or differently-stated twins (the `mem_of_ord_nonneg` triple, `with_ratFunc`, the
`_pkg` block), so they were transcribed. **The `silo` figure was the accurate predictor** (5,669 against
5,795 written, 2%), which is the opposite of AF103's experience — there, the substitutions were real
(private engines already public under other names); here they were not. The lesson to carry: neither
figure alone is a budget; the substitutions have to be *audited* (read the port declaration's body and
its visibility) before either number is believed.

The gap was not predicted and could not have been: two of the three `X₁` pins carry `maxHeartbeats`
ceilings the port does not transcribe (6.4 M and 3.2 M), and only working the ladder tells you how much
of that ceiling is usage.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af104_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` (corrected read) | 325 / 176,086 | **314 / 170,417** |
| ready rows | 29 / 9,804 | **22 / 6,379** |
| leaves | 18 / 15,127 | 18 / 15,127 |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is **−11 nodes / −5,669 lines**, *exactly* the cut. It was already in the read before the set
started for E's three rows, because a scaffold's declared names read as ported (the scoping doc's
caveat) — so the honest statement is that the read *predicted* the cut correctly and E's landing moved
nothing, which is a property of the instrument, not of the set.

The ready block moved −7 / −3,425 while **four rows became ready** (2,244 silo), all of them consumers
of this set:

* `AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion`
  (**1,381**, 19 premises) — C's consumer: the unfolded `s`-part integral becomes an Euler *product*;
* `AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType`
  (**435**, 12 premises) — B's consumer;
* `ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC`
  (**340**, 15 premises) — E's consumer;
* `AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact` (**88**, 2 premises) —
  A's and B's consumer.

One measurement about the correction list, worth carrying to the next scoping pass: the 21 `--unport`
false ported markers move `needed` by **exactly one node / 75 lines** (the uncorrected read is
313 / 170,342), and that node is `ModularCurve.ModularPolynomialData.eq_all`, the MD-005 row. On this
shelf the correction is narrow but not cosmetic.

## 8. What the set leaves behind

Five homes that did not exist before — `Cusp/ArchTypeProjector.lean` and `Cusp/SpectrumDensity.lean`
(the carrier's two projectors and its density, closing the story SET-AF103C/D opened),
`Adelic/RankinSelbergAnalyticity.lean` (the analyticity/positivity floor of the Rankin–Selberg
unfolding), `Adelic/IwasawaQuotientIntegral.lean` and `MeasureTheory/HaarQuotientNormalizer.lean` (the
two quotient-measure computations) and `ModularCurve/X1/GenusBound.lean` (the `X₁` invariants) — plus
three things worth carrying: **the surface gate is not optional on a mostly-`private` pin** (B's 16 →
29), **a pin's engine may already be public in its own premise module** (D2's 1 ok, and the frontier
cannot see it), and **the `haveI`-headed `Prop` is the tool chain's blind spot in three places now** —
`port_advise`'s substitute block, `dedup`'s shape tier, and the `_pkg` rows of any pin (FR-0306).

Two open items for the next round: the 346 headline's edit-loop gap (CARRY-FORWARD), and the port gap D
hit — `NumberField.AdeleRing.algebraMap_injective` exists only `private` in
`Adelic/RationalUnipotentBoxSheet.lean` and was proved inline in D1's `tsum_lintegral_density`;
promote it once a second consumer appears rather than copying the seven lines.
