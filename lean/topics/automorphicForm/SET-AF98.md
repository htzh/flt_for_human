# SET-AF98 — the archimedean Whittaker system, the Rankin–Selberg shell, and four leaves

**Status: LANDED (2026-11-21).** Six orders, eight modules (six new), **12 rows / 7,374 silo**.
The set is the Whittaker–Rankin–Selberg block that the SET-AF97 landing made ready: the archimedean
Whittaker system at a real and a complex place, the `diagOne` norm bound the Bessel inequality
reads, the shell-indicator bound of the Rankin–Selberg unfolding, the quotient integrand's torus
integral, the Borel set integral, the isotypic-vs-archimedean-cut decomposition, and four small
rows of the block.

| # | order | rows | silo | net new | modules |
|---|---|---|---:|---:|---|
| A | the global coefficient as an archimedean Whittaker system | 3 | 1,560 | 1,155 | `AutomorphicForm/Adelic/WhittakerSystem.lean` (new) |
| B | the `diagOne` norm bound at a complex place | 1 | 1,827 | 997 | `AutomorphicForm/Adelic/WhittakerDiagOneBound.lean` (new) |
| C | the shell indicator of the squared coefficient | 1 | 1,418 | 939 | `AutomorphicForm/Adelic/RankinSelbergShellIndicator.lean` (new) |
| D | the quotient integrand's torus integral, and the Borel fundamental domain | 2 | 1,439 | 930 | `AutomorphicForm/Adelic/RankinSelbergTorusIntegral.lean`, `…/BorelFundamentalDomain.lean` (new) |
| E | the isotypic submodule meets an archimedean cut | 1 | 836 | 895 | `LanglandsTunnell/IsotypicCuspSubmodule.lean` (new) |
| F | four leaves | 4 | 294 | ≈250 | `LanglandsTunnell/TateLocal/AddCharLevel.lean`, `AutomorphicForm/Adelic/UnitFactorizableTheorems.lean`, `LanglandsTunnell/WeightOneLiftFactorizationBound.lean`, `MeasureTheory/HaarQuotient.lean` (insertions) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af98_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | 417 / 206,821 |
| ready rows | 27 / 12,612 |
| leaves | 53 / 19,036 |
| withheld (FR-0044 guard) | 4 / 831 |

The figures are the SET-AF97 landing read reproduced exactly (its §7 "after" column), so nothing has
been ported since: the ready block is the fifteen rows AF97's landing created, and the AF-subject
part of it is the Whittaker/Rankin–Selberg block this set cuts. The rest of the ready shelf is the
other columns (`WeierstrassCurve` 697 + 599 + 256, `ModularCurve` 854 + 407 + 233 + 36 + 34 + 24,
`ModularForm` 464 + 452 + 175, `GaloisRep` 495, `EisensteinGeneral` 601, `NumberField` 108), and
§6 names every row this set does not cut.

**Caveat on re-reads.** The six scaffolds are wired, so `frontier` credits their eight nodes from the
moment they exist on disk (it reads the wire, not the proofs). A shelf read taken now would show the
eight rows gone and `needed` smaller by 8 nodes / 7,080 lines before the set has proved anything;
the §7 figures below are therefore taken after the landing, and a forecast taken during the set must
pair the read with `--unport` on the eight node names.

`--selfcheck` is unchanged from AF97's read (the same five over-broad wires outside the D–S demand);
the four-`--unport` correction it produced there is already in the front-end, so the corrected and
uncorrected reads agree on this shelf.

## 1. The stories

A *story* is one mathematical subject, and the set is the Whittaker–Rankin–Selberg story cut into
one subject per order.

* **A is the archimedean half of the coefficient's dictionary.** The three pins are one
  development — the archimedean Iwasawa calculus applied to `whittakerCoefficient` — and
  `port_advise` prices them at **39 declarations already in the port** (302 lines: the
  derivative/flow laws, the `ψ (α x)` laws, the `archRealGLAt`/`archComplexGLAt` charts) and 15
  duplicate lines removable by writing the shared block once. The two real-place rows share their
  engines outright (`diagSign_mul_unipotent` is proved twice in the pin, `glArch_ext` twice), so the
  module writes them once and the two headlines sit at the ends.
* **B is the quantitative half.** One 1,827-line pin, 87 declarations, 11 premises: the growth bound
  the Bessel inequality consumes. It imports A's sibling engines (the *local* complex system, in
  the archimedean Whittaker module) and the `LanglandsTunnell` torus-system growth block — not A
  itself, so A and B are independent orders.
* **C, D are the Rankin–Selberg unfolding.** C is the shell-surgery bound: the squared coefficient of
  a unipotent average is bounded by a *finite* sum of archimedean-data coefficients. D is the two
  measure-theoretic identities underneath the unfolding — the quotient integrand's `∫⁻` as a torus
  integral, and the Borel set integral as the Petersson integral times the Bruhat–Eisenstein factor.
  All three rows' premises are SET-AF97's B modules (the shell measure, the quotient-integrand
  definition layer).
* **E is the spectral-decomposition step** the archimedean cut consumes: a vector in the sup of a
  finite family of cusp constituents, lying in the isotypic cusp submodule and in the archimedean
  cut, has a *single* constituent carrying a nonzero vector in both. Its premises are SET-AF97's E
  (`IsCuspidalFn.add`/`.smul`) and the Hecke-coset system.
* **F is the small-row block**: `psiLocal_ne_one` (74 silo, project fan-in **144**), the Haar
  quotient's normalizer identity (106, fan-in 3), the `unitFactorizableOfType` bi-invariance
  companion (73), and the lift's newvector conductor (41). These four are `needed = 1` rows of the
  **ready** block, not `--include-leaves` rows — a distinction the shelf re-read in §7 measures, and
  the one the scoping note's §0 warns about. Small rows carrying disproportionate project demand.

## 2. The scaffolds

As SET-AF97: each new module exists before any order starts, with its header prose, its `spec-pin:`
wires, a **narrow** import list and the **headline theorem(s)** only, at the pin's own `solution`
statement and renamed to the published name, body `sorry`. `check_port` reads all six scaffolds at

> **8 ok / 0 mismatch / 0 missing / 0 own**

(3 + 1 + 1 + 1 + 1 + 1 across A–E), so every headline is the pin's byte-for-byte before a proof is
written. `scaffold_audit` is `incomplete` on all six by construction: the pin's other declarations are
the order's transcription, and `complete` is the order's gate.

Two consequences the orders carry, unchanged from AF97: a `MISSING` row means an invented helper
(keep it `private` or report it), and `scaffold_audit incomplete` is the order's **to-do list**.

The pin's `attribute [-instance]`/`attribute [-simp]` blocks are **not** in the scaffolds: they name
pin-prelude instances the port does not have (and they are proof-side). The `attribute [local instance]`
measurable-space blocks **are**, because the statements do not elaborate without them — C's statement
needs all six of `glBorel`/`adeleBorel`/`ideleBorel` and their `BorelSpace` companions.

### The pin's compressed names stay, and why (a recorded deviation)

The three pins of order A carry the pin's compressed definition names on their public surface —
`eC`, `iotaW`, `bprime`, `g0`, `W`, `Fstr`, `DFstr`, `DDstr`, `fstr` — and the port rectifies generated
tokens. **They are kept here, deliberately**: they occur inside the pins' *public statements* (`W D (x p) 1 (…) = lam * …`
is the shape of two of the headlines), and the statement check is textual, so rectifying one turns
every statement that mentions it into a `MISMATCH` and costs one `spec/decl_markers.tsv` row per
affected declaration. What *is* rectified is the pipeline label on the namespace — `E40DCFN` → `DCFN`,
as the sibling cuspidal-constituent module already spells it. The same call is recorded in this column
for `kIw`. A rectification pass, if wanted, is a refactor with the marker rows in hand, not an order's
improvisation; it is registered in [CARRY-FORWARD.md](../../CARRY-FORWARD.md).

A consequence to carry: the pin's two `W`s (`(D) (x) (g)` in the real-place pin, `(D) (φ) (g)` in the
complex-place one) are two declarations, and the port already holds a third under
`AutomorphicForm.DCFN.W` from the cuspidal-constituent development — so this is exactly the name that
legitimately needs more than one home, and the order says so.

## 3. The pricing

`port_advise` + `port_plan`, run per order:

| order | raw `S_` lines | dup copies | boilerplate | in the port | **net new** |
|---|---:|---:|---:|---:|---:|
| A (3 nodes) | 1,560 | 15 | 88 | 302 | **1,155** |
| B (1 node) | 1,827 | 29 | 49 | 752 | **997** |
| C (1 node) | 1,418 | 89 | 38 | 352 | **939** |
| D (2 nodes) | 1,439 | 0 | 105 | 404 | **930** |
| E (1 node) | 836 | — | — | — | **895** † |
| F (4 leaves) | 294 | — | — | — | ≈250 ‡ |
| **total** | **7,374** | **133** | **280** | **1,810** | **≈5,166** |

The `in the port` column is the reuse the set gets for free: 1,810 lines, most of them from the
archimedean Casimir/Whittaker modules the earlier AF sets wrote and the AF93 prelude. The three
substitution clusters `port_plan` reports — `casWords` (7), `casBarCoeff` (4), `casCoeff` (3) — are
the Casimir-word dictionaries, all already public.

† measured as the difference of the four-node read (`C+D+E` 2,764) and the two-node read (`D` 930).
‡ not measured: the four leaves are 9 declarations over four existing modules, and `port_advise` is
run per order by the order's own brief.

## 4. The gates

As SET-AF97 §4:

1. `check_port --force` → 0 mismatch / 0 missing / 0 own, **every** declaration `ok`.
2. `scaffold_audit` → `complete`.
3. The module's own `lake env lean -DautoImplicit=false` → no output at all; one locked `lake build`.
4. `#print axioms` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
5. `dedup --within` → 0 clusters, or the pin's own pairs with the reason.
6. `move_dead --dry-run` → `0 / 0`, or the documented escape clause.
7. A heartbeat probe pair in the header, never installed.

No bare `import Mathlib`; no `set_option maxHeartbeats`; no tree build; shell calls under two
minutes; `lake build` in the background with its output in `lean/tmp/af98/`.

## 5. The landing

| order | module | lines | decls | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `AutomorphicForm/Adelic/WhittakerSystem.lean` | **1,349** | 63 (24 public / 39 private) | **24 ok / 0 / 0** | clean (24 swept) | 0 | 2 / 7 † | 20,000 / 10,000 |
| C | `AutomorphicForm/Adelic/RankinSelbergShellIndicator.lean` | **1,082** | 27 (all public) | **27 ok / 0 / 0** | clean (27) | 1 cross (7 lines) § | 0 / 0 | 70,000 / 65,000 |
| D | `AutomorphicForm/Adelic/RankinSelbergTorusIntegral.lean` | **873** | 55 (53 / 2) | **53 ok / 0 / 0** | clean (58) | 0 | 0 / 0 | 5,000 / 2,500 |
| D | `AutomorphicForm/Adelic/BorelFundamentalDomain.lean` | **691** | 26 (all public) | **26 ok / 0 / 0** | clean (33) | 0 | 0 / 0 | 60,000 / 30,000 |
| B | `AutomorphicForm/Adelic/WhittakerDiagOneBound.lean` | **934** | 19 (17 / 2) | **17 ok / 0 / 0** | clean (17) | 1 (pin's own private pair) | 0 / 0 | 75,000 / 60,000 |
| E | `LanglandsTunnell/IsotypicCuspSubmodule.lean` | **941** | 47 (1 public / 46 private) | **1 ok / 0 / 0** ‡ | clean (1) | 0 | 1 / 4 | 4,000 / 3,000 |
| F | `LanglandsTunnell/TateLocal/AddCharLevel.lean` | **404** (was 312) | 4 on the wire | **4 ok / 0 / 0** | clean (4) | 0 | 0 / 0 | — |
| F | `AutomorphicForm/Adelic/UnitFactorizableTheorems.lean` (migrated) | **180** (was 75) | 4 on the wire | **4 ok / 0 / 0** | clean (4) | 0 | 0 / 0 | — |
| F | `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` | **988** (was 943) | 16 on the wire | **16 ok / 0 / 0** | clean (16) | 1 (pin's own pair) | 0 / 0 | — |
| F | `MeasureTheory/HaarQuotient.lean` | **1,046** (was ~960) | 6 on the wire | **6 ok / 0 / 0** | clean (6) | 1 (pin's own `d2` pair) | 0 / 0 | — |

‡ **This row's completeness gates are vacuous, and the set paid for the lesson (FR-0277).** The pin
declares 47 declarations of which **46 are `private`**, so `check_port` diffs one statement and
`scaffold_audit` is `complete` on the bare `sorry` scaffold. The work order's claim that
`statement_db.parse_file` reads "0 private declarations across all twelve rows" was read off the
wrong tuple index (the rows are 11-tuples, FR-0275) and is false for this row. The engine gate that
does work is the `parse_file` diff: **47 pin / 47 port declarations, 47 statement hashes identical**,
measured by the manager after landing. It is now the standard extra gate for a mostly-`private` pin.

§ `dedup --cross` over the six modules reports exactly one cluster: `T2_unipotentGL2_algebraMap_eq_globalPoints`
(C) against `unipotentGL2_algebraMap_eq_globalPoints` (A), 7 lines. It **stays**: the pin states the
law twice under two last names, and `scaffold_audit` keys the import-closure credit on the last name,
so dropping C's copy would put the row back to `MISSING` (FR-0269). The other 24 clusters the
within-module passes reported are gone (`--within` is 0 everywhere).

The six modules are **importable together** — the FR-0259 probe
`lean/tmp/af98/collision-probe5.lean` compiles the six-way import — which is the check that caught
the A/B prelude collision and the only gate that can.

† The pin's own unused `private` helpers `reg_sub`/`op_apply` (dead in the pin too): kept in place
under the §3.8 escape, not deleted.

The manager re-ran every gate independently of the orders' reports: `check_port --force` on each
module, `scaffold_audit` (`complete` on all four), the silence gate (0 bytes of output on all four),
`#print axioms` on the six landed headlines (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`),
and the import probe that is the FR-0259 detector (importing the set's modules together — the one
cross-module failure this set hit, see below, is exactly what it catches).

**A's finding reverses one of this order's premises, and it is the set's most useful instrument
result.** The work order said the `casWords`/`casCoeff`/`casBarCoeff` dictionaries were "already in
the port — import those, do not re-declare". They are not: `port_advise` matched them on a `def`'s
**type only** (`Fin 10 → ℂ`) against the *left*-Casimir `W10` and a sign vector, and the pin's
dictionary is the **right**-Casimir one. Deleting them would have been three `MISSING` rows and a
non-elaborating headline. This is the `def … : Prop` false-positive of §2.4 in another dress, and it
is recorded as FR-0266. **Read a `def` substitution row's body, not its type.**

**The shared prelude: one home, and the collision the gates cannot see (FR-0259).** Order A and
order B transcribe two pins that copy the same 15-declaration archimedean prelude
(`DCFN.{casWords, casCoeff, casBarCoeff, archDelAt_apply', …}`, `KType.{archComplexGLAt_eq_lift_rot,
…, final_bound}`) — 14 byte-identical. Written independently they made the two modules
**unimportable together** (`environment already contains AutomorphicForm.DCFN.casCoeff`), a failure
`check_port`, `scaffold_audit` and both single-module builds report as green. The manager's ruling:
A's home stays (it landed first), B imports `WhittakerSystem` and drops its copies. The detector is
the import probe in `lean/tmp/af98/collision-probe.lean`, and it belongs in the review of every set
whose orders transcribe sibling pins.

Two shape decisions the agents made and the manager kept: engines nest (`RankinSelberg.SPart` for
the quotient integrand, `RankinSelberg.ShellSurgery` for the shell surgery, `BorelUnfolding`,
`DiagOneCasimir`/`Su2KType` in B) because the port already publishes `continuous_diagOne`,
`det_diagOne`, `globalPoints_scalar`, `slab`, `measurableSet_slab`, `det_centralScalar`,
`globalPoints_injective` at `AutomorphicForm` — a flat transcription of these pins would have been
unimportable alongside six existing modules; and the pins' `set_option maxHeartbeats` declarations
(`torus_at_S`, 1,600,000 in the pin) are **not** carried: the proof transcribes verbatim at ≈68k
heartbeats, 24× under the pin's bump.

**The consumer zone.** `spec/AutomorphicFormSetAF98Consumer.lean` reads the set quantitatively:

* `profile_second_deriv_eq` — A's archimedean equation solved for the second derivative
  (`f'' = -(P f)/y²`), the form the growth analysis integrates against a bound;
* `norm_whittakerCoefficient_diagOne_le_at_b` — B's `∃ δ ∃ C` bound read at the unramified torus
  point `b` of its hypotheses, which is the form the cuspidal-constituent row consumes.

Both are real applications of the headlines (deleting `WhittakerSystem` or `WhittakerDiagOneBound`
breaks the file), and both are `sorry`-free. Two candidate zones were dropped rather than faked: the
`ideleNorm (u⁻¹) = 1` corollary of the shell's norm law, which needs a rewrite the port's
`ideleNorm`-as-`def` will not accept (`rw [← map_mul]` does not see it — the FR-0268 class), and the
`k = 1` specialization of C's shell bound, whose 28-binder statement is not worth hand-copying while
the row itself is what the next order reads. The set's 8 headlines are covered by the axiom sweeps.

## 6. Plan vs actual (the honesty section)

`port_plan`'s **≈5,166 net new math lines** landed as **6,126** in the six new modules (5,872) plus the
four insertions (≈250), a written ÷ net ratio of 1.19 — inside the 1.0–1.3 band the playbook records
for this column. Per order: A 1,349 vs 1,155 predicted, B 936 vs 997, C 1,082 vs 939, D 1,564 vs 930,
E 941 vs 895. D and A overshot, and both for the same reason: the pins carry public *engines* whose
statements the port writes in full (`SPart`, `BorelUnfolding`, `TorusOdeAux`, `DCFN`, `KType`) — the
prediction counts them once, and the written count pays for the section variables, the `open`s and the
docstrings that a port keeps and a pin does not.

**Four work-order claims turned out to be false, and the agents caught every one:**

1. **"the `casWords`/`casCoeff`/`casBarCoeff` dictionary is already in the port"** — it is not; the
   advice matched a `def` on its type (FR-0266). Order A transcribed them; deleting them would have
   been three `MISSING` rows and a non-elaborating headline.
2. **"`statement_db.parse_file` reads 0 private declarations across all twelve rows"** — false for
   order E's pin, which is 46/47 `private`, and false as read (the rows are 11-tuples, FR-0275).
   Consequence: E's two completeness gates were vacuous (FR-0277).
3. **"the `psiLocal_ne_one` pin's three helpers are public in the pin"** — backwards: all three are
   `private`, so they were written `private` (FR-0279).
4. **"import the Haar quotient's premises, do not re-prove"** — unsatisfiable: both premise modules
   *import* `HaarQuotient`, so the "premises" would be a cycle; the row was proved from the home
   module's own private engine instead (FR-0280).

The pattern is worth carrying: **three of the four are claims about the pin or about the instrument,
and none is checkable by any gate** — only by reading the pin's text or the tool's tuples. A work
order that states such a claim should say where it was read from, so the agent can re-read it in one
command rather than inherit it.

**One operational finding that cost a round and is not mathematical (FR-0278):** two *concurrent*
`lake build`s in this tree corrupt each other — lake deletes a target's `.olean` before rewriting it,
so an unrelated module's `import` fails while the other build runs. Builds must be serialized
globally, not per order. It is the one place where the "4 agents at a time" cap bites, and the cure is
a build lock outside `/tmp` (which this harness does not persist).

## 7. Not cut — named and deferred (FR-0040)

* Ready rows of the other columns: `ModularCurve.isIntegral_adjoin_coeffEmb_jq_inv_…` (854),
  `WeierstrassCurve.natCard_torsionOrbit_…` (697), `WeierstrassCurve.exists_isGalois_goodModel_…`
  (599), `GaloisRep.exists_isSemisimpleRepresentation_…` (495), `ModularForm.exists_polynomial_aeval_…`
  (464), `ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_…` (452),
  `ModularCurve.StarBank.hassePolyDescent` (407), `EisensteinGeneral.LocalUnr.integral_twisted_eq`
  (601), `ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_…` (233),
  `ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem` (175),
  `NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const` (108),
  `HaarQuotient.*` (106 — cut by order F), `AlgebraicCurve.exists_placeMap_mapDomain_…` (59),
  `DihedralWeightOne.hasNewvectorConductor_…` (41 — cut by F) and the three `ModularCurve` leaves
  (36 + 34 + 24).
* Withheld by the FR-0044 guard (the pruned subject's work): `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH`
  (327), `…_jOne` (283), `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`
  (126), `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95).
* The analytic leaves the AF column also reads, deferred whole: `MeasureTheory.*` (99, 98, 148, 90,
  84, 63, 18, 222, 104, 95 — 921 silo), `NumberField.mixedEmbedding.*` (237, 71, 67, 17),
  `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` (69, fan-in 41),
  `NumberField.Units.exists_forall_abs_sub_mult_mul_log_le` (98), `NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal`
  (94), `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` (684), `TateCurve.*` (1,038),
  `ValuationSubring.*` (825), the sixteen `WeierstrassCurve` leaves, and `M4aTorus.completedRayL_fe`
  (12,126). They are leaves of their own subjects, not of this story; one more leaves set takes them
  the way order F takes these four.

## 8. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af98_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 417 / 206,821 | **405 / 199,447** |
| ready rows | 27 / 12,612 | **22 / 7,902** |
| leaves | 53 / 19,036 | 53 / 19,036 |
| withheld | 4 / 831 | 4 / 831 |

The delta is **−12 nodes / −7,374 lines**, which is the set's cut exactly (row by row: 1,827 + 1,418
+ 836 + 818 + 681 + 621 + 573 + 306 + 106 + 74 + 73 + 41), and the twelve gone rows are the twelve
the table names. **Seven rows became ready** (2,664 silo), and they are the set's payoff:

* `AutomorphicForm.peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient`
  (671) — the consumer of order D's Borel row, exactly the pin's next step;
* `AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery`
  (133) — the consumer of order C's shell row;
* `AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String` (473)
  and `AutomorphicForm.exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul`
  (394) — the two rows behind order B's `diagOne` bound and order A's complex-place system;
* `AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate` (621),
  `NumberField.StandardAddChar.exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow` (234) and
  `AutomorphicForm.exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne`
  (138).

Two readings of this landing are worth carrying:

* **The four rows of order F are ready rows, not `--include-leaves` rows.** They are small
  (`needed = 1`), and the leaves block is untouched at 53 / 19,036 — the shelf's two blocks are
  different instruments, and a set that reads only the ready block can still be right about which
  rows it consumes. §6's "leaves" list is where the *leaves* block lives; this set consumed none of
  it.
* **The delta is the check that the wires are honest.** `needed` moved by exactly the pin lines of
  the twelve rows, no more and no less: a wired module credits only the node whose file its header
  names, so an over-broad wire shows up as a delta larger than the cut (FR-0265's five are unchanged
  and outside the D–S demand), and a missing wire as a row that stays on the shelf.
