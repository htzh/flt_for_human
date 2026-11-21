# SET-AF99 — the unfolding completes, and the arithmetic q-expansion

**Status: LANDED (2026-11-21).** Seven orders, seven new modules and four insertions, **20 rows /
5,129 silo**. The set is the block the SET-AF98 landing created — the Petersson/unfolding headline
first — plus two stories that sit beside it: the unramified package of right convolutions, the
twisted local integral of the Eisenstein column, and the arithmetic q-expansion of level-one forms.

| # | order | rows | silo | modules |
|---|---|---|---:|---|
| A | the Petersson integral is the quotient integral (28 premises) | 1 | 671 | `AutomorphicForm/Adelic/PeterssonUnfolding.lean` (new) |
| B | the `diagOne` dictionary at a complex place, and the relation at a real one | 2 | 867 | `AutomorphicForm/Adelic/WhittakerDiagOneSu2.lean` (new), `LanglandsTunnell/WhittakerODELinearDependence.lean` (insertion) |
| C | three consumer rows | 3 | 505 | `AutomorphicForm/Adelic/RankinSelbergShellIndicator.lean` (2 insertions), `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` (1) |
| D | the unramified package of right convolutions | 1 | 621 | `AutomorphicForm/Adelic/Cusp/UnramifiedPackage.lean` (new) |
| E | the twisted local integral | 1 | 601 | `EisensteinGeneral/LocalUnr.lean` (insertion) |
| F | the arithmetic q-expansion and the level-one basis | 3 | 1,091 | `ModularForms/IsArithmeticQExpansion.lean` (new) |
| G | the analytic floor: nine MeasureTheory leaves **and their narrow imports** | 9 | 773 | `MeasureTheory/ParametricIntegral.lean`, `…/HaarAveraging.lean`, `…/MoebiusIntegral.lean` (new) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af99_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | 405 / 199,447 |
| ready rows | 22 / 7,902 |
| leaves | 53 / 19,036 |
| withheld (FR-0044 guard) | 4 / 831 |

This is the SET-AF98 landing read, reproduced. The AF-subject part of the ready block is the seven
rows AF98's landing created (671, 621, 473, 394, 234, 138, 133) and this set cuts all seven; §7 names
every row it does not cut, including the two blocks that are *not* cuttable for a reason worth
recording (a missing definition layer, and pins written against `import Mathlib`).

## 1. The stories

* **A is the unfolding's identity claim, and the set's risk row.** 28 graph premises. Its premises
  are AF98's own Borel fundamental-domain row, AF97's shell measure, `HaarQuotient`'s two set-integral
  identities, the Bruhat representative, the box-sheet fundamental domains and the two
  Bessel/Whittaker-unfolding rows. Its consumer is the pin's next step (the analyticity of the
  `S`-part integral), so this is the row the whole Rankin–Selberg column hangs on.
* **B completes the `diagOne` dictionary, in two modules with opposite topology.** The complex-place
  row expands every `diagOne` value of the su(2)-string family; it must live *above*
  `WhittakerSystem.lean`, while its subject's natural home (`WhittakerDiagOne.lean`) sits *below* it —
  so it is a new module, and the import direction is the reason. The real-place row is the dual
  statement — the `diagOne` values satisfy a nontrivial linear relation — and belongs in
  `WhittakerODELinearDependence.lean`, whose subject is exactly linear dependence of
  Whittaker-equation solutions.
* **C is three consumers**, all insertions: the shell bound without the section law (the weaker
  sibling of AF98 C's row), the box indicator that discharges that row's `_hμbox` hypothesis, and the
  newvector conductor of the weight-one lift's *genuine* realization.
* **D is the unramified package**: the right convolution of a genuine cusp realization's member by an
  unramified translate decomposed into a finite package, and the Hecke eigenvalue law on the
  coefficient. Its premises are AF97's additive-character level rows — **AF98 F's `psiLocal_ne_one`
  is one of them**, so this set pays off the last set's leaf order.
* **E is the local `L`-factor** the Eisenstein column reads, in the module whose subject it is. Its
  four premises are all AF rows (AF97 D's Tate-local Fourier rows, the unramified Weyl integrand, the
  adic-completion modulus).
* **F is a three-row story with one premise**: the level-one q-expansion basis of SET-AF97 F is the
  input to all three rows (the aeval polynomial, its discriminant-normalized integrality, and the
  coefficient-side membership), plus the `E₄`/`Δ = X · η` q-expansion identities. Writing it once is
  the point.

## 2. The scaffolds

Four new modules, headline-only, at the pin's own `solution` statements and in the pin's own
namespaces (`AutomorphicForm`, `AutomorphicForm.SmoothCuspRealizationAt`, `ModularForm`):
`check_port` reads **6 ok / 0 mismatch / 0 missing / 0 own** across them before any order starts. The
two insertion orders (C, E) have no scaffold; their rows go where their subject is, and each carries
exactly one wire line.

Two rules the last set paid for are in this set's work order: **no two modules may declare the same
public full name** (FR-0274 — the import probe `lean/tmp/af99/collision-probe.lean` is the only
detector, and it names every module of this set), and **`import Mathlib` is not a probe** — the pins of
this set import it wholesale, the port does not, and a run costs ≈100 s or dies.

## 3. The pricing

| order | raw `S_` lines | dup copies | boilerplate | in the port | **net new** |
|---|---:|---:|---:|---:|---:|
| A + D (2 nodes) | 1,292 | 0 | 114 | 84 | **1,094** |
| B + C (5 nodes) | 1,372 | 0 | 141 | 259 | **972** |
| F (3 nodes) | 1,091 | not measured | — | — | — |
| E (1 node) | 601 | not measured | — | — | — |

`port_advise`/`port_plan` per group; the last two orders are insertions into wired modules and are
priced by their order's own probe.

## 4. The gates

As SET-AF98 §4, with FR-0278 added: `lake build` is serialized **globally**, not per order — two
concurrent builds in one tree corrupt each other's imports. Plus the set-level import probe.

## 5. The landing

| order | module | lines | checker | engine diff | axioms | dedup | move_dead |
|---|---|---:|---|---|---|---:|---|
| C | `AutomorphicForm/Adelic/RankinSelbergShellIndicator.lean` (+326) | 1,408 | **39 ok / 0 / 0** | 0 missing | clean | 0 | 0 / 0 |
| C | `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` (+82) | 1,070 | **18 ok / 0 / 0** | 0 missing | clean | 1 (pin's own pair) | 0 / 0 |
| E | `EisensteinGeneral/LocalUnr.lean` (+429, **migrated**) | **837** | **19 ok / 0 / 0** | 27 pin decls (26 private): 22 stated, 4 hash-reused, 0 missing | clean (11) | 1 (pin's own pair) | 0 / 0 |
| G | `MeasureTheory/ParametricIntegral.lean` | **271** | **4 ok / 0 / 0** | 4 pin publics, 0 missing | clean | 1 (pin's own pair) | 0 / 0 |
| G | `MeasureTheory/HaarAveraging.lean` | **434** | **10 ok / 0 / 0** | 10 pin publics, 0 missing | clean | 0 | 0 / 0 |
| G | `MeasureTheory/MoebiusIntegral.lean` | **226** | **8 ok / 0 / 0** | 8 pin publics, 0 missing | clean | 2 (pin's own pairs) | 0 / 0 |
| F | `ModularForms/IsArithmeticQExpansion.lean` | **887** | **42 ok / 0 / 0** | 68 pin publics: 64 declared, 1 hash-imported, 0 missing | clean (42) | 0 | 0 / 0 |
| A | `AutomorphicForm/Adelic/PeterssonUnfolding.lean` | **681** | **18 ok / 0 / 0** | 20 pin publics, 2 by closure, 0 unjustified | clean (18) | 1 cross (3 lines, §) | 0 / 0 |
| B | `AutomorphicForm/Adelic/WhittakerDiagOneSu2.lean` | **369** | **6 ok / 0 / 0** | 28 pin publics: 5 declared, 22 hash-imported, 0 missing | clean | 0 | 0 / 0 |
| B | `LanglandsTunnell/WhittakerODELinearDependence.lean` (+395) | 1,169 | **15 ok / 0 / 0** | 22 pin publics: 14 declared, 4 imported, 0 missing | clean (18) | 0 | 0 / 0 |
| D | `AutomorphicForm/Adelic/Cusp/UnramifiedPackage.lean` | **694** | **17 ok / 0 / 0** | 0 missing (17 pin publics, **0 by closure**) | clean (17) | 0 | 0 / 0 |

Order C's two insertions each needed a name-resolution decision the order could not have known: the
shell module's "already imported" additive-character rows live in `TateLocal/AddCharLevel.lean`, which
`GlobalAndInfinite` does *not* import (verified acyclic, FR-0280's shape again), and the lift module's
new row is at `AutomorphicForm` while the module's body is `DihedralWeightOne` — so the row is added
after an `end DihedralWeightOne` / `namespace AutomorphicForm` pair at the tail, with a
declaration-local `open … in` instead of a global open edit that would have changed name resolution for
the module's 30 existing declarations. Both moved neither heartbeat floor (probe pairs re-measured,
never installed).


## 6. Plan vs actual (the honesty section)

| order | silo (priced) | net new (predicted) | lines landed |
|---|---:|---:|---:|
| A | 671 | 566 | 681 (new module) |
| B | 867 | 614 | 369 + 395 (new module + insertion) |
| C | 505 | 358 | 326 + 82 (two insertions) |
| D | 621 | 528 | 694 (new module) |
| E | 601 | — | 429 (insertion, + 408 pre-existing) |
| F | 1,091 | — | 887 (new module) |
| **total** | **4,356** | — | **3,863** |

The written ÷ priced ratio is 1.11 on the two orders that were priced as a group (A+D 1,292 silo →
1,094 predicted, 1,375 written) and 0.89 on B+C (1,372 → 972, 1,172 written). Both sit in the band the
playbook records for this column. The set is *smaller* than AF98 in lines and *larger* in row count
(12 rows against 12, but with five modules instead of eleven), and that is the design: the rows behind
AF98's landing are smaller and the work is dominated by the two rows the pins themselves made hard —
A's 28-premise unfolding and F's 68-declaration q-expansion.

**Four order premises were wrong, and every one was caught by the agent:**

1. **"the additive-character level rows are already imported"** (order C, order E, twice) — they are
   not: `GlobalAndInfinite` does not reach `TateLocal/AddCharLevel.lean`, and E's two Tate-local
   premises were outside its 51-file closure. FR-0280's shape, three sightings in one set.
2. **"`scaffold_audit` reads 0 private declarations across the rows"** (order E) — its pin is 26/27
   private, so the two completeness gates are vacuous there and the hash diff is the only engine gate
   (FR-0277, second set running).
3. **"`scaffold_audit`'s closure credits are real"** (order A) — three of four were namesakes (§8).
4. **"the pin's three psiLocal helpers are public"** (AF98 F, repeated here as context) — they are
   private; the same claim about A's pin's `continuous_unipotentGL2` was a *generalization*, and there
   the port's general form is the right answer.

**The instrument came out of the set, not out of the plan.** `tools/deps/port_omissions.py` (order B),
the set-level import probe (`tmp/af99/collision-probe.lean`, 12 modules, silent), and the parser defect
FR-0286 with its blast radius measured. Two of the three exist because an order's gates read green on a
module that was not finished.

## 7. Not cut — named and deferred (FR-0040)

* **The `NumberField.mixedEmbedding` block (392 silo, 4 rows) is blocked, not deferred.** The four
  leaf rows (`trace_mixedEmbedding`, `summable_norm_schwartzMap_ringOfIntegers_translate`,
  `exists_forall_norm_embedding_sub_le`, `exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg`)
  read `needed = 1`, but their statements are written in the `NumberField.mixedEmbedding` vocabulary
  and **the port has no such definition** (`rg MixedEmbedding lean/` is empty; the corpus has the
  namespace but no top-level `Definitions/` row that the port wires). This is the FR-0049 shape — a
  readiness test that reads graph premises and not the statement's vocabulary — and the cure is a
  definition-layer order, not a proof order.
* ~~The MeasureTheory analytic leaves~~ — **cut as order G**, with the import research written into the
  order instead of avoided. Their pins are written against `import Mathlib` (all nine `S_` files list
  `Mathlib` and nothing else), so the narrow list is not in the pin; order G's brief makes finding it
  step one (and step three) of the port, with the `rg` recipe and the report requirement that the
  import list and how each entry was found be written down. That is the reusable artifact: the next
  leaves of this kind do not need the research again.
* Ready rows of the other columns, not cut: `ModularCurve.isIntegral_adjoin_coeffEmb_jq_inv_…` (854),
  `WeierstrassCurve.natCard_torsionOrbit_…` (697), `WeierstrassCurve.exists_isGalois_goodModel_…`
  (599), `GaloisRep.exists_isSemisimpleRepresentation_…` (495), `ModularCurve.StarBank.hassePolyDescent`
  (407), `ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_…` (233),
  `NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const` (108),
  `AlgebraicCurve.exists_placeMap_mapDomain_…` (59) and the three small `ModularCurve` rows
  (36 + 34 + 24).
* Withheld by the FR-0044 guard (the pruned complex-analytic subject's work):
  `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327), `…_jOne` (283),
  `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` (126),
  `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95).

## 8. Instrument finding — `scaffold_audit complete` is a last-name match, and it can be wrong

Order A found it on this set's own scaffold. `tools/deps/scaffold_audit.py` credits a pin declaration
as "satisfied by the import closure" when its **last name** occurs anywhere in the depth-4 closure.
Two consequences, both measured here:

* **On A's scaffold** the credit hid a *different object*: the pin's `slab` is
  `AutomorphicForm.slab`, and the closure's `NumberField.TateGlobal.slab` (finite places) shadowed it
  in the audit's set. A's module had neither `slab` nor `measurableSet_slab` and still read
  `complete`.
* **On `IsArithmeticQExpansion`'s scaffold** (order F) the audit credits 65 rows, 17 of them names
  like `B`, `main`, `nodes`, `restrict`, `Pp`, `Aform`, `Sform`, `Tform` — none of which any port
  declaration answers to as the pin's object.

`check_port` cannot catch this: it iterates the *module's* declarations and never asks what the pin
has that the module lacks. So for a module whose pin carries short or overloaded last names, the
engine gate is the **`statement_db.parse_file` diff** — every pin public declaration must appear in
the module at the pin's name with the pin's statement hash, or be shown by `#check @<full name>` (with
the *type* read, not just the name) to be reachable. That diff is now written into the work order's
preamble, and it is the reason order A declared `slab`/`measurableSet_slab` itself.

§ `dedup --cross` over the set reports one cluster: `ofReal_sq_norm` (3 lines) declared both here and
in AF98's `BorelUnfolding` sub-namespace, plus the seven `RS11C9` helpers at root here and under
`AutomorphicForm.BorelUnfolding` there. The duplication is deliberate — the pin's helper *statements*
name `slab` bare at the root, so the root copies are what make them elaborate — and it is registered in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) as a dedup round's work, not a set's.

**The one MISSING the promoted instrument still reports, and why it is right.** On A's finished module
`port_omissions.py` reads one `MISSING`: the pin's `continuous_unipotentGL2` is stated

```
(A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] : Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A))
```

and the port's root declaration of that name (`AutomorphicForm/Adelic/ConstantTerm.lean`) is the
*general* form `[CommRing R] [TopologicalSpace R] [ContinuousNeg R]`, whose hypotheses are weaker. So
the pin's row is a specialization of what the port has: the name resolves, but the statement does not
match, and a name-only probe (mine) called it a credit while the hash-based tool called it missing.
That is the correct reading — and the deliberate one: re-declaring the pin's stronger-hypothesis
version at the root name would collide (FR-0274), and the port deliberately states the general lemma
once. Recorded here so the next reader does not chase it; it is the single justified MISSING of the set.

**What it cost, measured.** The probe was run against order A's finished module (silent, `sorry`-free,
`check_port` 11 ok, `scaffold_audit` `complete`): it was **missing 8 of the pin's 20 public
declarations** — `globalPoints_mul_mem_slab_iff`, `preimage_slab`, `enorm_coe_real_of_nonneg`,
`mul_le_sq_add_sq`, `ofReal_sq_norm`, `indicator_comp_globalPoints_mul`, `tsum_indicator_const_set`,
`continuous_unipotentGL2` — with `globalPoints_unipotentGL2` the only genuine closure credit. The agent
had taken the audit's four closure credits at face value; three of them were namesakes. That is the
whole argument for the probe: **`complete` on a scaffold whose pin has short names is not a gate, and
the omission it hides is invisible to every other instrument.** The declarations went back to the
order in the same session.

**The second half of the finding, and the instrument.** Order B built the honest reading while fixing its
own module and found the *opposite* direction of the same mechanism: the pin's `det_diagOne` (general
`CommRing R`) has no statement-hash match in the port, and the audit credited it from
`AutomorphicForm.DCFN.det_diagOne`, the `AdeleRing`-only statement — a **specialized namesake hiding a
missing generalization**. So the fallback tier has to be a statement comparison (`check_port`'s
`alpha_stmt`), never a last name.

B's script — full transitive import closure, no depth cap, last name **and** `statement_db` nhash with
`alpha_stmt` as the fallback — is promoted to `tools/deps/port_omissions.py` (untracked), with a `--json`
summary so a set can quote one line per module. It answers the question `check_port` structurally
cannot: *is every pin public declaration on this module's wire declared, imported with the pin's
statement, or missing?* The natural next home is a `--omissions` mode of the checker itself; that is a
`spec/` change and belongs to a refactor round, not to a set.

## 9. After the landing — the shelf re-read, and the set's reusable artifacts

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af99_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 405 / 199,447 | **385 / 194,218** |
| ready rows | 22 / 7,902 | **30 / 10,642** |
| leaves | 53 / 19,036 | **44 / 18,163** |
| withheld | 4 / 831 | 4 / 831 |

The delta is **−20 nodes / −5,229 lines**: eleven ready rows (orders A–F, 4,356 silo) and nine leaves
(order G, 773 silo), twenty rows in all — and it is the first read on which the *leaves* block moved,
because order G is the set's only leaves order. **Nineteen rows became ready** (10,642 silo of new
ready work against 7,902 before), and three of them are the set's own next steps:

* `AutomorphicForm.exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet`
  — the consumer of order A's unfolding identity;
* `MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at` —
  the consumer of order G's `ParametricIntegral` (a mathlib-only leaf feeding an AF row, which is the
  point of porting those leaves at all);
* `AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell` and its
  `…_shell` sibling — consumers of orders C and B.

**What the set leaves behind that is reusable, in the order of its value:**

1. `tools/deps/port_omissions.py` (order B) — the omission check the checker structurally cannot do;
   it found A's 8 missing declarations and the one justified generalization MISSING, and it is the
   reason §8's finding cost a round instead of a set.
2. **The nine import lists of order G**, each with the `rg`/`#check` that settled it and the 27 lines
   measured away, plus FR-0287's rule (the `public import` re-export chain, not the declaring-module
   set, decides a narrowing list). That is the template the next mathlib-only leaves follow.
3. **The set-level import probe** (`tmp/af99/collision-probe.lean`, 15 modules) — the only FR-0274
   detector, silent on the final tree.
4. **Three legacy-migration precedents** in two sets (`UnitFactorizableTheorems`, `LocalUnr`), with
   FR-0285's three steps and its tell.
5. **FR-0286** — the parser's `\s`-crosses-newlines defect, with its blast radius measured (780 sites,
   141 files, 285 swallowing an opener) and the one-character cure, for the checker round that owns it.

**What this set did not do, deliberately.** It added no consumer zone. Both candidate zones were
*extractions* rather than compositions — A's identity is a conjunction whose halves the pins' own next
rows consume, and the Borel/quotient chain that would compose A with AF98's `BorelFundamentalDomain`
needs D2's `∃`-witness re-stated, which is a new declaration rather than a test. The set's consumer
surface is instead the nineteen new ready rows, each of which *is* a cross-module composition waiting
to be written; the record says so rather than shipping a `#check`-shaped file.
