# SET-AF11 — the Whittaker coefficient: its API and its archimedean differentiability

**Status: LANDED 2026-11-02** — manager's layer plus one dispatch, all gates green; **§5.1 records
the landing and the re-read**. The order is
[WORKORDER-AF11-whittaker-api.md](WORKORDER-AF11-whittaker-api.md). Two scoping measurements were
wrong on the tree and are corrected at dispatch in the note after §0 (§3 and §4 carry pointers);
the scoping text below is otherwise left as read. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF10 left. It is the **eleventh** `AutomorphicForm`-serving set, and it is the column's return to
the recipe's *cheapest* cut after four composition sets: not an engine reuse but **nine rows of small,
high-fan-in declarations** around one object.

The set is **9 rows / 1,595 silo / 1,211 net** (`port_plan`), of which **1,267 lines in 49
declarations** by the per-declaration worklist. It is a **transcription** set in the AF7 sense — only
**146 of the 1,413 declaration lines are in the port** — chosen because its fan-in is the largest on
the AF shelf: `whittakerCoefficient_unipotentGL2_mul` has leverage **17 / 54**, i.e. 54 project
consumers for 95 written lines. That is SET 3's "26-line leaf, 33 consumers" signal, and the recipe's
§1 says demand is inverted relative to size on this shelf.

| block | rows | silo | work | lines written per consumer |
|---|---:|---:|---:|---:|
| the coefficient's algebraic API | 4 | 525 | 446 | 95 / 54, 74 / 17, 97 / 14, 180 / 12 |
| the shell-surgery and realization identities | 3 | 368 | 309 | 114 / 1, 132 / 2, 63 / 2 |
| the archimedean differentiability (real + complex) | 2 | 702 | 512 | 279 / 3, 233 / 2 |
| | **9** | **1,595** | **1,267** | |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af11.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF10 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **877 / 354,646** | 877 / 354,646 |
| `needed [literal]` | 890 / 358,121 | 890 / 358,121 |
| frontier F | **1,538 / 772,720** | 1,538 / 772,720 |
| ready rows, all namespaces | 68 / 18,250 | 68 / 18,250 |
| ready rows, `AutomorphicForm` | **39 / 12,906** | 39 / 12,906 |
| leaves, all namespaces | 241 / 61,078 | 241 / 61,078 |
| leaves, `AutomorphicForm` | **72 / 15,039** | 72 / 15,039 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (4 checks; 1,357 `Thm_` sources, 1,538 declared names) | PASS |
| correction | **none needed** | — |

The read is SET-AF10's §5.1 to the line. Both blocks are quoted whole and every row accounted for in
Appendix A: 39 ready rows / 12,906 and 72 leaves / 15,039, of which 9 are this set's and 102 deferred
(§7 gives the reasons for the candidates; the rest are one-line `deferred`).

### 0.2 Why the Whittaker coefficient, and not the three larger rows

The three largest ready rows are still the Weyl-integrand pair (1,349 + 1,291) and
`isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043); each consumes a large unported
development of its own, and each is a set. The Whittaker coefficient is the opposite: **nine rows
whose object is already in the port** (`WhittakerCoefficient.lean`, the definition layer, 8
declarations) and whose statements are about that object and nothing else — its transformation law
under the unipotent, its additivity and smul over a locally constant coefficient, its continuity, the
diagonal reduction, shell surgery on the `diagOne` value, the two realization-scalar identities, and
its differentiability along the archimedean flow at a real and at a complex place.

**The nine rows are one object's API, not nine subjects.** That is the cut's real defence: the
mathematics is "what `whittakerCoefficient` does", and after this set a consumer of the Rankin–Selberg
or cusp-realization development can read the coefficient's algebra and analysis off one module.

### 0.3 Why this is a transcription set, and what that costs
The last three sets were compositions (915, 892 and 145 lines already in the port); this one is not.
Its nine `S_` files are flat — `port_plan` finds 55 duplicate lines and 184 boilerplate out of 1,595 raw,
and only 145 lines in the port — so the work is the pin's proofs, 1,267 lines in 49 declarations. Two of
the nine are close to the port already: the complex differentiability row shares **87 lines / 9
declarations** with the complex archimedean prelude SET-AF9 landed (`hasDerivAt_archFlowMatrixComplex_apply`,
`archComplexLiftAt_mul_archComplexGLAt`, `hasDerivAt_of_symm_mul_archFlowMatrixComplex`, …), which is the
port-once block; the real twin has no such block and is written whole.

### 0.4 At dispatch (2026-11-02): two corrections, and what the manager landed

Measured on the tree, not read off the shelf. The order is
[WORKORDER-AF11-whittaker-api.md](WORKORDER-AF11-whittaker-api.md).

1. **The definition gate was not free (§3 is corrected).** `spec/gate_scan.py` over
   `Def_UnramifiedWhittaker_HeckeRecursion.lean` against the two `SmoothCuspRealizationAt.` rows:
   row 6 uses **3/8** (`placeEmbed`, `repSome`, `repInf`), row 7 uses **2/8** (`placeEmbed`,
   `scalarPi`) — **4 declarations missing from the port**, and all four are spelled in the rows'
   *statements*, so rows 6 and 7 could not be stated, let alone proved. The manager ported the
   whole `Def_` node (8 declarations) as `RepTheory/LocalLanglands/UnramifiedWhittaker.lean`,
   wired, **8 ok / 0 mismatch / 0 missing**; the gate scan now reads 0 missing on both rows.
2. **The import list had a cycle (§4 is corrected).** `NumberTheory/NumberField/AdelicTraceFin.lean`
   — needed by three rows (5, 8, 9) for `NumberField.StandardAddChar.stdAddChar` — imports
   `AdelicTraceProducer` → `StandardGlobalAddChar` → `StandardGlobalAddCharRat`, and that module
   imported `WhittakerCoefficient`: the coefficient's module could not import the character. The
   cut is by subject, not by convenience: the pin's
   `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean` files **two subjects**, so its
   character-theoretic half (`IsPrincipalInvariantAddChar`, `IsGlobalAddChar` and the two
   degenerate cases) now lives in `NumberTheory/NumberField/GlobalAddChar.lean`
   (**4 ok / 0 / 0**), and `StandardGlobalAddCharRat.lean` imports that instead — handed over on
   the way (`spec-pin:` in, `PORT_FILES` row out, **44 ok / 0 / 0**).
3. **The wire and the counts.** `WhittakerCoefficient.lean` carries **10 `spec-pin:` lines** (the
   pin `Definitions/` file + the nine `Theorems/` wrappers) and checks **4 ok / 0 mismatch / 0
   missing** — the coefficient's definition layer; the other four declarations of the pin file are
   in `GlobalAddChar.lean`. So the landing target is **4 + 9 = 13 ok**, not the 8 + 9 §5 forecast.
   `lean/tmp/probe-af11-statements.lean` states all nine headlines as `example … := by sorry`
   against the migrated module alone and elaborates: the statements fit, and the module's `open`
   list covers them. One import was added after dispatch, at the worker's row-4 blocker:
   `NumberTheory/AdelicModulus` (the pin's `distribHaarChar_algebraMap` and
   `isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox` — the product formula, already in the
   port but outside the module's closure; the manager's edit, not the worker's).
4. **The price falls by 77 lines (§2 is corrected), not by the plan's dedup.** The pin carries
   `continuous_unipotentGL2` four times (rows 2, 3, 8, 9); the port has one, strictly more general
   copy at `AutomorphicForm.continuous_unipotentGL2` (`Adelic/ConstantTerm.lean`), already
   imported. Effective work: **~1,190 lines in 45 declarations**. The 12 substitutions of row 9
   (143 lines) are the complex port-once block in `ArchDerivCasimirComplexAPI.lean` and are
   imported, not transcribed.
5. **No `Def_` promotion, no `set_option`, no `sorry`; the two new modules are mathlib-like
   definition modules** (they host declarations without consumers by design: `heckeRecursionSeq`,
   `torusFactor`, `unipotent`, `diagZ` have no consumer in this set).

## 1. The nine rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `whittakerCoefficient_unipotentGL2_mul` | 123 | **95** | 6 | 4 | **17/54** | the coefficient at `n(x) * g` is the coefficient at `g` times the character factor — the transformation law everything else rewrites with |
| `whittakerCoefficient_sum_smul_of_continuous` | 86 | **74** | 2 | 0 | **10/17** | additivity over a finite sum of a locally constant coefficient (the smul/`sum` form) |
| `continuous_whittakerCoefficient` | 108 | **97** | 2 | 0 | 3/14 | continuity of the coefficient in the group variable |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | **180** | 15 | 2 | 4/12 | at a global point, the coefficient is a constant times its `diagOne` value |
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | **114** | 5 | 0 | 1/1 | the shell-surgery identity for the `diagOne` value (adèlic trace, `AdelicTraceFin`) |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | **132** | 1 | 1 | 1/2 | the sum over the archimedean representatives at a place |
| `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | **63** | 2 | 0 | 1/2 | the scalar-`Π` form of the same |
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | **279** | 8 | 0 | 2/3 | **the coefficient is differentiable along the real archimedean flow**, with the derivative given by the coefficient of the derivative (parametric integral) |
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | **233** | 8 | 0 | 2/2 | the complex twin |
| | **1,595** | **1,267** | **49** | | |

## 2. The price

```bash
python3 port_advise.py --nodes <the nine> --json build/af11-advise.json
python3 port_plan.py --json build/af11-advise.json
python3 build/af-worklist.py <the nine stems>
```

**`port_plan`.** raw **1,595** → declaration lines **1,411** → −55 duplicate copies → 1,356 once-cost →
**−145 already in the port** → **NET NEW 1,211**; 12 trusted substitutions, **0 suspect** (the cleanest
run the column has had — no type-only `def` artefact at all).

**The per-declaration worklist** (Appendix B): 1,413 declaration lines (the parser and `port_plan` differ by 2 lines), **146 imported**, **1,267 to
write in 49 declarations**. The two biggest single blocks are the differentiability pair (279 + 233,
16 declarations) and the diagonal reduction (180 lines in 15 declarations — the largest declaration
count after the complex one).

## 3. The definition gate — corrected at dispatch: **one** `Def_` node, 8 declarations

*(As scoped this section said "complete, no `Def_` node"; `gate_scan` at dispatch found four
declarations of `Def_UnramifiedWhittaker_HeckeRecursion` missing from the port, used by rows 6 and
7 at their statements. See §0.4.1; the measurement below was otherwise right.)*

`spec/gate_scan.py` over the five `Def_` modules of the nine wrappers' closure, all nine rows:

| pin `Def_` module | port home | used (max) | missing |
|---|---|---|---:|
| `Def_AutomorphicForm_WhittakerCoefficient` | `…/Adelic/WhittakerCoefficient.lean` | 2/8 | **0** |
| `Def_NumberField_AdelicTraceFin` | `…/NumberField/AdelicTraceFin.lean` | 5/6 | **0** |
| `Def_AutomorphicForm_ProductionPinsGeneral` | `…/ProductionPinsGeneral.lean` | 0/50 | **0** |
| `Def_AutomorphicForm_ArchDerivCasimir` | `…/ArchDerivCasimir.lean` | 4/56 | **0** |
| `Def_AutomorphicForm_ArchDerivCasimirComplex` | `…/ArchDerivCasimirComplex.lean` | 1/32 | **0** |

Fourth set in a row with no definition obligation. This one is worth noting: the whole set is
*phrased against* an object (`whittakerCoefficient`) whose definition layer is 8 declarations and
whose module is 82 lines — the definition gate being free is what makes the API story affordable.

## 4. The home, and its migration

**`AutomorphicForm/Adelic/WhittakerCoefficient.lean`** — the object's own module (82 lines, 8
declarations, the `Def_` transcription). It is **legacy** (`PORT_FILES`, no `spec-pin:`), and the
migration is measured, not assumed: with its one `Def_` wire added, `check_port --force` on a copy gives
**8 ok / 0 mismatch / 0 missing**. So the manager's layer is: the `Def_` wire in, the `PORT_FILES` row
out, `UNWIRED-PUBLIC.md` regenerated, and then the nine rows' wires (10 `spec-pin:` lines in total).

**Imports the module must gain** — corrected at dispatch: **not** all acyclic, and all of them are
now in the module (§0.4.2). The list as scoped, kept for the record:

| for | module |
|---|---|
| the two differentiability rows | `ArchDerivCasimir` (real), `ArchDerivCasimirComplexAPI` (complex), `Mathlib.Analysis.Calculus.ParametricIntegral` |
| shell surgery | `NumberTheory/NumberField/AdelicTraceFin` |
| the realization identities, the diagonal reduction | `ArchDerivCasimir` (via `ArchWeightCharTransport`/`ArchType`), `ProductionPinsGeneral` (already reached through `CarrierPins`) |

**Namespace note.** Two rows' wrapper statements are qualified `RankinSelberg.…` and
`SmoothCuspRealizationAt.…`, and neither namespace exists in the port yet (the modules that will grow
them are unported). The rows are stated at their wrapper's qualified names — that is what the checker
diffs — but they live in the coefficient's module, because *their* subject is the coefficient, not the
Rankin–Selberg development that will one day cite them. That is a deliberate, recorded split: the
module is the object, the namespace is the consumer's.

## 5. The cut

**One order, one worker, 1,267 lines / 49 declarations / 9 public headlines, all in one module.**
The nine rows are independent of each other (their pin proofs cite only `Def_` modules and each
other through the coefficient's API), so the worker can land them in any order — but the
transformation law (`whittakerCoefficient_unipotentGL2_mul`) is written first, because the diagonal
reduction and the realization identities rewrite with it.

**The manager's layer**: the legacy migration measured at one wire (§4), the nine wires, and a
statements probe (all nine headings as `example … := by sorry` against the migrated module) — the check
that cost SET-AF8 an hour and has caught a missing `open` in every set since.

**Gates.** No tree build; the module's own `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000`
and its own `flock`/`timeout 280 lake build`; `check_port --force` → `0 mismatch / 0 missing` (the `ok`
count is **4 + 9 = 13** — corrected at dispatch, §0.4.3; the definition layer is 4 after the split,
and measure it rather than assume it); `#print axioms` on all nine
→ `[propext, Classical.choice, Quot.sound]`; zero warnings; `dedup`/`move_dead`; and one
`spec/AutomorphicFormSetAF11Consumer.lean` zone that composes the transformation law with the
differentiability identity (the derivative of the coefficient written through the transformation law
is a real composition).

### 5.1 The landing (2026-11-02)

**Files.** `AutomorphicForm/Adelic/WhittakerCoefficient.lean` 138 → **1,404** (the nine headlines, the
33 private helpers and six section headers, +1,266); `spec/AutomorphicFormSetAF11Consumer.lean`
(93 lines, new); `NumberTheory/NumberField/GlobalAddChar.lean` (57) and
`RepTheory/LocalLanglands/UnramifiedWhittaker.lean` (95) from the manager's layer, and
`StandardGlobalAddCharRat.lean` handed over. **42 declarations: 9 public headlines + 33 private
helpers.**

**What the worklist's 49 became 42.** The nine `solution` entries are the nine public headlines with
the pin's body inlined (the pin has no separate headline in its `S_` files — the `Theorems/` wrapper
carries the name). Of the 40 helpers, seven went: the pin's four `continuous_unipotentGL2` copies
(rows 2, 3, 8, 9 — the port's `AutomorphicForm.continuous_unipotentGL2` is strictly more general),
row 5's `gl_ext` (the imported `ArchDerivCasimir.eq_of_glArch_eq_of_glFin_eq`), row 1's
`addChar_neg_eq_conj` (dead in its own file, pin `:30`), and row 1's two prelude instances, folded
into one 3-line `private instance` delegating to the port's
`FltWs24.AdelicModulusOne.countable_principalSubgroup`. Nine private helpers are *deliberately*
private though the pin has them public (`whittakerCoefficient_eq_one_diagGL2_mul` and the row-4/5/7/8/9
preludes): publishing them would need a wire per pin `S_` file and would move the checker's count off
the set's gate. Promoting any of them is a one-line edit plus a `spec-pin:` line, and is a consumer's
call (§3.8 of the playbook).

**Gates, re-run by the manager.** Edit loop at `-DmaxHeartbeats=200000` **silent, 6.0 s**; own
`flock`/`timeout 280 lake build` green (3,608 jobs, no warnings); `check_port --force` **13 ok / 0
mismatch / 0 missing / 0 own / 0 kw** — the nine resolve by name against their `Theorems/` wrappers
(4 → 13, and the two manager modules hold at 4 / 8); `#print axioms` on all nine
`[propext, Classical.choice, Quot.sound]`; `dedup --within` 0 clusters / 0 lines, `move_dead` 0/0;
the whole wired corpus `check_port --changed` 10,498 ok / 0 / 0; the frozen checker unchanged
(6,892 identical / 3 mismatched / 18 missing, all pre-existing in `AlgebraicCurve/`); the statements
probe still elaborates; the consumer zone compiles in 0 errors, 0 warnings.

**Deviations from the pin, all recorded.** One `attribute [local instance]` block replaces the pin's
per-proof `letI`/`haveI` (FR-0121: `linter.style.haveILetI` is live and `set_option` is forbidden),
and the flow-coefficient lemmas are restated in the port's `archMatrixUpdate` form (still `rfl`);
**`add_left_injective` → `add_right_injective`** in row 1 is the one substantive correction — without
it the `conv_lhs` set-integral rewrite silently aims at `fun u => x + u`, so the pin's spelling does
not transport; the rest are v4.34 deprecations and simp-arg lints (FR-0122). The headlines shadow the
module's `variable (F)` with an explicit `(F : Type) [Field F] [NumberField F]` because the checker
hashes the signature text and the wrappers spell the binders inline (FR-0123) — measured, not
assumed: `13 ok` is the proof. **No `set_option`, no `sorry`, no `native_decide`, no new import, no
hub edit.**

**The two parametric-integral rows were carried by mathlib, not by the port's engines.** Rows 8 and 9
both end at `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the engine the pin invokes, with the
pin's `M₁ * M₂` dominating bound transcribed over port API (`exists_isCompact_adelicBox_subset`,
`IsCompact.exists_bound_of_continuousOn` on `C ×ˢ [-2,2]`, `adelicAddHaar_adelicBox_lt_top`,
`Measure.integrableOn_of_bounded`, `IsArchSmoothAt(.Complex).differentiableAt_flow`). The port's own
`hasDerivAt_integral_*` / `contDiff_parametricIntegral_*` are shaped for right convolution against
compact-support factorizable test functions and are `private` outside the module's closure: the risk
register's "look at the port's engines first" produced a recorded negative, and the pin transcribed.

**The consumer's one extra hypothesis, and why it is not a weakening.** The zone composes row 1 with
row 8 by rewriting the derivative of a *unipotent translate* of the coefficient. Row 1's invariance
premise `hper` is stated at a fixed `g` while the flow moves `g`, so the zone states the uniform
left-unipotent invariance `∀ β g, φ (n β · g) = φ g` — the standard automorphy of an automorphic form —
as a **consumer-side hypothesis** and derives row 1's premise from it at each point. Neither headline
is weakened; the gap is real and it is the shape a Rankin–Selberg consumer will meet.

**Plan against actual.** Lines: **1,210** against the estimate's 1,190 (+1.7 %) and the worklist's
1,267 — the excess over the estimate is rows 8/9's restated flow-coefficient lemmas and row 4's
private engine, the shortfall against the worklist is the seven dropped helpers. Declarations: **42**
against 45; the three are exactly the dropped `gl_ext` plus the two prelude instances folded into one.
Checker: **13 ok**, the forecast to the declaration. No build-time incident: the largest declaration
is far under the 200,000 cap and the module builds in 6–7 s.

**The re-read.** The demand side is the forecast to the line (−9 / −1,595); the return is on the leaf
side, and it is **seven for seven**:

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 877 / 354,646 | **868 / 353,051** | −9 / −1,595 ✓ (exact) |
| `needed [literal]` | 890 / 358,121 | **881 / 356,526** | −9 / −1,595 ✓ |
| frontier F | 1,538 / 772,720 | **1,547 / 774,315** | +9 / +1,595 ✓ |
| ready rows, all namespaces | 68 / 18,250 | 67 — | the set's two ready rows leave; one row net-enters from another column (the read is global) |
| `AutomorphicForm` ready rows | 39 / 12,906 | 37 (forecast) | −2, the set's two ready rows |
| leaves, all namespaces | 241 / 61,078 | **234** | −7 ✓ |
| `AutomorphicForm` leaves | 72 / 15,039 | 65 (forecast) | −7 ✓ (all nine of the set's rows are gone from both blocks) |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,357 / 1,538) | **PASS** (1,366 `Thm_` sources, 1,547 declared names) | — |

The readied rows are what the four API headlines were for: the seven leaves were the set's own, and
the return the fan-in promised (54 / 17 / 14 / 12 project consumers) is a *future* read — the
coefficient's API now exists, so the Rankin–Selberg and cusp-realization rows that read a `diagOne`
value can import it. This is the first set in four where the demand side is the smaller half of the
payoff, and the figures are consistent with that (§0.2 of the scoping).

## 6. Risk register

1. **The parametric-integral rows are the only analytic risk.** 279 and 233 lines, and the real twin
   has no port-once block (§0.3); the complex twin imports 87 lines from AF9's prelude. Both are
   dominated-convergence proofs — the same shape `ConvolutionLimit.lean` and `RightConvRegularity.lean`
   already carry, so the port's existing engines (`contDiff_parametricIntegral_*`,
   `hasDerivAt_integral_*`) are the first place to look before transcribing a hand-rolled bound.
2. **`AdelicTraceFin` is used 5/6 by three rows** — it is ported (`…/AdelicTraceFin.lean`), but the
   shell-surgery row is the first consumer in this column: read its API before transcribing the trace
   manipulations.
3. **The fifteen-declaration diagonal reduction** is the set's second-largest block; its pin proof is a
   chain of rewrites through the transformation law. It is the one row where a wrong first rewrite
   costs the whole proof.
4. **The two `…Complex` prelude blocks are the pin's copies** (`hasDerivAt_flow_*`,
   `archComplexLiftAt_mul_archComplexGLAt`, …): the 87-line port-once block is imported; do not
   re-transcribe it (AF8's Appendix B lesson: a name-anchored reading mistakes the prelude for work).
5. **No `Def_` node, no promotion, no new module** (§3, §4); **no `set_option maxHeartbeats`, no
   `native_decide`, no `sorry`**; zero warnings; the only expected suppression is a local
   `linter.unusedVariables` if a pin statement carries an unused binder (none of the nine does — check).
6. **The `RankinSelberg.` and `SmoothCuspRealizationAt.` qualified names must be kept** (§4): they are
   the wrapper's, and the checker's name tier reads them; do not "simplify" them into the flat
   namespace.

## 7. What this set does not do

- **It does not take the local Casimir ODE pair** — `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype`
  (695, leaf, **650 lines in 52 declarations**) and `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight`
  (347, leaf, 315 in 10) — **1,042 silo / 965 net**. That is the *local* side: the Casimir as a
  second-order operator on the Whittaker **profile**, solved with explicit special functions
  (arctan/log/sqrt), a transcription set of its own and the natural next cut.
- **It does not take the three largest ready rows** (the Weyl-integrand pair 1,349 + 1,291,
  `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` 1,043), nor
  `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` (624): separate subjects, each a set.
- **It does not take AF10's one readied row**,
  `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` (321, 6
  premises): the complex twin of SET-AF9's bridge, cheap, and better folded into whichever Casimir set
  comes next than into an API set.
- **The 4 withheld rows / 831 silo** remain the prunable complex-analytic subject.
- **No `Def_` node, no new module, no promotion**; the one legacy migration is the manager's (§4).

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af10-landed.json` by `build/af11-shelf-appendix.py` (silo, premises,
leverage, disposition).

### The ready block — **39 rows / 12906 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | 3 | 2/5 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | 3 | 1/5 | deferred (§7) |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | deferred (§7) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | 2 | 4/15 | deferred (§7) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4/12 | **SET-AF11** |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1/2 | **SET-AF11** |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |

### The leaves block — **72 leaves / 15039 silo**

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | 2/2 | deferred (§7) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred (§7) |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred (§7) |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred (§7) |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred (§7) |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred (§7) |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred (§7) |
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | 2/2 | **SET-AF11** |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred (§7) |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred (§7) |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 1/1 | deferred (§7) |
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | 1/1 | deferred (§7) |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | 2/3 | **SET-AF11** |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 1/1 | deferred (§7) |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 1/1 | deferred (§7) |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 1/1 | deferred (§7) |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | 1/1 | **SET-AF11** |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `whittakerCoefficient_unipotentGL2_mul` | 123 | 17/54 | **SET-AF11** |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | deferred (§7) |
| `continuous_whittakerCoefficient` | 108 | 3/14 | **SET-AF11** |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `whittakerCoefficient_sum_smul_of_continuous` | 86 | 10/17 | **SET-AF11** |
| `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | 1/2 | **SET-AF11** |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 2/2 | deferred (§7) |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred (§7) |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 3/22 | deferred (§7) |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 3/8 | deferred (§7) |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred (§7) |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred (§7) |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred (§7) |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 2/14 | deferred (§7) |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred (§7) |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred (§7) |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 5/18 | deferred (§7) |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred (§7) |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 3/4 | deferred (§7) |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred (§7) |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred (§7) |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred (§7) |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred (§7) |
| `constantTerm_add` | 13 | 1/2 | deferred (§7) |
| `constantTerm_smul` | 11 | 1/1 | deferred (§7) |

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py` from the port's statement index: per row, every declaration whose
statement is not in the port, with its pin line and span.

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `whittakerCoefficient_unipotentGL2_mul` | 98 | 3 | 95 | 6 |
| `whittakerCoefficient_sum_smul_of_continuous` | 74 | 0 | 74 | 2 |
| `continuous_whittakerCoefficient` | 97 | 0 | 97 | 2 |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 180 | 0 | 180 | 15 |
| `RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 114 | 0 | 114 | 5 |
| `SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 132 | 0 | 132 | 1 |
| `SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 63 | 0 | 63 | 2 |
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 279 | 0 | 279 | 8 |
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 376 | 143 | 233 | 8 |
| **9 rows** | **1413** | **146** | **1267** | **49** |

### `whittakerCoefficient_unipotentGL2_mul`

98 declaration lines, 3 imported, **95 to write** in 6 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `whittakerCoefficient_unipotentGL2_mul` | 36 | 75 | theorem |
| `setIntegral_adelicBox_comp_add_right` | 29 | 39 | theorem |
| `solution` | 14 | 111 | theorem |
| `integral_cond_adelicBox_comp_add_right` | 7 | 68 | theorem |
| `productionPinsOf_ν` | 5 | 34 | theorem |
| `addChar_neg_eq_conj` | 4 | 30 | theorem |

### `whittakerCoefficient_sum_smul_of_continuous`

74 declaration lines, 0 imported, **74 to write** in 2 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 52 | 36 | theorem |
| `continuous_unipotentGL2` | 22 | 14 | theorem |

### `continuous_whittakerCoefficient`

97 declaration lines, 0 imported, **97 to write** in 2 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 76 | 34 | theorem |
| `continuous_unipotentGL2` | 21 | 13 | theorem |

### `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul`

180 declaration lines, 0 imported, **180 to write** in 15 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `whittakerCoefficient_eq_one_diagGL2_mul` | 53 | 130 | theorem |
| `integrand_vadd` | 21 | 52 | theorem |
| `measurePreserving_principalIdeleOf_smul` | 16 | 83 | theorem |
| `whittakerCoefficient_productionPinsOf_eq` | 16 | 103 | theorem |
| `solution` | 16 | 194 | theorem |
| `image_principalIdeleOf_inv_smul_adelicBox` | 11 | 119 | theorem |
| `diagOne_mk0_eq_diagGL2` | 11 | 183 | theorem |
| `unipotentGL2_mul_globalPoints_diagGL2` | 10 | 37 | theorem |
| `globalPoints_unipotentGL2` | 5 | 47 | theorem |
| `globalPoints_coe_apply` | 4 | 30 | theorem |
| `distribHaarChar_principalIdeleOf` | 4 | 79 | theorem |
| `measurableEmbedding_principalIdeleOf_smul` | 4 | 99 | theorem |
| `diagGL2` | 3 | 34 | def |
| `principalIdeleOf` | 3 | 73 | def |
| `principalIdeleOf_smul` | 3 | 76 | theorem |

### `RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery`

114 declaration lines, 0 imported, **114 to write** in 5 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 80 | 63 | theorem |
| `gl_ext` | 15 | 41 | theorem |
| `mul_comm_of_glArch_eq_one_of_glFin_eq_one` | 7 | 56 | theorem |
| `whittakerCoefficient_mul_right` | 6 | 29 | theorem |
| `glArch_unipotentGL2_eq_one` | 6 | 35 | theorem |

### `SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient`

132 declaration lines, 0 imported, **132 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 132 | 16 | theorem |

### `SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient`

63 declaration lines, 0 imported, **63 to write** in 2 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `placeEmbed_scalarPi_eq_centralScalar_det` | 32 | 20 | theorem |
| `solution` | 31 | 52 | theorem |

### `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt`

279 declaration lines, 0 imported, **279 to write** in 8 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 131 | 169 | theorem |
| `hasDerivAt_setIntegral_flow` | 69 | 100 | theorem |
| `continuous_archFlowAt` | 23 | 62 | theorem |
| `continuous_unipotentGL2` | 17 | 21 | theorem |
| `hasDerivAt_flow_of_isArchSmoothAt` | 15 | 85 | theorem |
| `continuous_archFlowMatrix_apply` | 11 | 38 | theorem |
| `archFlowAt_coe_apply` | 9 | 49 | theorem |
| `archFlowAt_neg` | 4 | 58 | theorem |

### `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex`

376 declaration lines, 143 imported, **233 to write** in 8 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `hasDerivAt_setIntegral_flowComplex` | 75 | 265 | theorem |
| `solution` | 66 | 340 | theorem |
| `continuous_archFlowAtComplex` | 24 | 223 | theorem |
| `continuous_archFlowMatrixComplex_apply` | 18 | 190 | theorem |
| `hasDerivAt_flow_of_isArchSmoothAtComplex` | 18 | 247 | theorem |
| `continuous_unipotentGL2` | 17 | 173 | theorem |
| `archFlowAtComplex_coe_apply` | 11 | 208 | theorem |
| `archFlowAtComplex_neg` | 4 | 219 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af11.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.whittakerCoefficient_unipotentGL2_mul \
  --nodes AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous \
  --nodes AutomorphicForm.continuous_whittakerCoefficient \
  --nodes AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul \
  --nodes AutomorphicForm.RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery \
  --nodes AutomorphicForm.SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient \
  --nodes AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient \
  --nodes AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt \
  --nodes AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex \
  --json build/af11-advise.json
python3 port_plan.py --json build/af11-advise.json     # 1,595 raw / 1,411 decl / 145 in port / 1,211 net
python3 build/af-worklist.py whittakerCoefficient_unipotentGL2_mul \
  whittakerCoefficient_sum_smul_of_continuous continuous_whittakerCoefficient \
  whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul \
  RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery \
  SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient \
  SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient \
  hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt \
  hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
```

The migration probe of §4:

```bash
cd ../lean
python3 - <<'PY'
import pathlib
src = pathlib.Path('FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean').read_text()
i = src.index('-/')
wire = "  spec-pin: Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean\n"
pathlib.Path('tmp/probe-WC-wired.lean').write_text(src[:i] + wire + src[i:])
PY
python3 spec/check_port.py --force tmp/probe-WC-wired.lean     # 8 ok / 0 mismatch / 0 missing
```

**Forecast on landing** (read after SET-AF10, §0.1): `needed` **877 / 354,646 → 868 / 353,051**
(−9 / −1,595), frontier **1,538 / 772,720 → 1,547 / 774,315**, the `AutomorphicForm` ready shelf
**39 / 12,906 → 37 / 12,552** (the two ready rows leave), the leaves **72 / 15,039 → 65 / 13,798** (the
seven leaves leave). What the set in turn readies is a re-read question; the fan-in of the four API
rows (54, 17, 14, 12 project consumers) is the reason to expect a positive return, and AF11 is the
first set in four where the *demand* side is the smaller half of the payoff.

**Measured at landing (§5.1):** the first three rows are exact to the line; of the last two, the
*leaves* are exact (241 → **234**, −7), while the ready shelf reads 68 → **67** all-namespaces rather
than 66 — the read is global, so a row from another column entered in the same interval. The
`AutomorphicForm`-only figures (39 → 37 ready, 72 → 65 leaves) are as forecast.
