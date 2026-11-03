# SET-AF10 — the complex Casimir algebra closes: the seven rows SET-AF9 readied

**Status: LANDED 2026-11-02 — manager's layer plus one dispatch, all gates green; §5.1 records the landing and the re-read.** Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF9 left. It is the **tenth** `AutomorphicForm`-serving set, and it is the direct payoff of the
ninth: all seven rows are `AutomorphicForm` rows that **became ready because SET-AF9 landed** (§0.2),
and every one of them destructures or cites a headline AF9 wrote.

The set is **7 rows / 1,567 silo**, and it is the third composition set in a row — **915 of its 1,485
declaration lines are already in the port** (the complex archimedean engine AF9 landed, plus the
`Def_` layer), so the work is **570 lines / 27 declarations**: one 289-line prelude block and six
corollary proofs over an engine that exists.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| the complex Casimir algebra | 5 | 1,443 | 469 | `ArchCasimirComplex.lean` |
| the right-convolution rows | 2 | 124 | 101 | `ArchDerivRightConv.lean` |
| | **7** | **1,567** | **570** | two files, one order |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af10.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF9 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **884 / 356,213** | 884 / 356,213 |
| `needed [literal]` | 897 / 359,688 | 897 / 359,688 |
| frontier F | **1,531 / 771,153** | 1,531 / 771,153 |
| ready rows, all namespaces | 74 / 19,496 | 74 / 19,496 |
| ready rows, `AutomorphicForm` | **45 / 14,152** | 45 / 14,152 |
| leaves, all namespaces | 241 / 61,078 | 241 / 61,078 |
| leaves, `AutomorphicForm` | **72 / 15,039** | 72 / 15,039 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (4 checks; 1,357 `Thm_` sources, 1,531 declared names) | PASS |
| correction | **none needed** | — |

The read is SET-AF9's §5.1 to the line — no set has landed since, so this brief opens on the
instrument's own numbers with no `--unport` and no correction. Both blocks are quoted whole and every
row is accounted for: Appendix A lists the 45 ready rows and the 72 leaves with a disposition each (7
are this set's, 110 are deferred — the candidates with reasons in §7, the rest one-line `deferred`).

### 0.2 Why these seven: the read-back of the last landing

SET-AF9 §5.1 counted **seven rows readied** by its ten rows. This brief takes exactly those seven, and
the reason is visible in their own import lines: five of them import **only** `Definitions/` plus
`Theorems/Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex` — the AF9 leaf —
and their proofs open by destructuring its fifteen-fold conjunction:

```lean
obtain ⟨-, -, hEF, -, -, hEiF, hiEF, -, -, -, -, hiEiF, -, -, -⟩ :=
  archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ
```

The other two import AF9's real-place rows (`archCasimirAt_rightTranslate_and_rightConv_…` needs
`archCasimirAt_rightTranslate_archRealGLAt` + `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` +
`archCasimirAt_rightConv_of_…`; the `isArchSmoothAt_rightConv_and_exists_…` row needs
`isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar`). So this is not a
selection out of the shelf; it is the shelf's own reply to the last landing.

### 0.3 The size, stated plainly

570 lines is **below** the recipe's one-order band (≈1,100–1,400 net), and this brief says so rather
than padding the set with a neighbour of another subject. It is taken as its own set because it is
seven *headlines* over an engine that is already ported and checked — the marginal cost of a dispatch
is mostly its briefing, and this briefing is cheap because the engine, the homes and the wires all
exist (§4). If the manager prefers to fill a dispatch, §7 names the one candidate that shares no
subject and must **not** be folded in (the Whittaker/Casimir ODE quartet) and the one that could
legitimately follow it.

### 0.4 The manager's layer, landed

Three things, all measured:

1. **The seven wires are in.** `ArchCasimirComplex.lean` carries **10** `spec-pin:` lines (its 5 plus the
   five complex rows' `S_` files), `ArchDerivRightConv.lean` **6** (its 4 plus the two real rows'), and
   both re-check unchanged — **101 ok / 0 mismatch / 0 missing** and **3 / 0 / 0** — so the new wires
   collide with nothing. No per-declaration markers (policy 2026-11-02).
2. **The statements are verified.** `lean/tmp/probe-af10-statements.lean` states all seven headlines,
   lifted verbatim from their wrappers, as `example … := by sorry` against exactly the two homes, and
   elaborates — the FR-0112 check that a `#check` list cannot make. It also settled the only header
   edit the set needs: the two real rows use `adelicBox`, so `ArchDerivRightConv.lean` must
   `open NumberField.AdelicBox` (`NumberField.AdelicLevel` is already open).
3. **Nothing else.** No `Def_` node (§3), no migration, no promotion, no new module, no new import
   beyond that `open`. The manager's whole layer is 7 header lines and one probe.

## 1. The seven rows

| row (`AutomorphicForm.` dropped) | silo | work | prem | lev | what it states |
|---|---:|---:|---:|---:|---|
| `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` | 1,227 | **289** | 1 | 2/4 | the **complex analogue of `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt`**: the left-acting complex Casimir element agrees with `archCasimirAtComplex` (and with the bar-Casimir, and both derivatives of it, at a right translate) |
| `isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar` | 73 | **62** | 3 | 1/1 | for a character-typed factorisable test function, `rightConv` of a smooth function is again smooth and its Casimir is the convolution of the Casimir — and stays in `levelInvariantSubmodule ⊓ archCutSubmodule` |
| `archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero` | 70 | **61** | 1 | 1/1 | at `iH`-weight `n` with the compact raising operator vanishing, the compact Casimir acts by `−(n²+2)` |
| `archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul` | 54 | **45** | 1 | 2/2 | the `E`/`F⁻`-mixed `∂̄∂` identity at `iH`-weight `m` |
| `archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt` | 51 | **39** | 3 | 2/3 | the Casimir commutes with right translation by a **row isometry** (every place) and with right convolution |
| `archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul` | 49 | **40** | 1 | 2/2 | the twin of the fourth row, `∂∂̄` in the other order |
| `archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex` | 43 | **34** | 1 | 1/2 | the **Casimir decomposition**: `archCasimirAtComplex + archCasimirBarAtComplex` in terms of the compact Casimir and the `iH`/`E+F⁻`/`iF⁻−iE` derivatives |
| | **1,567** | **570** | | |

**One story.** Every row is a Casimir identity at the complex place or its right-convolution transfer;
the big one is the complex half of a pair whose real half has been in the port since `ArchCasimir.lean`,
and the six others are corollaries of the same fifteen-fold commutator conjunction. Nothing in the set
is about a different object.

## 2. The price

```bash
python3 port_advise.py --nodes <the seven> --json build/af10-advise.json
python3 port_plan.py --json build/af10-advise.json
python3 build/af-worklist.py <the seven row stems>     # the per-declaration reconciliation
```

**`port_plan`.** raw `S_` lines **1,567** → declaration lines **1,478** → **0 duplicate copies** (the
pin wrote this development once) → 89 boilerplate → **892 already in the port** → **NET NEW 586**;
99 trusted substitutions + 2 suspect, and the two suspects are real: the pin's `Del1`/`Del2`
(pin `:319`/`:322`) *are* `ArchCxGL.D1`/`D2` in `ArchCasimirComplex.lean` (`:148`/`:220`, same
signature) — **import them, do not write them**.

**The per-declaration reconciliation** (Appendix B is its output): of 1,485 declaration lines, **915
imported**, **570 to write in 27 declarations**. The distribution is the shape of the set: one row
carries 289 of the lines in 21 declarations (the pin's `LeftCas`/`CommC` prelude: `Ld`, `Ld_one`,
`Ld_Ld_one`, `Ld_apply_lift`, `casimirs_apply`, `leftCas_one`, `casimirs_rightTranslate_any`,
`archComplexGLAt_mul_comm_of_archComponent_eq_one`, `hasDerivAt_negflow_mul_const`, …), and the other
six are **one declaration each** (their `solution`), 34–62 lines apiece. Appendix B's 915 "imported"
is spot-checked for FR-0115's failure mode: `archDelAt_apply` and `casimir_identity` are in
`ArchCasimirComplex.lean` itself, i.e. the home, so the import direction is satisfied.

## 3. The definition gate: complete, no `Def_` node

`spec/gate_scan.py` over all six `Def_` modules of the seven wrappers' closure, against all seven rows:

| pin `Def_` module | port home | used (max over rows) | missing |
|---|---|---|---:|
| `Def_AutomorphicForm_ArchDerivCasimirComplex` | `…/ArchDerivCasimirComplex.lean` | 17/32 | **0** |
| `Def_AutomorphicForm_ArchDerivCasimirComplexAPI` | `…/ArchDerivCasimirComplexAPI.lean` | 24/43 | **0** |
| `Def_AutomorphicForm_ProductionPinsGeneral` | `…/ProductionPinsGeneral.lean` | 0/50 | **0** |
| `Def_AutomorphicForm_CuspidalConstituent` | `…/Cusp/Constituent.lean` | 2/21 | **0** |
| `Def_AutomorphicForm_FactorizableTestFn` | `…/FactorizableTestFn.lean` | 4/10 | **0** |
| `Def_AutomorphicForm_RightConvolution` | `…/RightConvolution.lean` | 1/5 | **0** |

Third set in a row with no definition obligation: the `ArchDerivCasimirComplex`/`…API` pair is what
the whole complex archimedean subject is phrased against, and it landed before the AF column started
these leaves.

## 4. Homes: the two modules that already hold the engines

**Five complex rows → `AutomorphicForm/Adelic/ArchCasimirComplex.lean`** — "the complex-place Casimir
engine", the module SET-AF9 extended with the four complex leaves, and the module that already holds
`archDelAt_apply`, `casimir_identity`, `archCxGL.D1/D2` and the AF9 headline every one of these proofs
cites. Its wire grows from 5 to 10 pin files (the five rows' `S_` files).

**Two real rows → `AutomorphicForm/Adelic/ArchDerivRightConv.lean`** — "differentiating a right
convolution along an archimedean flow", where SET-AF9 put the two Casimir rows; the bridge rows here
are the same subject one step further (right translate by a row isometry, and the Casimir of a
character-typed convolution). Its wire grows 4 → 6.

**Import direction, checked row by row:**

| row group | consumes (port module) | home is at or above it? |
|---|---|---|
| 5 complex rows | `ArchDerivCasimirComplex`, `…ComplexAPI`, AF9's complex headline (in `ArchCasimirComplex`) | **yes** — the home *is* that module |
| `archCasimirAt_rightTranslate_and_rightConv_…` | `ArchCasimir` (`archCasimirAt_rightTranslate_archRealGLAt`, `…_rowIsometryInclAt_of_ne`) + `ArchDerivRightConv` (the AF9 bridge row) | **yes** — `ArchDerivRightConv` imports `ArchCasimir` since AF9's manager layer |
| `isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_…` | the same two plus `RightConvRegularity` (AF5) and `FactorizableTestFnArchSmooth` (AF6) | **yes** — all imported by `ArchDerivRightConv` |

No new import is needed in either file, and no module is created: the homes exist, are
`check_port`-wired (§4 of SET-AF9/§5 of the playbook), and are 0-dead.

## 5. The cut

**One order, one worker, 570 lines / 27 declarations / 7 public headlines.** Files:
`ArchCasimirComplex.lean` (5 rows, +5 wires) and `ArchDerivRightConv.lean` (2 rows, +2 wires). The two
files are disjoint from anything in flight (nothing is in flight), and the second depends on the first
only through AF9's landed declarations, so a single worker can do them in either order.

**The manager's layer is empty, and that is a finding.** No `Def_` node (§3), no legacy migration (both
homes were migrated by SET-AF9/this session), no promotion (the engines are public), no new module, no
new import. The only metadata work is **7 `spec-pin:` lines** — and, per the 2026-11-02 policy, **no
per-declaration markers** (playbook §5): every new row's `S_` file joins its home's header, and that is
the whole wire.

**Gates.** No tree build; each module's own `lake env lean -DautoImplicit=false
-DmaxHeartbeats=200000` silent and its own `flock`/`timeout 280 lake build`; `check_port --force` →
`0 mismatch / 0 missing` (baselines: `ArchCasimirComplex` 101 ok, `ArchDerivRightConv` 3 ok — the new
counts follow from the wire, so measure them); `#print axioms` on all seven headlines → `[propext,
Classical.choice, Quot.sound]`; zero warnings; `dedup`/`move_dead` per module; and one
`spec/AutomorphicFormSetAF10Consumer.lean` zone that composes the Casimir decomposition
(`archCasimirAtComplex + archCasimirBarAtComplex`) with the left-Casimir bridge on the same function.

### 5.1 The landing (2026-11-02)

**Files.** `ArchCasimirComplex.lean` 1,593 → **2,127** (+539: the `ElemC`/`CasLRC` prelude and five
headlines), `ArchDerivRightConv.lean` 1,169 → **1,291** (+126 −1, the one changed line the
`open NumberField.AdelicBox`), plus the new `spec/AutomorphicFormSetAF10Consumer.lean` (62 lines).
**27 declarations: 7 public headlines + 20 private helpers.**

**Gates, re-run by the manager.** `check_port --force` **106 ok / 0 mismatch / 0 missing**
(`ArchCasimirComplex`, baseline 101 + 5) and **5 / 0 / 0** (`ArchDerivRightConv`, 3 + 2); both files and
the consumer `lake env lean`-silent at the project caps (zero warnings); both module builds silent
(15.5 s / 6.9 s); `#print axioms` on **all seven** headlines `[propext, Classical.choice, Quot.sound]`;
`dedup --within` 0/0, `dedup --cross` over the two homes 0, `move_dead` 0/0; the consumer zone 0 errors.
Zero `-- pin:` markers in both files (the wires are 10 and 6), and no `set_option` suppression was
needed — none of the seven pin statements carries the `hw'` binder.

**FR-0115 recurred, and it is now measured twice.** 905 of the 915 in-port declaration lines were
imported as-is; **10 lines in 2 declarations** (`glArch_ext` pin `:930`, `rightTranslate_mul` pin
`:1162`) had to be re-stated `private` because their port copies live in `ArchCasimir.lean`, outside
this home's closure.

**The two re-statements were *tested* against the dedup rule, and the rule lost.** `dedup --cross`
between the two Casimir modules reports **6 clusters / 31 lines**: the four ℝ/ℂ twins (`U`, `D1`, `D2`,
`conjCLM`, type-distinct — not removable) and these two. The manager applied "delete the copy, import
the home" and **reverted it**: the port's copies are not at `AutomorphicForm.glArch_ext` but at
`AutomorphicForm.Elem17LR.glArch_ext` and `…OsAlg17.rightTranslate_mul` — inside the *transcription
namespaces* the pin's generated files created around each prelude — so `import …ArchCasimir` pulls a
1,640-line engine in and **still** leaves the six unqualified call sites unresolved. Ten private lines
are the cheaper and clearer shape; the promotion of those two helpers out of the transcription
namespace is a separate refactor with its own home and cascade. FR-0116.

**The re-read.** The demand side is the forecast to the line; the return is **one** row (AF9's was
seven):

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 884 / 356,213 | **877 / 354,646** | −7 / −1,567 ✓ (exact) |
| `needed [literal]` | 897 / 359,688 | **890 / 358,121** | −7 / −1,567 ✓ |
| frontier F | 1,531 / 771,153 | **1,538 / 772,720** | +7 / +1,567 ✓ (exact) |
| ready rows, all namespaces | 74 / 19,496 | 68 / 18,250 | −6 / −1,246 |
| `AutomorphicForm` ready rows | 45 / 14,152 | **39 / 12,906** | −6 / −1,246 |
| `AutomorphicForm` leaves | 72 / 15,039 | 72 / 15,039 | — ✓ (unchanged, as forecast) |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |

The one readied row is `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex`
(**321**, 6 premises): the complex twin of the real bridge SET-AF9 landed, waiting on the complex
commutator + the left-Casimir bridge this set wrote. That is a *narrow* return, and the honest reason
is visible in the numbers: AF10's rows sat at the end of a long chain (each row's premises were already
ported), whereas AF9's seven each needed two or more of its leaves. **A set's return is a property of
its position in the graph, not of its size** — the same lesson FR-0106 recorded, now with both
signs measured in consecutive sets.

## 6. Risk register

1. **The 21-declaration prelude is the only real work.** The big row is 1,204 declaration lines of which
   915 import; its 289 lines are the pin's `LeftCas`-prelude. Read them in dependency order (`Ld` first:
   it is a `def`, and `Ld_one`/`Ld_Ld_one`/`Ld_apply_lift`/`Ld_rightTranslate` build on it), and note
   that the pin's `Ld` on this side is *new* — SET-AF9 deleted the real side's `Ld` as a duplicate of
   `CommConv17.Lf`, so do not look for a twin.
2. **The fifteen-fold destructuring.** AF9's
   `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` concludes a 15-conjunct conjunction, and
   four of the six small rows open by destructuring it **positionally**
   (`obtain ⟨-, -, hEF, -, -, hEiF, hiEF, …, hiEiF, -, -, -⟩`); the big row cites the same headline
   twice. Copy the pin's position list verbatim — an off-by-one reads as a type error two lines later.
3. **`Del1`/`Del2` are `ArchCxGL.D1`/`D2`** (§2). Import.
4. **Two `set_option linter.unusedVariables` exemptions are expected**: the `∀ (w') (hw' : w' ≠ w)`
   binder the AF9 headlines carry and no proof step uses. Keep the binder spelled as the pin's (the
   checker compares spelling) and place the local option, as SET-AF9 did (`smooth_sub`) — this is the
   same class, and it is the only suppression this set should need.
5. **`w.IsComplex` is a hypothesis of five rows** and the six rows' proofs are stated at a complex
   place: do not generalise. The real-place twins are separate rows (SET-AF9's).
6. **The `solution` is the whole file** for six rows: the wrapper's statement is the public headline and
   the pin's `solution` body is its proof, exactly as the pin writes it. No `main` exists for them.
7. **No `set_option maxHeartbeats`, no `native_decide`**, no `sorry`; the complex engine is light
   (AF9's `ArchCasimirComplex` builds in 15.3 s at 1,588 lines).

## 7. What this set does not do

- **It does not take the Whittaker/Casimir quartet** — `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype`
  (695, leaf), `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` (347, leaf),
  `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` (404, leaf) and
  `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` (298, leaf) — **1,744 silo / 4
  leaves**. It is the *next* candidate and it is a different subject (the Casimir as an ODE on Whittaker
  functions, at both place types); it is named here with its size so the next scoping pass starts from
  the measurement rather than a re-read.
- **It does not take the three largest ready rows** — the Weyl-integrand integrability pair
  (1,349 + 1,291) and `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043); each is a
  consumer of a large unported development and a set of its own.
- **It does not take `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family`** (624, 3 premises,
  leverage 2/5) — Eisenstein series, another subject.
- **The 4 withheld rows / 831 silo** remain the prunable complex-analytic subject (`Pic0` torsion
  finiteness, the prescribed-divisor engine) — not this column's work.
- **No `Def_` node, no migration, no promotion, no new module, no new import** (§5).

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af9-landed.json` by `build/af10-shelf-appendix.py` (silo, premises,
leverage, disposition).

### The ready block — **45 rows / 14152 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` | 1227 | 1 | 2/4 | **SET-AF10** |
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
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4/12 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1/2 | deferred (§7) |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar` | 73 | 3 | 1/1 | **SET-AF10** |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero` | 70 | 1 | 1/1 | **SET-AF10** |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul` | 54 | 1 | 2/2 | **SET-AF10** |
| `archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt` | 51 | 3 | 2/3 | **SET-AF10** |
| `archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul` | 49 | 1 | 2/2 | **SET-AF10** |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex` | 43 | 1 | 1/2 | **SET-AF10** |
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
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | 2/2 | deferred (§7) |
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
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | 2/3 | deferred (§7) |
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
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | 1/1 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `whittakerCoefficient_unipotentGL2_mul` | 123 | 17/54 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | deferred (§7) |
| `continuous_whittakerCoefficient` | 108 | 3/14 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `whittakerCoefficient_sum_smul_of_continuous` | 86 | 10/17 | deferred (§7) |
| `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | 1/2 | deferred (§7) |
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
statement is not in the port, with its pin line and span. This is the order's transcription list.

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` | 1204 | 915 | 289 | 21 |
| `isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar` | 62 | 0 | 62 | 1 |
| `archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero` | 61 | 0 | 61 | 1 |
| `archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul` | 45 | 0 | 45 | 1 |
| `archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt` | 39 | 0 | 39 | 1 |
| `archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul` | 40 | 0 | 40 | 1 |
| `archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex` | 34 | 0 | 34 | 1 |
| **7 rows** | **1485** | **915** | **570** | **27** |

### `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex`

1204 declaration lines, 915 imported, **289 to write** in 21 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `Ld_Ld_one` | 45 | 1037 | theorem |
| `casimirs_apply` | 37 | 1091 | theorem |
| `leftCas_one` | 34 | 1128 | theorem |
| `archComplexGLAt_mul_comm_of_archComponent_eq_one` | 21 | 948 | theorem |
| `Ld_apply_lift` | 18 | 1011 | theorem |
| `hasDerivAt_negflow_mul_const` | 17 | 973 | theorem |
| `hasDerivAt_const_mul_negflow` | 16 | 990 | theorem |
| `casimirs_rightTranslate_any` | 15 | 1182 | theorem |
| `leftCas_eq` | 12 | 1205 | theorem |
| `solution` | 12 | 1217 | theorem |
| `exists_decomp` | 10 | 1172 | theorem |
| `Ld_one` | 8 | 1029 | theorem |
| `isArchSmoothAtComplex_rightTranslate_any` | 8 | 1197 | theorem |
| `glArch_archComplexGLAt` | 5 | 935 | theorem |
| `negflow_mul_lift` | 5 | 1006 | theorem |
| `archDelBarAt_apply'` | 5 | 1086 | theorem |
| `Ld_rightTranslate` | 5 | 1167 | theorem |
| `archComponent_glArch_archComplexGLAt_of_ne` | 4 | 940 | theorem |
| `glFin_archComplexGLAt` | 4 | 944 | theorem |
| `Ld` | 4 | 969 | def |
| `Ld_Ld_one_eq` | 4 | 1082 | theorem |

### `isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar`

62 declaration lines, 0 imported, **62 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 62 | 13 | theorem |

### `archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero`

61 declaration lines, 0 imported, **61 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 61 | 11 | theorem |

### `archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul`

45 declaration lines, 0 imported, **45 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 45 | 11 | theorem |

### `archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt`

39 declaration lines, 0 imported, **39 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 39 | 14 | theorem |

### `archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul`

40 declaration lines, 0 imported, **40 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 40 | 11 | theorem |

### `archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex`

34 declaration lines, 0 imported, **34 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 34 | 11 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af10.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex \
  --nodes AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar \
  --nodes AutomorphicForm.archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero \
  --nodes AutomorphicForm.archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul \
  --nodes AutomorphicForm.archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt \
  --nodes AutomorphicForm.archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul \
  --nodes AutomorphicForm.archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex \
  --json build/af10-advise.json
python3 port_plan.py --json build/af10-advise.json     # 1,567 raw / 1,478 decl / 892 in port / 586 net
python3 build/af-worklist.py leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex \
  isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar \
  archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero \
  archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul \
  archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt \
  archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul \
  archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
```

**Forecast on landing** (read after SET-AF9, §0.1): `needed` **884 / 356,213 → 877 / 354,646**
(−7 / −1,567), frontier **1,531 / 771,153 → 1,538 / 772,720**, the `AutomorphicForm` ready shelf
**45 / 14,152 → 38 / 12,585** (−7 / −1,567), the leaves **72 / 15,039 unchanged**, the withheld block
unchanged. What the set in turn *readies* is a re-read question, and by SET-AF9's experience it will
not be zero: the Casimir decomposition and the left-Casimir bridge are the premises of the
`archCasimirAt*`/`archDelAt*` rows still on the shelf.
