# WORKORDER-AF11 — the Whittaker coefficient's API, and its archimedean differentiability

**Issued 2026-11-02, one dispatch.** Scope: [SET-AF11.md](SET-AF11.md) — §1 the nine rows, §2 the
price, §4 the home, §5 the cut, §6 the risk register, and **Appendix B, the per-declaration
worklist**. This order states the work, the manager's landed layer, the traps and the gates, and it
**corrects two measured claims of the set file** (§0.3 below: the definition gate is not free, and
one import the plan listed is on the wrong side of a cycle).

**Audience.** A fresh coding session. Wire: the target module carries its own `spec-pin:` header
and `spec/check_port.py` owns its statements. **No per-declaration markers** (policy 2026-11-02):
the header is the tracking, and nothing goes in source. Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The row count.** 9 rows, 1,595 silo, 1,413 declaration lines in the pin's `S_` files, of which
**146 are imported** and **1,267 stand in 49 declarations** by Appendix B. After the dedup the
manager measured (§1) the work is **~1,190 lines in 45 declarations**: 77 lines of that
worklist are the pin's four unused copies of a continuity lemma the port already has.

## 0. The manager's layer, landed (do not redo it)

1. **The wire is in, and the counts differ from the set file's forecast.** `WhittakerCoefficient.lean`
   carries **10 `spec-pin:` lines** — the pin `Definitions/` file plus the nine `Theorems/`
   wrappers — and `spec/check_port.py --force` on it gives **4 ok / 0 mismatch / 0 missing**: the
   module's coefficient definition layer. §4/§5 of the set expected 8; the other four declarations
   of the pin's definition file are now in their own module (§0.3), so **the landing target for this
   module is 4 + 9 = 13 ok / 0 mismatch / 0 missing**, not 17. Measure it; do not assume it.
2. **Two definition modules were added, both wired, both green.**
   * `NumberTheory/NumberField/GlobalAddChar.lean` — `IsPrincipalInvariantAddChar`,
     `IsGlobalAddChar` and the two degenerate cases (4 declarations), wire
     `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean`, **4 ok / 0 / 0**.
   * `RepTheory/LocalLanglands/UnramifiedWhittaker.lean` — the pin's `UnramifiedWhittaker` block:
     `heckeRecursionSeq`, `torusFactor`, `unipotent`, `diagZ`, `repSome`, `repInf`, `scalarPi`,
     `placeEmbed` (8 declarations), wire
     `Definitions/Def_UnramifiedWhittaker_HeckeRecursion.lean`, **8 ok / 0 / 0**.
3. **Why (the two corrections).**
   * **The definition gate was not free.** `gate_scan` over
     `Def_UnramifiedWhittaker_HeckeRecursion.lean` against the two `SmoothCuspRealizationAt.` rows:
     row 6 uses 3/8 (`placeEmbed`, `repSome`, `repInf`), row 7 uses 2/8 (`placeEmbed`, `scalarPi`),
     **4 missing from the port** — those four names are spelled in the rows' *statements*, so the
     rows could not even be stated. Ported as above; both rows now read **0 missing**.
   * **The import list had a cycle.** `NumberTheory/NumberField/AdelicTraceFin.lean` (needed by rows 5, 8 and 9
     for `NumberField.StandardAddChar.stdAddChar`) imports
     `AdelicTraceProducer` → `StandardGlobalAddChar` → `StandardGlobalAddCharRat`, and that module
     imported `WhittakerCoefficient`. The cycle was cut at the subject boundary: the pin's
     `Def_AutomorphicForm_WhittakerCoefficient.lean` is **one file with two subjects**, so its
     character-theoretic half (the two predicates) moved to `GlobalAddChar.lean` and
     `StandardGlobalAddCharRat.lean` imports that instead. That module was handed over on the way
     (`spec-pin:` added, `PORT_FILES` row retired, **44 ok / 0 / 0**).
4. **The statements are verified, not assumed.** `lean/tmp/probe-af11-statements.lean` states all
   **nine** headlines verbatim from their `Theorems/` wrappers as `example … := by sorry` against
   **the migrated module alone**, and elaborates silently (nine `declaration uses sorry` warnings,
   nothing else). Re-run it before you start: it is the answer to "does this statement fit this
   module", and it has already settled that the module's `open`s cover all nine.
5. **Imports are complete; add none.** The module now imports `ArchDerivCasimir`,
   `ArchDerivCasimirComplexAPI`, `AdelicMaximalCompact`, `Cusp/SmoothRealization`,
   `HeckeEigensystem`, `Siegel/Covering`, `WindowedSiegel/RowIsometry`,
   `NumberTheory/NumberField/AdelicTraceFin`, `NumberTheory/AdelicBox`,
   `NumberTheory/AdelicLevel/{HeckeGen,Level,Projections}`, `NumberTheory/AdelicDock/LocalEmbedding`,
   `RepTheory/LocalLanglands/{HeckeCosetLocal,HeckeCosetSystem,UnramifiedWhittaker}`,
   `NumberTheory/NumberField/GlobalAddChar`,
   `NumberTheory/AdelicModulus` (added at the worker's row-4 blocker: it supplies
   `NumberField.AdeleRing.distribHaarChar_algebraMap` and
   `NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`, and through
   `NumberTheory/AdelicHaar/ProductFormula` the port's `countable_principalSubgroup`), and
   `Mathlib.Analysis.Calculus.ParametricIntegral`. Its `open` list is the union of the nine
   wrappers' and includes `NumberField.AdelicBox`, `NumberField.AdelicLevel`, `LocalGL2`,
   `AdelicDock`, `AutomorphicForm.WindowedSiegel`, `AutomorphicForm.SiegelCovering` and
   `AutomorphicForm.SmoothCusp`. **If a proof needs something not reachable from here, that is a
   blocker** — report it, do not add an import.
6. **The metadata edits are done.** `PORT_FILES` rows for `WhittakerCoefficient.lean` and
   `StandardGlobalAddCharRat.lean` retired (with comments), `spec/UNWIRED-PUBLIC.md` regenerated,
   the frozen checker unchanged at 3 mismatched / 18 missing (all pre-existing, all in
   `AlgebraicCurve/`), `dedup --within` 0 clusters and `move_dead` 0 declarations on all four
   touched modules. **You owe no hub edit.** If you believe you need one, stop and report: it is
   the manager's.

## 1. What you write

All of it is **proof bodies** in `FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean`, at
the pin's statements, appended below the two definition lemmas. The nine headlines are **public**
and keep their pin names (rows 5, 6 and 7 inside `namespace AutomorphicForm`, with
`namespace RankinSelberg` / `namespace SmoothCuspRealizationAt` for those three). **Every helper is
`private`** — that is what keeps the checker's count at 4 + 9: a `private` declaration is not diffed,
and a public helper whose statement is not in one of the ten wired files would be a `missing`.

**Land in this order.** The transformation law first (rows 4, 5, 6, 7 rewrite with it), then the two
cheap algebraic rows, then the realizations, then the two differentiability rows last (they are the
only analytic risk, and they are the largest).

| # | row (`AutomorphicForm.` dropped) | pin `S_` file | worklist | shape |
|---|---|---|---:|---|
| 1 | `whittakerCoefficient_unipotentGL2_mul` | `S_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul.lean` | **95** / 6 | prelude: `addChar_neg_eq_conj` (4), `setIntegral_adelicBox_comp_add_right` (29), `integral_cond_adelicBox_comp_add_right` (7) + the headline (36) |
| 2 | `whittakerCoefficient_sum_smul_of_continuous` | `S_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous.lean` | **74** / 2 | one 52-line proof over finite sums of integrable terms |
| 3 | `continuous_whittakerCoefficient` | `S_AutomorphicForm_continuous_whittakerCoefficient.lean` | **97** / 2 | one 76-line dominated-convergence proof |
| 4 | `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | `S_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul.lean` | **180** / 15 | prelude: `diagGL2` (3), `principalIdeleOf` (3), `infra` lemmas + the 53-line headline |
| 5 | `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | `S_AutomorphicForm_RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery.lean` | **114** / 5 | `gl_ext` (15, already in the port as a `private`), `whittakerCoefficient_mul_right` (6), `glArch_unipotentGL2_eq_one` (6), `mul_comm_of_glArch_eq_one_of_glFin_eq_one` (7) + the 80-line headline |
| 6 | `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | `S_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient.lean` | **132** / 1 | one 132-line proof; no prelude at all |
| 7 | `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | `S_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient.lean` | **63** / 2 | `placeEmbed_scalarPi_eq_centralScalar_det` (32) + the 31-line headline |
| 8 | `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | `S_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt.lean` | **279** / 8 | prelude: `archFlowAt_coe_apply`, `archFlowAt_neg`, `continuous_archFlowMatrix_apply`, `continuous_archFlowAt`, `hasDerivAt_flow_of_isArchSmoothAt`, `hasDerivAt_setIntegral_flow` (69) + the 131-line headline |
| 9 | `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | `S_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex.lean` | **376** / 8, of which **143 in the port** | the complex mirror; `hasDerivAt_setIntegral_flowComplex` (75) + the 66-line headline over the port-once block |

**What the worklist does not charge you, and this order does** (drop these, do not transcribe them):

1. **`solution`** — every row's last declaration is the pin's proof of that row's headline, with the
   same statement. Its body becomes the headline's body; there is no `solution` in the port.
2. **The pin's four copies of `continuous_unipotentGL2`** (rows 2, 3, 8, 9 — 22/21/17/17 lines). The
   port has **one** at `AutomorphicForm.continuous_unipotentGL2`
   (`AutomorphicForm/Adelic/ConstantTerm.lean`, general over `[CommRing R] [TopologicalSpace R]
   [ContinuousNeg R]`, which is strictly weaker than the pin's `[IsTopologicalRing A]`), already
   imported. Use it; write no copy. **That is 77 of the 1,267 lines (and 4 of the 49 declarations), and the
   reason the effective count is ~1,190 / 45.**
3. **The pin's `countable_numberField` / `countable_principalSubgroup` / `productionPinsOf_ν`**
   (row 1's three imported declarations): the port has all three
   (`NumberField.TateGlobal.countable_numberField`, `NumberField.countable_principalSubgroup`,
   `AutomorphicForm.productionPinsOf_ν`). One of them needs a binder spelling, not a proof.
4. **The 12 substitutions of row 9** (143 lines) are the port-once block of the complex archimedean
   prelude, byte-identical in `ArchDerivCasimirComplexAPI.lean`:
   `isArchSmoothAtComplex_archDerivAtComplex`, `IsArchSmoothAtComplex.differentiableAt_flow`,
   `hasDerivAt_archFlowMatrixComplex_apply`, `archComplexLiftAt_mul_archComplexGLAt`,
   `hasDerivAt_of_symm_mul_archFlowMatrixComplex`, `archComplexLiftAt_of_symm_one`,
   `archDirMatrixComplex`, `contDiff_of_symm_mul_const_complex`,
   `hasDerivAt_cexp_neg_ofReal_mul_const`, `hasDerivAt_cexp_ofReal_mul_const`,
   `hasDerivAt_ofReal_mul_const`, and the binder-spelled `countable_numberField`. **Import them; do
   not re-transcribe them.**

## 2. Traps

1. **The two parametric-integral rows are the only analytic risk** (279 and 233). Both are
   dominated-convergence proofs of "differentiate under the integral". Go to mathlib first
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` and the `ParametricIntegral` API, just
   imported) and then to the port's own engines (`hasDerivAt_integral_*`,
   `contDiff_parametricIntegral_*` in `AutomorphicForm/Adelic/RightConvRegularity.lean` and
   `ConvolutionLimit`-shaped modules) before transcribing the pin's hand-rolled bound. The real twin
   has **no** port-once block (§0.3 of the set): only the complex one does.
2. **`AdelicTraceFin` is the first consumer here** (row 5, and `stdAddChar` in rows 5, 8, 9). Read
   its API — `traceInt`, `traceFinHom`, `adelicTrace`, `stdAddChar`, `psiK_algebraMap` — before
   transcribing the trace manipulations; the shell-surgery proof rewrites the trace, not the
   integral.
3. **Row 4 is the one place a wrong first rewrite costs the whole proof.** Its chain starts from
   `whittakerCoefficient` at `α ≠ 0` and rewrites through the transformation law to `α = 1`
   at `globalPoints (diagOne α) * g`; the prelude's `principalIdeleOf` (the `α`-adic class) and
   `diagGL2` are small `def`s the pin defines locally, and its `measurePreserving`/`image` lemmas
   are about `x ↦ principalIdeleOf α • x` on the box. The 15 declarations are in Appendix B; follow
   the pin's order.
4. **Rows 5, 6, 7 keep their consumers' namespaces.** `AutomorphicForm.RankinSelberg.…` and
   `AutomorphicForm.SmoothCuspRealizationAt.…` are what the checker reads; do not "simplify" them
   into the flat namespace and do not move the declarations to another module.
5. **Row 6's `hloc` steps compare the new `UnramifiedWhittaker.repSome`/`repInf` with
   `LocalGL2.localRepSome`/`localRepInf`** by `Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
   simp [...]`; both are now in scope (`RepTheory/LocalLanglands/{UnramifiedWhittaker,
   HeckeCosetLocal}.lean`, the second already imported through `HeckeCosetLocal`). The two pairs are
   type-distinct on purpose (`π : K` versus `algebraMap R K ϖ`); the equality is the pin's inline
   `hloc` in row 6 and must be proved there, not promoted.
6. **The pin's `attribute [local instance]` lists are not scaffolding to copy wholesale.** In the
   port `NumberField.AdelicHaar.adeleBorel` / `glBorel` / `ideleBorel` are `def`s, not instances;
   register one locally only where a proof needs the measurable space (`letI := pins.nS`,
   `attribute [local instance] NumberField.AdelicHaar.adeleBorel`). `p2m_open` → `open`;
   `p2m_reactivate` lines are dropped.
7. **Row 5's statement has nine `_`-named hypotheses** (`_hk₀`, `_hWpt`, `_hκ`, `_haexp`, `_hysupp`,
   `_hWmult`, `_hμbox`, `_hboxvan`, `_hxsum`); they are `_`-prefixed in the wrapper precisely so the
   port does not need a `linter.unusedVariables` suppression. If a statement you transcribe turns
   out to need one, report it with its pin line instead of adding it silently.
8. **Row 7's `diagPi` is the port's `LocalGL2.diagPi`** (already imported), and row 7's
   `hgen` hypothesis is *its* statement, not the pin's `scalarPi` one.
9. No `set_option maxHeartbeats`, no `native_decide`, no `sorry`/`admit`/`axiom`; zero warnings; no
   new module, no new import, no hub edit.

## 3. Gates

1. `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
   FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean` silent, then its own
   `flock .lake/flt_build.lock timeout 280 lake build
   FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient`; **no tree build**, no dependents.
2. `python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean`:
   `0 mismatch / 0 missing`, **ok count 4 + however many headlines you land** (target **13** if all
   nine resolve by statement; measure, do not assume). Also re-check the two managers' modules are
   untouched: `GlobalAddChar.lean` 4 ok, `UnramifiedWhittaker.lean` 8 ok.
3. `#print axioms` on all nine headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on the module.
5. `dedup.py --within` and `move_dead.py` per module over the module: report every cluster and
   disposition. The manager's landing is 0/0, so any cluster is yours; dead *specialized*
   mathematics goes to `Reserve/`, port plumbing is deleted, and a general lemma that rounds out an
   API is kept in place with the reason recorded in your report.
6. `spec/AutomorphicFormSetAF11Consumer.lean`, **one zone**, a real composition with no `#check`
   and no `sorry`: compose the **transformation law** (row 1) with the **real differentiability
   identity** (row 8) — rewrite the derivative of `t ↦ whittakerCoefficient … (g₀ * archRealGLAt hw
   (h * archFlowMatrix d t))` through the transformation law at a unipotent factor, so the zone's
   conclusion is a derivative identity *obtained by rewriting with the API*, not a restatement of
   either headline. The natural instantiations are row 8 at `unipotentGL2 x * g₀` and row 1 at
   `g = g₀ * archRealGLAt hw (h * archFlowMatrix d t)`; if the one you pick forces a hypothesis the
   two headlines do not provide (`hper` uniform in `t`, say), **report it at first belief** instead
   of weakening either headline. It imports the coefficient module only; `lake env lean` it to zero
   errors.
7. `lean/tmp/probe-af11-statements.lean` still elaborates (nine `sorry` warnings, nothing else).

## 4. Report

Per row: lines written, declarations written and their public/`private` split, which worklist
entries you **dropped** and why (the four classes above), and the pin line of every deviation. Then
the module's build time and silence; the checker counts (before 4, after whatever you measure);
the nine `#print axioms` blocks; `dedup`'s clusters and `move_dead`'s dispositions; the consumer
zone's error count; and one paragraph on the two parametric-integral rows — whether the port's
engines carried them or the pin's bound was transcribed, with the reason.

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with
the pin line and the error. Do not grind out a diagnosis first, never work around a hub defect
locally, and do not add an import, a module, or a `set_option`.
