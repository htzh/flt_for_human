# WORKORDER-AF9 — the archimedean derivative algebra and the Casimir bridge

**Issued 2026-11-02, one dispatch, two orders in sequence.** Scope: [SET-AF9.md](SET-AF9.md) — read
§0 (the read and the FR-0114 caveat), §1 (the ten rows), §4 (the homes, with the measured migration)
and the two appendices (A = the shelf, B = the per-declaration worklist). This order states the work,
the manager's landed layer, the traps and the gates.

**Audience.** A fresh coding session. Wire: every target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its statements. **There are no per-declaration markers** (policy of
2026-11-02): a module's tracking is its `spec-pin:` lines, nothing else, and the grandfathered
`-- pin:` lines in the modules you touch are **stripped**, every file they named moving into the
header (§3.8). Pin clone `/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib
`v4.34.0`.

**The row count.** 10 rows, 2,503 silo, **≈1,380 lines / 105 declarations to write**; 911 of the 2,281
declaration lines are already in the port and are **imported, not transcribed** (SET-AF9 Appendix B is
per-row exact). This is a *composition* set: the pin's per-file preludes are the port's engine.

## 0. The manager's layer, landed (do not redo it)

1. **Two legacy modules migrated to `check_port`,** so their whole public surface is statement-diffed
   and your additions are checked against the pin:
   - `AutomorphicForm/Adelic/ArchCasimir.lean` — three `spec-pin:` lines; **131 ok / 0 mismatch / 0
     missing**; the one drift the migration found (`smooth_sub`'s unused binder spelled `_hθ`) is fixed
     to the pin's `hθ` with one local `set_option linter.unusedVariables false in`; header rewritten;
     build **9.6 s**, silent; `dedup` 0 clusters; `move_dead` 0.
   - `AutomorphicForm/Adelic/ArchCasimirComplex.lean` — one `spec-pin:` line; **97 ok / 0 / 0**; build
     **7.9 s**, silent; `dedup` 0; `move_dead` 0.
   Both are out of `spec/old_check_stmts.py`'s `PORT_FILES`, and `spec/UNWIRED-PUBLIC.md` is
   regenerated (114 → 112 modules).
2. **Order B's home is import-ready.** `AutomorphicForm/Adelic/ArchDerivRightConv.lean` now imports
   `ArchCasimir`, `Cusp.Constituent`, `NumberTheory.AdelicLevel.Level` and `…HeckeGen` (the Casimir
   engine and the cusp/level vocabulary of the second row's statement). It builds (7.4 s) and is still
   **1 ok / 0 / 0**.
3. **The surfaces are verified, not assumed** — keep these three probes and re-run them when a name
   will not resolve:
   - `lean/tmp/probe-af9-a.lean` — the eight leaves' vocabulary (`archDerivAt{,Complex}`,
     `archCasimirAt{,Complex}`, `archFlowAt{,Complex}`, `archDirMatrix{,Complex}`, `ArchDir{,Complex}`,
     `HasArchCharacterAt`, `rowIsometryInclAt₀`, `cuspKFiniteSubmodule`, `IsArchSmoothAt{,Complex}`,
     `archReal/archComplexLiftAt`, `archEntries`, `rightTranslate`) against the two Casimir modules;
   - `lean/tmp/probe-af9-b.lean` — order B's vocabulary (`productionPinsOf`, `levelInvariantSubmodule`,
     `levelOne`, `heckeGen`, `adelicBox`, `finiteAdelicGL2Subgroup`, `ArchTypeFamily.ofChar`,
     `IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor`) against
     `ArchDerivRightConv.lean` as it now stands;
   - `lean/tmp/probe-af9-statements.lean` — **both order-B headlines as `example … := by sorry`**: they
     elaborate, so the statements fit the home. That probe is also the warning FR-0112 earned: a
     `#check` list cannot see a missing instance; an `example` whose *statement* is the headline can.

## 1. Order A — the eight leaves (975 lines), two files

Transcribe the pin's `main` (the row) and the declarations Appendix B lists for that file; the rest of
each `S_` file is already imported. All eight headlines are **public** at their `Theorems/` wrapper's
statement; everything else stays `private` exactly as the pin has it. **No markers:** each new row's
pin `S_` file joins the module's `spec-pin:` header, and the old `-- pin:` lines go (§3.8).

**`AutomorphicForm/Adelic/ArchCasimir.lean`** (append; the four real leaves):

| pin `S_` file | pin lines | row declaration | work |
|---|---|---:|---:|
| `S_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt.lean` | 192 | `main` 185, `solution` 202 | **25** |
| `S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt.lean` | 162 | `main` 141, `solution` 178 | **117** |
| `S_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne.lean` | 82 | `solution` 96 | **16** |
| `S_AutomorphicForm_apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero.lean` | 91 | (`main` + `solution`) | **91** |

**`AutomorphicForm/Adelic/ArchCasimirComplex.lean`** (append; the four complex leaves):

| pin `S_` file | pin lines | work |
|---|---:|---:|
| `S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.lean` | 385 | **302** |
| `S_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one.lean` | 233 | **223** |
| `S_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne.lean` | 105 | **101** |
| `S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero.lean` | 100 | **100** |

`check_port` expectations after A: `ArchCasimir` **131 → 135 ok**, `ArchCasimirComplex` **97 → 101 ok**,
0 mismatch / 0 missing on both. If a count comes out different, a statement is not verbatim — fix it,
do not add a marker.

## 2. Order B — the two Casimir rows (405 lines), one file

**`AutomorphicForm/Adelic/ArchDerivRightConv.lean`** (append):

| pin `S_` file | row declaration | work |
|---|---|---:|
| `S_AutomorphicForm_archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt.lean` | `main` 649, `solution` 766 | **217** |
| `S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar.lean` | `solution` 73 | **188** |

Both headlines **public**, at the `Theorems/` wrapper's statement, in `namespace AutomorphicForm` (the
file's existing namespace); the helpers `private`. `check_port` expectation: **1 → 3 ok**, 0 / 0.

## 3. Traps

1. **The prelude is not work.** Each `S_` file's head is the pin's own copy of a prelude the port
   already holds (875 lines byte-identical): e.g. the real commutator leaf is 192 declaration lines of
   which **167 import and 25 are yours**. Appendix B is the exact per-declaration list — write from it,
   not from the file's top.
2. **`main` and `solution` are the rows' own proofs, not imports.** `port_advise` reports them as
   "same name" because unrelated port declarations are called `main`/`solution` (`TransvectionFrame.main`,
   `DeuringNormResidue.solution`). They are where the mathematics is; do not skip them.
3. **The complex bracket table** (`br_*`: 14 three-line `Matrix` identities plus four more) is the bulk
   of `archDerivAtComplex_commutator_of_isArchSmoothAtComplex`. The pin proves each with `ext i j;
   fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex, Matrix.mul_apply,
   Fin.sum_univ_six] <;> norm_num`-style steps. **No `native_decide`, no `set_option maxHeartbeats`**
   (measured: none of the ten pin files carries one). If a step does not fit the cap, the cost is
   instance inference — bisect it, do not raise the cap.
4. **Check the candidate, not just the missing name** (FR-0113): the pin's
   `IsLocallyConstant.comp_continuous` exists; `Continuous.comp_continuous` does not. Ask `#check` about
   the name you intend to write.
5. **`open scoped` instances** (FR-0112): the probes carry the instances the two orders need
   (`CompactSpace (ArchInfra.Kprod K)`, `IsFiniteMeasure (ArchInfra.muK K)`); if a proof needs another,
   add an `example` for it and keep going — do not weaken a statement to dodge an instance.
6. `p2m_open` → `open`/`open scoped`; `p2m_reactivate` lines are dropped. No `sorry`/`admit`/`axiom`/
   `native_decide` in any module.
7. Do not touch `ArchDerivCasimir{,Complex,ComplexAPI}.lean` (still legacy, not this set's business).
8. **No per-declaration markers, and strip the old ones** (policy 2026-11-02). `ArchCasimir.lean` and
   `ArchCasimirComplex.lean` carry ~150 and ~130 grandfathered `-- pin: <name> (<file>:<line>)` lines:
   delete every one (whole file, not only near your additions) and remove the header sentences that
   describe them. A marker was also naming the pin file its declaration came from, so **the strip and
   the wire are one edit**: every distinct file the markers named goes into the module's `spec-pin:`
   header, together with each new row's file. Measured, so you can tell a wire gap from a real
   failure: on `ArchCasimir.lean`, markers stripped with only its original three wires gives
   `132 ok / 0 mismatch / 3 missing` (each `missing` naming its file "(not in this wire)"); stripped
   with all six wires it is `135 ok / 0 / 0` over the same declaration set. The gate is therefore
   **0 mismatch / 0 missing**, not a particular `ok` count — and the cure for `missing` is a
   `spec-pin:` line, never a marker.

## 4. Gates

1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` silent for all three files, then
   each module's own `flock .lake/flt_build.lock timeout 280 lake build <module>`; **no tree build**, no
   dependents.
2. `spec/check_port.py --force` on all three: the counts in §0/§1/§2, 0 mismatch, 0 missing.
3. `#print axioms` on **all ten** headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on all three modules.
5. `dedup.py` (`--within` and `--cross`) and `move_dead.py` per module; triage by the rule — dead
   mathematics → `Reserve/`, duplicate or plumbing → delete; report each disposition. The two migrated
   modules were 0/0 at the manager's landing, so any cluster is yours.
6. `spec/AutomorphicFormSetAF9Consumer.lean` — one zone, a real composition, no `#check`: compose the
   **bridge** (order B's Casimir identity) with the **algebra** (order A's commutator relations), e.g.
   derive `archCasimirAt hw (rightConv K x f) = rightConv K (archCasimirAt hw x) f` *and* one of the
   commutator/character identities on the same `x`. `lake env lean` it to zero errors.

## 5. Report

Per file: line counts, build time and silence; the three checker counts; the axioms block; `dedup`'s
clusters and `move_dead`'s dispositions; the consumer zone's error count; **how many of the 911
in-port declarations you imported as-is and how many needed a re-statement, and why**; every deviation
from the pin with the pin line. **A blocker goes back immediately** — "blocked on `<decl>` at pin
`:NNN`; likely needs `<X>`" — with the pin line and the error; do not grind out a diagnosis, and never
work around a hub defect locally.
