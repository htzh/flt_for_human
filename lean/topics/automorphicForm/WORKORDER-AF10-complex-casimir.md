# WORKORDER-AF10 — the complex Casimir algebra closes

**Issued 2026-11-02, one dispatch.** Scope: [SET-AF10.md](SET-AF10.md) — §1 the seven rows, §2 the
price, §4 the homes, §6 the traps, and **Appendix B, the per-declaration worklist**. This order states
the work, the manager's landed layer, the traps and the gates.

**Audience.** A fresh coding session. Wire: each target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its statements. **No per-declaration markers** (policy 2026-11-02): the
header is the tracking, and nothing goes in source (playbook §5). Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The row count.** 7 rows, 1,567 silo, **570 lines / 27 declarations to write**; **915 of the 1,485
declaration lines are already in the port** and are imported, not transcribed. Six of the seven rows
are a single public declaration each — their `solution` from the pin is the whole proof.

## 0. The manager's layer, landed (do not redo it)

1. **The seven wires are in.** `ArchCasimirComplex.lean` carries 10 `spec-pin:` lines (5 were there;
   the five complex rows' `S_` files added), `ArchDerivRightConv.lean` 6 (4 there; the two real rows'
   files added). Both re-checked unchanged: **101 ok / 0 mismatch / 0 missing** and **3 / 0 / 0** — the
   new wires create no name collision with the existing declarations.
2. **The statements are verified, not assumed.** `lean/tmp/probe-af10-statements.lean` states all
   **seven** headlines as `example … := by sorry` — the statements lifted verbatim from their
   `Theorems/` wrappers — against exactly the two homes, and elaborates. Re-run it before you start;
   it is also the answer to "does this statement fit this module". Two things it settled: the two real
   rows need `open NumberField.AdelicBox` in `ArchDerivRightConv.lean`'s header (`NumberField.AdelicLevel`
   is already open, `adelicBox` is not), and nothing else is missing.
3. **No `Def_` node, no migration, no promotion, no new module.** `gate_scan` over the six `Def_`
   modules of the seven wrappers' closure: **0 missing**, max use 24/43 (`…ArchDerivCasimirComplexAPI`)
   and 17/32 (`…ArchDerivCasimirComplex`). Your only metadata edit is the `open` line above.

So the whole of your work is proof bodies in two existing modules, at the pin's statements.

## 1. What you write

**`AutomorphicForm/Adelic/ArchCasimirComplex.lean`** (append; five rows):

| pin `S_` file | work | shape |
|---|---:|---|
| `S_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex.lean` | **289** in 21 declarations | the pin's `LeftCas`/`CommC` prelude (`Ld`, `Ld_one`, `Ld_Ld_one`, `Ld_apply_lift`, `Ld_rightTranslate`, `casimirs_apply`, `leftCas_one`, `leftCas_eq`, `casimirs_rightTranslate_any`, `exists_decomp`, …) + `solution` |
| `S_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero.lean` | **61** in 1 | the compact Casimir at `iH`-weight `n` acts by `−(n²+2)` |
| `S_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul.lean` | **45** in 1 | the `∂̄∂` identity at weight `m` |
| `S_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul.lean` | **40** in 1 | its twin, `∂∂̄` |
| `S_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex.lean` | **34** in 1 | the Casimir decomposition |

**`AutomorphicForm/Adelic/ArchDerivRightConv.lean`** (append; two rows):

| pin `S_` file | work | shape |
|---|---:|---|
| `S_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar.lean` | **62** in 1 | smoothness + the Casimir identity of a character-typed right convolution, and its level/arch-cut membership |
| `S_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt.lean` | **39** in 1 | the Casimir commutes with right translation by a row isometry (every place) and with right convolution |

All seven headlines **public**, verbatim from their `Theorems/` wrapper, in `namespace AutomorphicForm`;
every helper `private`. No markers, no new module, no new import beyond the `open` of §0.2.

## 2. Traps

1. **The fifteen-fold conjunction.** `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` (AF9's)
   concludes a 15-conjunct conjunction, and four of the small complex rows open by destructuring it
   **positionally** (`obtain ⟨-, -, hEF, -, -, hEiF, hiEF, …, hiEiF, -, -, -⟩`); the big row cites the
   same headline twice. Copy the pin's position list verbatim — an off-by-one reads as a type error
   two lines later.
2. **`Del1`/`Del2` are the port's `ArchCxGL.D1`/`D2`** (`ArchCasimirComplex.lean:148`/`:220`, same
   signature; pin `:319`/`:322`). Import them; do not write them.
3. **The pin's `Ld` on this (complex) side is new.** SET-AF9 deleted the *real* side's `Ld` as a
   duplicate of `CommConv17.Lf`; there is no complex twin to look for, and the real module's deletion
   is not a precedent for dropping this one — read the pin's `LeftCas` prelude in dependency order
   (`Ld` is a `def`; `Ld_one`, `Ld_Ld_one`, `Ld_apply_lift`, `Ld_rightTranslate` build on it).
4. **`hw : w.IsComplex` is a hypothesis of five rows** and the complex rows are stated at a complex
   place; do not generalise — the real-place twins are separate rows, landed in AF9.
5. **One `set_option linter.unusedVariables false in` is expected** on the two headlines whose pin
   statement carries `∀ (w') (hw' : w' ≠ w)` and uses it in no step; keep the binder spelled as the
   pin's (the checker compares spelling) and place the local option, as AF9 did on `smooth_sub`. Report
   any further exemption with its pin line rather than adding it silently.
6. **`solution` is the whole file for six rows** — the wrapper's statement is the public headline and
   the pin's `solution` body is its proof; there is no `main` for them. The big row does have a
   prelude, and it is Appendix B's 21 declarations.
7. No `set_option maxHeartbeats`, no `native_decide`, no `sorry`/`admit`/`axiom`; zero warnings.
8. `p2m_open` → `open`/`open scoped`; `p2m_reactivate` lines are dropped.

## 3. Gates

1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` silent on both, then each
   module's own `flock .lake/flt_build.lock timeout 280 lake build
   FLTForHuman.AutomorphicForm.Adelic.<Module>`; **no tree build**, no dependents.
2. `spec/check_port.py --force` on both: `0 mismatch / 0 missing`, and the `ok` count grows by the
   public headlines you add (baselines 101 and 3 — measure, do not assume).
3. `#print axioms` on all seven headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on both modules.
5. `dedup.py` (`--within` and `--cross`) and `move_dead.py` per module; triage by the rule — dead
   mathematics → `Reserve/`, duplicate or plumbing → delete; report each disposition. Both modules were
   0/0 at the manager's landing, so any cluster is yours. Expect the known ℝ/ℂ `--cross` twins (`U`,
   `D1`, `D2`, `conjCLM`): they are type-distinct and stay.
6. `spec/AutomorphicFormSetAF10Consumer.lean` — one zone, a real composition, no `#check`: compose the
   **Casimir decomposition** (`archCasimirAtComplex + archCasimirBarAtComplex`) with the
   **left-Casimir bridge** on the same function `φ`. `lake env lean` it to zero errors.

## 4. Report

Per file: line counts, build time and silence; the two checker counts; the axioms block; `dedup`'s
clusters and `move_dead`'s dispositions; the consumer zone's error count; how many of the 915 in-port
declaration lines you imported as-is versus re-stated (and why, with the module the port's copy lives
in); every deviation from the pin with the pin line. **A blocker goes back immediately** — "blocked on
`<decl>` at pin `:NNN`; likely needs `<X>`", with the pin line and the error; do not grind out a
diagnosis, never work around a hub defect locally, and do not add an import or a module of your own.
