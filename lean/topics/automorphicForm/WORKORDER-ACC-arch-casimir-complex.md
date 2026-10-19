# WORKORDER-ACC — the complex archimedean Casimir layer

One set: the missing complex definition pair, the complex Casimir engine, and its first headline.
Mathematics and landing record: [../../logs/arch-casimir-complex.md](../../logs/arch-casimir-complex.md);
subject: [TOPIC-arch-casimir.md](TOPIC-arch-casimir.md) §4–§5 (Set B); column:
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3.

**Status: landed 2026-10-18.**

## 1. Scope

| | |
|---|---|
| headline | `AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` |
| pin proof | `P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.lean` (857 lines, 97 declarations) |
| statement authority | `Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.lean` (29 lines) |
| definition pair | `Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean` (196 / 32) and `…ComplexAPI.lean` (381 / 46) |
| expected checker delta | **+79** = +78 definition pair, +1 headline |

**Not this set:** the other complex headlines
(`leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` 1,227,
`archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` 133), the 35-file complex fan, and
any change to the landed real `ArchDerivCasimir.lean`/`ArchCasimir.lean`.

## 2. The definition pair first

The target's wrapper imports `Def_AutomorphicForm_ArchDerivCasimirComplex` and the `S_` file also
imports `…ComplexAPI`; **neither was ported**, although the frontier priced the target as `--ready`
(this is the §4(a) import-only-definition blindness, not a last-name artefact). Both modules import
only the already-ported `Def_AutomorphicForm_ArchDerivCasimir`, so the wave homes them whole:

* `ArchDerivCasimirComplex.lean` — the complex transport, smoothness, six directions, flows,
  derivatives, the two Casimirs, and the circle subgroup;
* `ArchDerivCasimirComplexAPI.lean` — the complex API ladder.

They are transcribed verbatim at the pin namespace, checked by name against their `Definitions/`
files. Only `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right` drift.

## 3. The engine and the dedup finding

`port_advise` reports **0 substitutions** and 43 **binder-spelling** variants against the landed
real `ArchCasimir.lean` (`ℝ` versus `ℂ`, `ArchDir` versus `ArchDirComplex`). A normalized comparison
is only ≈0.38 similar: the complex engine has additional `archDelAt`/`archDelBarAt`,
`Del1`/`Del2`, the conjugate-function transport and `archCasimirBarAtComplex`. The duplication is
architectural, not textual; a generic `RCLike` rewrite of the real engine is a separate, risky wave.

The cut therefore mirrors `ArchCasimir.lean`:

* one module `ArchCasimirComplex.lean` (857 pin lines, 96 public engine declarations + 1 headline);
* the engine is public under `AutomorphicForm.ArchCxGL`, each declaration carrying a
  `-- pin: P2MW.S_…ArchCxGL.<name> (<S_ file>:<line>)` marker into the pin `S_` file;
* the `S_` file is **not** in `SOURCES`, so the checker exempts the engine (tier 3) and
  `spec/UNWIRED-PUBLIC.md` lists it; the headline is the only wired declaration;
* imports: `ArchDerivCasimirComplexAPI.lean` plus
  `Mathlib.Analysis.Calculus.FDeriv.Symmetric` (the same single mathlib import the real engine
  needs for `ContDiffAt.isSymmSndFDerivAt`).

## 4. Drift

* `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right` in the definition pair;
* `by simp; norm_cast` → `by simp` in the complex `D2_symm` (the `norm_cast` had no goals);
* one narrow `set_option linter.unusedVariables false in` on the headline (`hxc` is unused by the
  `package` proof);
* no heartbeat override, no `import Mathlib` bare, no `sorry`/`admit`.

## 5. Build discipline

* edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`;
* `flock .lake/flt_build.lock timeout 300 lake build <module>` (definition pair first, then the
  engine);
* no whole-tree build.

## 6. Wiring

* `SOURCES`: the two `Definitions/` modules and the headline wrapper; the engine `S_` file stays
  unlisted;
* `PORT_FILES`: the two definition modules and the engine;
* run `python3 ../tools/deps/unwired_register.py` to write the 96 engine rows.

## 7. Results

* edit loop: 0 errors / 0 warnings;
* `lake build`: definition 4.2 s, API 4.7 s, engine 6.3 s;
* checker: **10,342 identical**, 0 mismatched / 0 missing, 10,678 checked (+78 definition pair,
  +1 headline); 294 registered-unwired exempted (the 96 engine declarations plus the existing 198);
* `#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`;
* register current; the frontier no longer lists the target.

## 8. Successors

`leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` (1,227 pin lines), the
133-line `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne`, and then the complex proof
fan (35 files, 16,365 raw → 11,851 net). The complex `_rowIsometryInclAt_of_ne` row is the smallest
next leaf; the 1,227-line `leftCasimirComplex` is the structural successor of this headline.
