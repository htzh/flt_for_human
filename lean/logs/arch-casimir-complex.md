# The complex archimedean Casimir layer — definition pair, engine and the right-translate headline

**Status: landed 2026-10-18.** Three modules, green with 0 errors and 0 warnings:
`ArchDerivCasimirComplex.lean` (196 pin lines / 32 declarations),
`ArchDerivCasimirComplexAPI.lean` (381 / 46), and `ArchCasimirComplex.lean` (857 pin lines,
96 public engine declarations + 1 headline). No `sorry`, no axiom beyond
`[propext, Classical.choice, Quot.sound]`. Checker **10,342 identical**, 0 mismatched /
0 missing: the definition pair is **+78** and the headline **+1**; the engine's 96 declarations
are public tier 3 and registered (294 registered-unwired exempted).

| | |
|---|---|
| headline | `AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` |
| pin proof | `P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.lean` (857 lines) |
| statement authority | `Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.lean` |
| definition pair | `Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean` (196 / 32) and `…ComplexAPI.lean` (381 / 46) |
| structure | definition pair listed and checked; engine public tier 3; one wired headline |
| build | def 4.2 s, API 4.7 s, engine 6.3 s; 0 warnings |
| register | 96 engine declarations with `-- pin:` provenance, current |

## 1. What the theorem says

Right translation by `archComplexGLAt hw m` preserves, for every `m : GL (Fin 2) ℂ`:
complex archimedean smoothness, continuity of every first flow derivative, continuity of every
second flow derivative, and both the holomorphic and anti-holomorphic Casimirs:

```
archCasimirAtComplex hw (rightTranslate K (archComplexGLAt hw m) x)
  = rightTranslate K (archComplexGLAt hw m) (archCasimirAtComplex hw x)
archCasimirBarAtComplex hw (rightTranslate K (archComplexGLAt hw m) x)
  = rightTranslate K (archComplexGLAt hw m) (archCasimirBarAtComplex hw x)
```

This is the complex analogue of the real-place headline
`archCasimirAt_rightTranslate_archRealGLAt`; it is the engine the 35-file complex mirror of the
arch-Casimir fan rests on.

## 2. The definition pair

The target needs two pin `Definitions/` modules that the port did not have:

* `ArchDerivCasimirComplex.lean` — `archComplexGLAt`/`archComplexLiftAt`,
  `IsArchSmoothAtComplex`, the six-direction `ArchDirComplex` and its `toComplex`/`toComplexI`
  maps, `splitTorusGL2Complex`, `archFlowMatrixComplex`/`archFlowAtComplex`,
  `archDerivAtComplex`, `archDelAt`/`archDelBarAt`, `archCasimirAtComplex`/
  `archCasimirBarAtComplex`/`archKCasimirAtComplex`, and the circle subgroup;
* `ArchDerivCasimirComplexAPI.lean` — the complex mirror of the real API ladder: the flow-matrix
  derivative, the chain rule, linearity and smoothness algebra, commutation with the finite part,
  the left/right composition rules, `archComplexProjAt`, and the circle lemmas.

Both are transcribed verbatim at their pin namespace, with only the stub import replaced by
`FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir`. The only drift is `dif_pos`/`dif_neg` →
`dite_eq_left`/`dite_eq_right` (proof terms).

## 3. The engine, and the dedup finding

`port_advise` reports **no exact substitution** into the port: the real-place
`ArchCasimir.lean` has 43 declarations with the same names but **binder-spelling** differences
(`Matrix (Fin 2) (Fin 2) ℝ` versus `ℂ`, `ArchDir` versus `ArchDirComplex`). A normalized
line-for-line comparison gives a similarity of ≈0.38, and the complex half has extra material the
real engine does not have: `archDelAt`/`archDelBarAt`, `Del1`/`Del2`, the conjugate function,
`archCasimirBarAtComplex`, and the `archCasimirBar` transport. The duplication is **structural,
not textual**: both engines use the same chart/`D1`/`D2`/`AdM` architecture, but the complex types
and the two Casimirs make a generic `RCLike` rewrite a separate, risky refactor of the landed real
engine. The cut is therefore a separate complex engine, ported once, public tier 3, exactly in the
`ArchCasimir.lean` shape:

* `ArchCasimirComplex.lean` — 96 public declarations under `AutomorphicForm.ArchCxGL`, each with a
  `-- pin:` marker into the pin `S_` file; the checker exempts them (tier 3) and
  `spec/UNWIRED-PUBLIC.md` lists them;
* the headline is the only wired declaration;
* the engine imports `ArchDerivCasimirComplexAPI.lean` and
  `Mathlib.Analysis.Calculus.FDeriv.Symmetric` (the same one-module import the real engine needs
  for `ContDiffAt.isSymmSndFDerivAt`).

Two proof drifts: `by simp; norm_cast` → `by simp` in `D2_symm` (the `norm_cast` had no goals),
and one narrow `set_option linter.unusedVariables false in` on the headline (the wrapper's
`hxc : Continuous x` is unused by the `package` proof).

## 4. Verification

* edit loop: 0 errors / 0 warnings for all three modules;
* `lake build`: definition 4.2 s, API 4.7 s, engine 6.3 s;
* checker: **10,342 identical**, 0 mismatched / 0 missing, 10,678 checked; the definition pair is
  +78 and the headline +1, exactly the new wired surface;
* `#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`;
* `unwired_register.py --check`: current; 96 engine declarations registered;
* the frontier no longer lists the target.

## 5. What it buys

Set B of [TOPIC-arch-casimir.md](../topics/automorphicForm/TOPIC-arch-casimir.md) is now unblocked:
the definition pair is homed, the first headline is verified, and the engine is importable by the
rest of the complex fan. The remaining complex headlines are
`leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` (1,227 pin lines) and
`archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` (133), followed by the 35-file proof
fan (16,365 raw → 11,851 net). The real-place engine is untouched.
