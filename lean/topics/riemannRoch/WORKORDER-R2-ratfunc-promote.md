# Work order — R2: promote the two `RatFunc` helpers (the last unverified pair)

**Status: ready to dispatch.** Tiny follow-up to `WORKORDER-R-refactor.md`. All of
phase 1 is landed and the milestone build is green (4830 jobs); checker
**2942 identical / 0 mismatched / 0 missing / 30 own-proof** (2972 checked).

## 0. The gap

Two pin-**public** declarations are port-**private**, with no public copy anywhere
and neither wrapper in `SOURCES`, so the 0/0 gate does not cover them:

| pin wrapper | pin-public name | port private copy |
|---|---|---|
| `Theorems/Thm_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty.lean` | `Place.eq_ofHeightOneSpectrum_or_eq_placeInfty` | `PrincipalDivisors/RatFuncDegree.lean:59` |
| `Theorems/Thm_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.lean` | `Place.placeInfty_ne_ofHeightOneSpectrum` | `PrincipalDivisors/RatFuncDegree.lean:76` |

The refactor round kept them private because their home (`RatFuncDegree.lean`, a
different effort's module) was outside its reopen set. That reason no longer holds:
the milestone is done, the tree is quiet, and the pair is the only remaining
pin-public/port-private gap.

They also have **private rebuilds** in `Genus/Stichtenoth.lean`:
`exists_ofHeightOneSpectrum_or_eq_placeInfty` (`:784`) and
`placeInfty_ne_ofHeightOneSpectrum'` (`:799`), whose consumers are at `:809`,
`:815`, `:833`.

## 1. Task

1. In `FLTForHuman/AlgebraicCurve/PrincipalDivisors/RatFuncDegree.lean`, drop
   `private` from the two declarations. **Before editing**, diff the port statement
   against the pin wrapper's statement (the checker's `norm`); they must be identical.
   If either differs, **stop and report** — do not respell it.

   **Authorized deviation (manager, after the stop report).** The diff found exactly
   one real discrepancy: `placeInfty_ne_ofHeightOneSpectrum` (`:76`) is written with
   **implicit** `{K : Type*}` while every pin copy (wrapper
   `Theorems/Thm_…_placeInfty_ne_ofHeightOneSpectrum.lean:12`, the public original
   `Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean:31`, and the pin's
   private `S_` copies) binds **explicit** `(K : Type*)`. The checker's `norm`
   distinguishes the two, and the port's binder form is therefore the drift.
   **Authorized:** change `:76` to explicit `(K : Type*)` — this is a statement change
   *toward* the pin (playbook §4: statements are the pin's), not a weakening — and
   pass `K` at the one internal call site `:102`
   (`placeInfty_ne_ofHeightOneSpectrum K w`). `eq_ofHeightOneSpectrum_or_eq_placeInfty`
   already matches (implicit `{K : Type*}` on both sides) and needs no change.
   Re-run the checker simulation first; expected `2944 identical / 0 mismatched`.
2. In `spec/check_flt_statements.py`, append to `SOURCES` the two `Theorems/Thm_*`
   wrappers **first**, then their pin `S_` sources (the pin repeats the dichotomy
   privately in its first three `S_` files; add the one the wrapper's statement
   lives in — `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean`
   is the provenance named in the port header — for the dotted-name fallback).
   `PORT_FILES` already contains `RatFuncDegree.lean`; confirm.
3. In `FLTForHuman/AlgebraicCurve/Genus/Stichtenoth.lean`, delete the two private
   rebuilds and rewire their consumers to the now-public
   `Place.eq_ofHeightOneSpectrum_or_eq_placeInfty` /
   `Place.placeInfty_ne_ofHeightOneSpectrum` from `RatFuncDegree` (Stichtenoth must
   already import it — H1b added that import; if not, add it).
4. Rebuild the touched modules under flock; run the checker; run `#print axioms` on
   the 14 headlines.

## 2. Acceptance

- Checker `0 mismatched / 0 missing`; identical count **2942 → 2944** (+2).
- No new `private` debt; no statement changed; no `sorry`/`admit`/`axiom`/`import
  Mathlib`/heartbeat override.
- The 14-headline `#print axioms` unchanged (`[propext, Classical.choice, Quot.sound]`).
- Friction entry under `## Refactor round` in `lean/logs/riemann-roch-friction.md`,
  and update the "Known residual" note in `topics/riemannRoch/PLAN-P1.md` §7 to say it
  is closed.

Build discipline as always: edit loop `timeout 120 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; probe only in `ScratchR2.lean`;
`flock /tmp/flt_for_human.lock timeout 180 lake build <module>`; no whole-tree build;
**no git command**.
