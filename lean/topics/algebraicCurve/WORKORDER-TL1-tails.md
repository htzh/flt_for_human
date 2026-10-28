# WORKORDER TL1 — the tails: five fragments, each the last public declaration of an engine the port already has

Scope: **one new module** and **five insertions**, three of them into registered-unwired modules that the
manager wires before dispatch. Nothing else may be edited. (Part of SET 5, [SET-5.md](SET-5.md) §1 — reviewer's call 5 cut
the `FunctionField` pair here; call 6 kept the order at eleven rows.)

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | home |
|---|---|---:|---|
| `AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom` | `S_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom` | 162 | **new** `FLTForHuman/AlgebraicCurve/FunctionField.lean` |
| `AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_sum_lifts` | `S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts` | 127 | insert into `Differential/PushPull.lean` |
| `AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor` | `S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor` | 65 | insert into `Defs/AdelicIndex.lean` |
| `AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq` | `S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq` | 25 | **new** `FunctionField.lean` |
| `AlgebraicCurve.Divisor.support_pushforward_subset` | `S_AlgebraicCurve_Divisor_support_pushforward_subset` | 14 | insert into `Defs/PushPull.lean` |
| `AlgebraicCurve.Divisor.evalFun_add` | `S_AlgebraicCurve_Divisor_evalFun_add` | 13 | insert into `Defs/PlaceEvaluationAlgebra.lean` |
| `AlgebraicCurve.Divisor.evalFun_zsmul` | `S_AlgebraicCurve_Divisor_evalFun_zsmul` | 12 | insert into `Defs/PlaceEvaluationAlgebra.lean` |
| `AlgebraicCurve.hasCanonicalLocalResidueK` | `S_AlgebraicCurve_hasCanonicalLocalResidueK` | 12 | insert into `LocalResidue/Instance.lean` |
| `AlgebraicCurve.Divisor.support_pullback_subset` | `S_AlgebraicCurve_Divisor_support_pullback_subset` | 11 | insert into `Defs/PushPull.lean` |
| `AlgebraicCurve.Place.pairwiseDisjoint_fiber` | `S_AlgebraicCurve_Place_pairwiseDisjoint_fiber` | 10 | insert into `Defs/PushPull.lean` |
| `AlgebraicCurve.Divisor.evalFun_ne_zero` | `S_AlgebraicCurve_Divisor_evalFun_ne_zero` | 9 | insert into `Defs/PlaceEvaluationAlgebra.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements come from each node's
`Theorems/Thm_<stem>.lean` wrapper**, proofs from the `S_` file.

**The mathematics.** Five fragments, unrelated except in character — each is the last public
declaration of a development the port already carries: the `RatFunc K →ₐ[K] F` layer (existence from
a transcendental element over an algebraically closed base, and finiteness of the transported
module), the trace/pullback identity for differentials along a finite separable along-map, the
pole-divisor filtration of `LSpace`, the support of a pushforward/pullback and pairwise disjointness
of fibres, the `evalFun` laws on divisors, and the canonical local residue instance.

## The four alias rows — surface, not proof

Four rows' **mathematics is already in the port**; only the pin's names are missing. Write the
pin-named statement as a one-line public declaration over the existing proof, in the module that
holds it — this is what the surface rule asks for (SET 4's BC9b precedent), and it is the whole of
these four rows:

| row | already in the port | what to write |
|---|---|---|
| `Divisor.evalFun_add` | `evalFun_add_of_forall_ne_zero` (`Defs/PlaceEvaluationAlgebra.lean`) — statement-identical, different name (the pin's *definitions* layer names it so) | the wrapper-named statement |
| `Divisor.evalFun_zsmul` | `evalFun_zsmul_divisor` (same module) | idem |
| `Divisor.evalFun_ne_zero` | `evalFun_ne_zero_of_forall_ne_zero` (same module) | idem |
| `hasCanonicalLocalResidueK` | the unconditional `instHasCanonicalLocalResidueK` (`LocalResidue/Instance.lean:453`) — the pin's whole proof is `inferInstance` | `inferInstance` at the pin's binders |

## Why these homes (do not re-home them)

- **`AlgebraicCurve/FunctionField.lean`**, `namespace AlgebraicCurve.FunctionField`: the port has no
  home for the `RatFunc`-algHom layer — `Defs/RatFuncPlaces.lean` is the ℙ¹ *place* vocabulary and
  `PrincipalDivisors/RatFuncDegree.lean` the place/degree theory. Both pin files import `Mathlib`
  only, so the module needs no FLT import; it will be what the Weil-reciprocity development
  (`weilReciprocity`, `exists_weilPairing`, which consume these two rows and are not ported)
  imports. Add `import FLTForHuman.AlgebraicCurve.Defs.Place` only if a proof needs `Place`.
- **`Differential/PushPull.lean`** defines `pullbackAlong` / `traceAlong` and imports
  `Defs/Correspondence` (for `FiniteAlong` / `SeparableAlong`). It is **registered-unwired**: the manager wires it
  before dispatch; append this node's wrapper and `S_` file to that block.
- **`Defs/AdelicIndex.lean`** defines `LSpace` (abbrev) and `mem_lSpace_iff_ord`; the leaf is the
  pole-divisor filtration of that space. Registered-unwired, wired by the manager before dispatch; append the pair.
- **`Defs/PushPull.lean`** defines `pushforward` (and `pushforward_apply`), `pullback`, `fiber`
  (546) and the `restrict` dictionary the three leaves use. It is a hub (29 importers), so the
  insertion's price is re-elaboration, not a cycle.
- **`Defs/PlaceEvaluationAlgebra.lean`** is the module of the `evalFun_*` laws (its header already
  carries one wrapper statement for exactly this reason). Registered-unwired; the manager's wire
  lists the six `Theorems/Thm_AlgebraicCurve_Divisor_evalFun_*` wrappers before dispatch — extend it,
  do not rewrite it.
- **`LocalResidue/Instance.lean`** (1,690 lines, 1 `spec-pin:` line) holds the instance.

**Import, do not copy** — the prelude blocks the pin files re-spell:

- `Differential/PushPull.lean` / `Defs/Correspondence.lean`: `traceAlong_smul_pullbackAlong` (18),
  `pullbackAlong_single` (24), `pushforwardAlong_single` (20), `isPrincipal_pushforwardAlong` (19),
  `correspondence_mem_principal` (18), `SeparableAlong` / `finrankAlong` (16 each);
- `Defs/AdelicIndex.lean`: `residuePairing` (19), `residuePairing_injective` (20),
  `weilSmul_mem_omegaSpace_{add,_of_mem_lSpace}` (19 / 25), `adeleBdd` (15);
- `Defs/LocalResidue.lean`: `kaehlerResidueTermKFam_support_subset` (22),
  `kaehlerResidueTermKFam_eq_zero_of_adeleBdd_canonical` (17), `weilOfKaehlerK` (18);
- `Defs/PushPull.lean` / `P1/EnginePrelude.lean`: `isPrincipalIdealRing_comap` (51),
  `restrict_fiber_finite` (36), `irreducible_mk_comap` (35), `ord_restrict` (34),
  `ramificationIndex_dvd_ord` (30), `SumRamificationInertia` (29), `isUnit_mk_comap_iff` (25),
  `isPrincipal_pushforward_of_normFormula` (24), `pullback_mem_degZero` (22), `pullback_apply` (13).

`Divisor.support_pushforward_subset`'s proof uses `Finsupp.mem_support_iff` and `pushforward_apply`;
`support_pullback_subset` uses `restrict_mem_support_of_mem_support_pullback` and
`restrict_mem_fiber`; `pairwiseDisjoint_fiber` uses `Place.mem_fiber`. All are in the port — import
them, and do not restate `Place.fiber_eq_fiberOver` (a recorded deliberate omission, CARRY-FORWARD).

## Rules

- The new module: header `/- … -/` with prose and `spec-pin:` lines for both wrappers and `S_` files
  of its two nodes, no cross-references to port modules or notes; `set_option autoImplicit false`,
  `noncomputable section`.
- Insertions: append and add each node's wrapper **and** `S_` file to the module's `spec-pin:` block;
  keep every existing declaration untouched.
- Universe and binder spelling from the wrapper, character for character. The three `evalFun` rows
  and `hasCanonicalLocalResidueK` are *surface*: their bodies are one line, and their statements
  must be the wrappers' verbatim (the pin's `Divisor.evalFun_add` has its own binder layout, which
  the existing `…_of_forall_ne_zero` copy already matches).
- Imports stay specific: **never `import Mathlib`** in a library module. Replace the pin's
  `import Mathlib` (and any broad import a `S_` file carries) with the specific mathlib modules the
  file needs — playbook §4's hygiene rule.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished modules `flock .lake/flt_build.lock timeout
  110 lake build <module>`. Every command under 2 minutes, its own `timeout`, no loops; logs under
  `lean/tmp/tl1-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module, every added
  declaration `ok`; `#print axioms` on all eleven headlines → `[propext, Classical.choice,
  Quot.sound]`; 0 warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; no commit; no
  `spec/decl_markers.tsv` row.
- If a proof needs a `private` port helper or a declaration below its home, **stop and report** —
  do not promote, do not restate, do not edit a hub.

## Report (one message)

per file: build + warnings, the checker summary line, declarations added; the eleven axioms lines;
the four alias rows confirmed as one-liners (or the statement difference that stopped them); any
blocker.
