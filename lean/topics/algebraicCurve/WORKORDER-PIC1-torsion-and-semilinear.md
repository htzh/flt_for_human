# WORKORDER PIC1 — the torsion of `Pic0`, the Weil datum, and the semilinear action

Scope: **two new modules** and **five insertions**. Nothing else may be edited. (Part of SET 5,
[SET-5.md](SET-5.md) §1; the `WeilDatum` definition module is the definition gate of
SET-5 §0.1 and is transcribed here as the order's first step.)

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero` | `S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero` | 79 | 7 (6 `private`) | **new** `FLTForHuman/AlgebraicCurve/Pic0/Torsion.lean` |
| `AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow` | `S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow` | 67 | 1 | **new** `Pic0/Torsion.lean` |
| `AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul` | `S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul` | 35 | 1 | **new** `Pic0/Torsion.lean` |
| `AlgebraicCurve.Pic0.torsion.move_of_forall_isRational` | `S_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational` | 26 | 1 | insert into `Place/OrderArithmetic.lean` |
| `AlgebraicCurve.WeilDatum.symm_pairing` | `S_AlgebraicCurve_WeilDatum_symm_pairing` | 9 | 1 | **new** `Defs/WeilDatum.lean` (with the definition) |
| `AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul` | `S_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul` | 151 | 11 (1 `private`) | insert into `Defs/Correspondence.lean` |
| `AlgebraicCurve.SemilinearAut.pushforwardAlong_smul` | `S_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul` | 17 | 1 | insert into `WeilExchange/GaloisRamification.lean` |
| `AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place` | `S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place` | 14 | 1 | insert into `Defs/SemilinearAut.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements come from each node's
`Theorems/Thm_<stem>.lean` wrapper**, proofs from the `S_` file.

**The mathematics.** Four pieces of the same `Pic0`/`SemilinearAut` complex: the torsion of `Pic0`
is finite when it is finite on every prime power; an `n`-torsion class whose divisor representative
is fixed has a function whose orders are `n` times that representative; a torsion class can be
moved off a finite set of places with rational support; the `WeilDatum` pairing is inverted by
`d.symm`; and a semilinear automorphism commutes with the `pic0` correspondence in `g`, in the
along-version of SET 4's `pushforward_smul`, and on places through `ofAlgAut`.

## Why these homes (do not re-home them)

- **`Place/OrderArithmetic.lean`** (771 lines, 8 `spec-pin:` lines, 2 importers) holds
  `Pic0.exists_mk_eq_forall_notMem_support` — SET 4's moving lemma, this node's premise. The node adds
  the rationality clause; the pair belongs together, and anything above must import that module.
- **`Defs/Correspondence.lean`** (the `algebraAlong` / `Divisor.pullbackAlong` /
  `Pic0.correspondence` / `IntertwinesAlong` API) is the node's own subject. It is
  **registered-unwired**: the manager has added its wire before dispatch, and the worker appends the
  node's wrapper and `S_` file to it.
- **`WeilExchange/GaloisRamification.lean`** (245 lines, 11 `spec-pin:` lines) holds SET 4's
  `SemilinearAut.pushforward_smul`; this node is its along-version.
- **`Defs/SemilinearAut.lean`** (511 lines, 2 `spec-pin:` lines) is `SemilinearAut.ofAlgAut` and the
  `smul_toValuationSubring` law (198).
- **`Pic0/Torsion.lean`** is new because `Pic0`, `Pic0.torsion` and `Pic0.mk` live in
  `Defs/Divisor.lean`, a hub with 15 importers; three rows about torsion's finiteness and its
  divisor representatives are a subject of their own, and a module above `Defs/Divisor` is
  cascade-free. It imports `Defs/Divisor` and imports nothing else it does not need — in
  particular it does **not** need `Place/OrderArithmetic` (the moving lemma stays with its premise).
- **`Defs/WeilDatum.lean`** carries the pin's `Definitions/Def_AlgebraicCurve_WeilDatum.lean`
  (structure `WeilDatum` + `pairing` / `symm` / `addLeft`, 81 pin lines, 4 declarations) and the one
  node, whose proof is `rfl` after `inv_div`. It imports `Defs/PlaceEvaluation.lean` for
  `Divisor.evalFun`. Its wire is the pin `Def_` file plus the node's wrapper and `S_` file.

**Import, do not copy** — the substitution blocks that live in the port:

| block | declarations |
|---|---|
| `Defs/Correspondence.lean` | `pullbackAlong_single` (24), `pushforwardAlong_single` (20), `isPrincipal_pushforwardAlong` (19), `correspondence_mem_principal` (18), `SeparableAlong` / `finrankAlong` (16 each), `correspondence_mk` (15), `mul` (11), `correspondence_apply` (9) |
| `Defs/SemilinearAut.lean` | `ord_smul` (22, 21), `SemilinearAut` (15), `smulResidueRingEquiv_algebraMap` (14), `deg_smul` (13, 11), `instModuleZModTorsion` (13), `instDistribMulActionTorsion` (12), `smulValuationSubringEquiv` (12), `ofAlgAut_smul` (11) |
| `Defs/Place.lean` | `not_isField_of_ne_top` (28), `exists_unit_mul_zpow` (16), `ofHeightOneSpectrum` (12), `ord_algebraMap_aux` (12) |
| `Defs/Divisor.lean` | `principal` (12) |
| `WeierstrassCurve/Velu/MapEquation.lean` | `smulRingEquiv` (14), `smulResidueAlgEquiv` (13) — a `def` of another namespace; if the proof only needs the `SemilinearAut` form, use that |

`SemilinearAut.pic0_correspondence_swap_smul`'s pin prelude carries its own `private ord_smul` (7
lines). It is a copy of the public `Place.ord_smul` / `SemilinearAut.ord_smul` — import, do not copy.
`Pic0.exists_ord_eq_mul…`'s six helpers are two-in-port (`ord_algebraMap_aux`,
`mk_eq_zero_iff_aux`) and four new; write the four, `private`, at the pin's names.

## Rules

- New modules: header `/- … -/` with prose and `spec-pin:` lines for the wrapper and the `S_` file
  (and, for `WeilDatum`, the pin `Def_` file), no cross-references to port modules or notes;
  `set_option autoImplicit false`, `noncomputable section`.
- Insertions: append and add the wrapper **and** `S_` file to the module's existing `spec-pin:`
  block; keep every existing declaration untouched. `Defs/Correspondence.lean`'s block is the one
  the manager has just created — extend it, do not rewrite it.
- Universe and binder spelling from the wrapper, character for character.
- Imports stay specific: **never `import Mathlib`** in a library module. Replace the pin's
  `import Mathlib` (and any broad import a `S_` file carries) with the specific mathlib modules the
  file needs — playbook §4's hygiene rule.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished modules `flock .lake/flt_build.lock timeout
  110 lake build <module>`. Every command under 2 minutes, its own `timeout`, no loops; logs under
  `lean/tmp/pic1-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module, every added
  declaration `ok`; `#print axioms` on all eight headlines → `[propext, Classical.choice,
  Quot.sound]`; 0 warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; no commit;
  no `spec/decl_markers.tsv` row.
- If a proof needs a `private` port helper or a declaration below its home, **stop and report** —
  do not promote, do not restate, do not edit a hub.

## Report (one message)

per file: build + warnings, the checker summary line, declarations added; the eight axioms lines;
the declaration names that stayed `private` in `Pic0/Torsion.lean` and why; any blocker.
