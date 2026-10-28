# WORKORDER RP2 — the residue field of a regular prolongation

Scope: **one insertion**, into `FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean`. Nothing
else may be edited. (Part of SET 5, [SET-5.md](SET-5.md) §1; no new module — the reviewer's call 1.)

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff` | `S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff` | 646 | 28 (1 `private`) | insert |
| `AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic` | `S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic` | 260 | 16 | insert |
| `AlgebraicCurve.RegularProlongation.transcendental_of_residue_transcendental` | `S_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental` | 110 | 1 | insert |
| `AlgebraicCurve.RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero` | `S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero` | 88 | 6 | insert |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements come from each node's
`Theorems/Thm_<stem>.lean` wrapper**, proofs from the `S_` file. All four are leaves: their pin files
import only `Definitions/Def_AlgebraicCurve_RegularProlongation.lean`, which the port has as
`RegularProlongation.lean`.

**The mathematics.** The residue side of a regular prolongation `R` of a valuation subring `A` of
`L` into `F` (residue field `Fbar`): an element of `R.integers` whose residue is transcendental over
the residue field makes its `L`-span integral; a monic bivariate relation between `x` and the
residue variable forces integrality of the residue adjoin; a minimum-order/residue bound for monic
polynomials; and the headline `eq_integers_of_forall_mem_adjoin_iff` — a valuation subring `V` of `F`
that agrees with `R.integers` on the `L`-adjoin of `x` **is** `R.integers`, given the two `finrank`
hypotheses. These are the steps by which a prolongation's integers are identified from their
behaviour on one transcendental element.

## Why this home (do not re-home it)

`RegularProlongationFinrank.lean` already declares the whole engine the four proofs consume, and it
is the module of the same subject (the residue map of a regular prolongation: its `finrank`
transport and its frame). Import, do not copy:

| already in `RegularProlongationFinrank.lean` | pin lines |
|---|---:|
| `mem_of_sum_smul_mem`, `valuation_lt_one_of_sum_smul_mem` | 39 / 18 |
| `linearIndependent_coe`, `linearIndependent_coe_frame`, `linearIndependent_adjoin`, `linearIndependent_adjoinField`, `linearIndependent_residue_pow`, `linearIndependent_residue_frame` | 21 / 10 / 37 / 8 / 9 / 26 |
| `exists_normalizer`, `exists_repr_adjoinField`, `exists_normalize_aeval` | 21 / 26 / 30 |
| `residue_sum_constHom_mul`, `aeval_eq_linearCombination`, `linearIndependent_pow_iff_transcendental` | 10 / 8 / 19 |
| `constHom` (80), `residue_constHom` (91), `residue_eq_zero_iff` (96) | the pin's `residue_eq_zero_iff` prelude copy is **already public here** |

From `RegularProlongation.lean` (already imported here): the `RegularProlongation` structure,
`toRegularProlongation`, `toRegularProlongation_residue`, `smul_const_ne_zero`.
`ord_nonneg_of_mem` / `mem_of_ord_nonneg` / `mem_iff_ord_nonneg` are public in
`Defs/WeilOfKaehler.lean`, `Defs/PushPull.lean`, `Differential/ConstantFieldExtension.lean` (binder
variants: take the `Theorems/` wrapper's) — do not restate them.

The pin repeats `constHom` and `residue_constHom` in three of the four files; they are written once,
here. That is the only "port once" item in this order.

## Rules

- Insertions only: append to `RegularProlongationFinrank.lean` (after its existing declarations,
  before nothing is moved) and add **two** `spec-pin:` lines per node — the `Theorems/` wrapper and
  the `S_` file — to that module's existing block. Keep every existing declaration untouched.
- Universe and binder spelling from the wrapper, character for character (section variables where
  the wrapper has them, inline binders where it writes them inline — the checker compares text).
  The 646-line node's 27 public declarations are pin-public and stay public; the one `private`
  helper (`residue_eq_zero_iff`) is already public here and is imported.
- Imports stay specific: **never `import Mathlib`** in a library module. Replace the pin's
  `import Mathlib` (and any broad import a `S_` file carries) with the specific mathlib modules the
  file needs — playbook §4's hygiene rule.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished module `flock .lake/flt_build.lock timeout
  110 lake build FLTForHuman.AlgebraicCurve.RegularProlongationFinrank`. Every command under 2
  minutes, its own `timeout`, no loops; logs under `lean/tmp/rp2-*.log`.
- `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean` →
  **0 mismatch, 0 missing**, every added declaration `ok`; `#print axioms` on the four headlines →
  `[propext, Classical.choice, Quot.sound]`; 0 warnings; no `sorry`/`admit`/`axiom`; no
  `set_option maxHeartbeats`; no commit; no `spec/decl_markers.tsv` row.
- If a proof needs a `private` port helper or a declaration below this module, **stop and report** —
  do not promote, do not restate, do not edit a hub.

## Report (one message)

the module's build + warnings and its checker summary line; the four axioms lines; the declaration
count added (public / `private`); any deviation beyond a tactic rename (one line each); any blocker.
