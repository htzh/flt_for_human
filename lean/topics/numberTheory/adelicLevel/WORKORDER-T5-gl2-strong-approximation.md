# WORKORDER-T5 — GL₂ strong approximation over ℚ (tier-3 engine, five modules, one headline)

**Status: landed 2026-10-18** — results in §8. Read
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3 (the workflow), §4
(definitions whole node; `private` is a build tool; a hub edit is a wave) and
[porting-playbook.md](../../../porting-playbook.md) §3–§5 before starting.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

**One node, one story: every finite idèle class has a rational representative up to the
integral level.** 898 pin lines, **46 declarations, 0 substitutions, 874 net new lines** —
this is a full-length transcription, not a reassembly. The development is unique to this pin
file (no sibling `S_` file re-proves any of the 45 engine names), so the cut is a linear
five-module engine plus one listed façade.

## 1. Scope

Six new files, nothing else:

| # | module | pin lines | decls |
|---|---|---:|---:|
| 1 | `FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/Elementary.lean` | 21–128 | 14 |
| 2 | `FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/Membership.lean` | 130–300 | 15 |
| 3 | `FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/Conjugation.lean` | 302–494 | 8 |
| 4 | `FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/Gauss.lean` | 658–719 | 3 |
| 5 | `FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/Approximation.lean` | 721–874 | 5 |
| 6 | `FLTForHuman/NumberTheory/AdelicLevel/StrongApproxRat.lean` — **listed façade** | — | 1 |

Modules 1–5 are tier 3 (unlisted): every declaration public, at the pin names, namespace
`NumberField.AdelicLevel.GL2StrongApproxW8M` (the pin's, kept verbatim — the `W8M` is a p2m
chunk marker; the port keeps such names when nothing else reads them), each with a
`-- pin: <name> (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:<line>)`
marker. Write them **in the order 1→5**, building each before starting the next; 6 last.

**Explicitly not this order.**

* Any other `NumberField.AdelicLevel` row (the `IdealBall`/`Level`/`PrincipalLevel`/`HeckeGen`
  modules are the landed definition layer; do not touch them).
* The pin `Definitions/` modules the silo imports — `Def_NumberField_AdelicLevel`,
  `Def_NumberField_AdelicBox`, `Def_AutomorphicForm_ConstantTerm` are already homed in the port
  and `Def_AutomorphicForm_AdelicLsXi` is **not used** by any of the 46 declarations (§4).
* The pin's `p2m_*` scaffolding (`p2m_open`, `p2m_export`, `p2m_reactivate`, `P2M.Util`).
* **Any edit to an existing module.** No promotion, no hub edit, no wave — see §6.

## 2. The headline

Statement authority is the pin wrapper
`Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean`
(10 lines). State it **verbatim** (the checker diffs it, and the façade is the only new checker
surface):

```lean
theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers ℚ) ℚ
```

Its pin proof is the `S_` file's `solution`, lines 884–898:

```lean
  haveI : IsPrincipalIdealRing (NumberField.RingOfIntegers ℚ) :=
    NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq
  obtain ⟨γ, hγ⟩ :=
    NumberField.AdelicLevel.GL2StrongApproxW8M.exists_map_mul_mem_finiteIntegralGL2
      (NumberField.RingOfIntegers ℚ) ℚ g
  refine ⟨γ, ?_⟩
  rw [NumberField.AdelicLevel.GL2StrongApproxW8M.glFin_globalPoints]
  exact hγ
```

The wrapper carries `attribute [-simp] AutomorphicForm.unipotentGL2_zero
AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero
AutomorphicForm.unipotentGL2_coe`; the port does **not** reproduce it (the port's
`unipotentGL2_coe` is a plain `@[simp]`, and no listed statement is affected — say so in the
façade docstring).

## 3. The five engine modules, declaration by declaration

Pin line numbers refer to
`P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean`
(read it read-only at `/home/haitao/proj/fermats-last-theorem/P2M/Sol/`; raw URL
`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean`).

**Module 1 — `Elementary` (21–128).** `section ElementaryMatrices`,
`variable {S : Type*} [CommRing S]`; imports the port's
`FLTForHuman.AutomorphicForm.Adelic.ConstantTerm` (for `unipotentGL2`, `unipotentGL2_coe`,
`unipotentGL2_add`) plus `Mathlib.LinearAlgebra.Matrix.Notation`.

| pin | declaration |
|---:|---|
| 25 | `lowerUnipGL2` (`def`, `GL (Fin 2) S` via `val`/`inv`/`val_inv`/`inv_val`) |
| 37 | `lowerUnipGL2_coe` (`@[scoped simp]`) |
| 40 | `lowerUnipGL2_inv` |
| 43 | `unipotentGL2_inv` |
| 46 | `lowerUnipGL2_add` |
| 52 | `map_lowerUnipGL2` |
| 58 | `map_unipotentGL2` |
| 64 | `diagTorusGL2` (`def`) |
| 76 | `diagTorusGL2_coe` (`@[scoped simp]`) |
| 79 | `diagTorusGL2_mul` |
| 85 | `map_diagTorusGL2` |
| 91 | `conj_unipotent_entry` |
| 100 | `conj_lowerUnip_entry` |
| 109 | `gauss_factorization` (the four-matrix Gauss identity) |

**Module 2 — `Membership` (130–300).** Re-opens
`variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]`;
imports module 1, `…/AdelicLevel/Level.lean`, `…/AdelicLevel/IdealBall.lean`,
`…/AdelicBox.lean`.

| pin | declaration |
|---:|---|
| 133 | `algebraMap_finiteAdeleRing_apply` |
| 136 | `valued_algebraMap_finiteAdeleRing_apply` |
| 141 | `one_apply_mem` |
| 145 | `zero_apply_mem` |
| 149 | `one_matrix_apply_mem` |
| 158 | `unipotentGL2_mem` |
| 178 | `lowerUnipGL2_mem` |
| 198 | `diagTorusGL2_mem` |
| 218 | `exists_sub_algebraMap_eq_mul_integral` (uses `AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles`) |
| 249 | `exists_common_denominator` (uses `IsLocalization.exist_integer_multiples`) |
| 274 | `ratGL` (`abbrev`) |
| 277 | `ratGL_mul` |
| 280 | `ratGL_inv_mul_val` |
| 287 | `ratGL_val_apply` |
| 293 | `ratGL_inv_val_apply` |

**Module 3 — `Conjugation` (302–494).** Imports module 2.

| pin | declaration |
|---:|---|
| 302 | `conj_entry_mem` (56 lines) |
| 357 | `exists_conj_unipotent_mem` |
| 399 | `exists_conj_lowerUnip_mem` |
| 441 | `absorb_unipotent_left` |
| 461 | `absorb_lowerUnip_left` |
| 481 | `mul_lowerUnip_apply_one_zero` |
| 490 | `det_apply` |
| 494 | `exists_lowerUnip_translate_isUnit` (164 lines — the valuation choice of `t`) |

**Module 4 — `Gauss` (658–719).** Imports module 3.

| pin | declaration |
|---:|---|
| 658 | `detUnit` (`def`, the determinant as a unit) |
| 667 | `detUnit_coe` (`@[scoped simp]`) |
| 672 | `exists_gauss_decomposition` |

**Module 5 — `Approximation` (721–874).** Imports modules 3 and 4, plus
`…/AdelicLevel/Projections.lean` (`glFin`) and `…/AutomorphicForm/Adelic/Basic.lean`
(`globalPoints`).

| pin | declaration |
|---:|---|
| 723 | `exists_primeGenerator` (`[IsPrincipalIdealRing R]`, `omit [IsFractionRing R K] in`) |
| 742 | `finiteIdele_exists_global_profile` (`[IsPrincipalIdealRing R]`) |
| 802 | `exists_ratGL_inv_mul_mem_of_finiteIdele` |
| 859 | `exists_map_mul_mem_finiteIntegralGL2` (`[IsPrincipalIdealRing R]`) |
| 870 | `glFin_globalPoints` |

**The mathematics**, for the module docstrings: an idèle class in the finite idèles is
approximated by a rational point modulo the integral level subgroup. `exists_gauss_decomposition`
is the Gauss (LU) decomposition of a 2×2 matrix over the finite adèles: after translating one
entry by a well-chosen integral adèle `t` (so that a row entry becomes a unit), the matrix
factors as `unipotent * lowerUnip * unipotent * diagonal` with the determinant as the diagonal
unit. `finiteIdele_exists_global_profile` is the global idèle profile: in a PID, for a finite
idèle `δ` there is `α ∈ Kˣ` making both `α⁻¹δ` and `αδ⁻¹` integral everywhere — the principal
idèles are cofinal in the idèle class group at the finite level. `exists_ratGL_inv_mul_mem_of_finiteIdele`
assembles the two, and the three `absorb_*` steps move the unipotent factors of the Gauss
decomposition into the rational point by adjusting the adèlic parameters (`a - algebraMap q`
conjugation lemmas).

## 4. What is already in the port — and the name paths that differ

`port_advise` reports **0 substitutions**: every one of the 46 declarations is new. The
*prerequisites* are all present, and this is the §4(a) hand-check of the import-only layer:

| pin name used | port home |
|---|---|
| `NumberField.AdelicLevel.finiteIntegralGL2`, `mem_finiteIntegralGL2_iff` | `NumberTheory/AdelicLevel/Level.lean:170,173` |
| `NumberField.AdelicLevel.glFin` | `NumberTheory/AdelicLevel/Projections.lean:94` |
| `NumberField.AdelicLevel.{coe_zero_apply, coe_one_apply, coe_add_apply, coe_mul_apply, coe_sub_apply, coe_neg_apply}` | `NumberTheory/AdelicLevel/IdealBall.lean` (`section Coe`) |
| `AutomorphicForm.unipotentGL2`, `unipotentGL2_coe`, `unipotentGL2_add`, `unipotentGL2_zero` | `AutomorphicForm/Adelic/ConstantTerm.lean:36,42,48,45` |
| `AutomorphicForm.globalPoints` | `AutomorphicForm/Adelic/Basic.lean:31` |
| `NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles` | `NumberTheory/AdelicBox.lean:225` |
| `FiniteAdeleRing.isUnit_iff` | **mathlib** `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean:170` |
| `HeightOneSpectrum.{mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation', intValuation_singleton, intValuation_eq_one_iff, valuation_of_algebraMap, valuation_le_one, intValuation_le_one}` | mathlib `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` |
| `WithZero.{exp, log, exp_log, exp_eq_one, exp_zsmul}` | mathlib `Mathlib/Algebra/GroupWithZero/WithZero.lean` |
| `Valuation.{map_add_of_distinct_val, zero_ne_one, ne_zero_iff}`, `Valuation.zero_iff`, `Matrix.det_fin_two_of`, `IsLocalization.exist_integer_multiples`, `NumberField.classNumber_eq_one_iff`, `Rat.classNumber_eq` | mathlib |

**Two name paths differ from the pin — adapt the proof term, never the statement.**

1. **`algebraMap_mem_adicCompletionIntegers`.** The pin calls
   `NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers R K v n` (pin:331). The port has
   this lemma **only** at `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers`
   (`NumberTheory/AdelicLevel/IdealBall.lean:87`, inside `section Local` with
   `variable {R K} (v : HeightOneSpectrum R)`), so its explicit arguments are `(v : …) (r : R)`
   with `R K` implicit. Write
   `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers (R := R) (K := K) v n`
   (or `open NumberField.AdelicLevel` and call it bare). Do **not** edit `AdelicBox.lean` to add
   an alias — that is a hub edit (§6).
2. `NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles R K a'` matches the port
   exactly (`R K` explicit) — no change.

Everything else in the 45 engine declarations is namespace-identical to the pin
(`NumberField.AdelicLevel.GL2StrongApproxW8M`), so `-- pin:` markers resolve by name.

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the
> low cap is what finds it. Diagnose it (`set_option diagnostics true`,
> `trace.Meta.synthInstance true` on that one declaration, in a scratch copy under `tmp/`), fix
> the inference, re-run. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. When a file is done,
> `flock .lake/flt_build.lock timeout 300 lake build <module>` (writes the `.olean`, builds
> dependencies, never dependents). Every `lake build` serialized and bounded. **Never a bare
> whole-tree `lake build`.**

**Hub prohibition.** Do not edit `AdelicLevel/{Level,IdealBall,Projections,PrincipalLevel}.lean`,
`AdelicBox.lean`, `AutomorphicForm/Adelic/{Basic,ConstantTerm}.lean`, `AdelicHaar/*`, or any
other existing module — not even to add a `simp` lemma, an alias or a promotion. If you believe
a promotion is genuinely required, **stop and report** with the declaration, the host and the
price from `python3 tools/deps/build_ladder.py --edit <host>`. On this measurement none is
needed: the 45 declarations are new names, and the two name paths of §4 are call-site edits.

**Drift surface, in the order the pin hits it.**

1. `Elementary`: `Matrix.mul_apply`, `Fin.sum_univ_two`, `Matrix.cons_val'`,
   `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.empty_val'`, `Matrix.cons_val_fin_one`,
   `GeneralLinearGroup.map`, `RingHom.mapMatrix_apply`, `Matrix.map_apply`, and
   `linear_combination … hci …` in `gauss_factorization` (needs `ring`-level normalization; if
   `linear_combination` leaves a goal, `ring_nf` first, and report it).
2. `Membership`: `IsFractionRing.injective`, `Ne.isUnit`, `Units.isUnit`, `coe_mul_apply`,
   `algebraMap K (FiniteAdeleRing R K) d * a' = a` rewriting through `hdu.unit_spec`.
3. `Conjugation`: the long `exists_lowerUnip_translate_isUnit` (164 lines) is a valuation
   argument on `Valued.v` with values in `WithZero (Multiplicative ℤ)`:
   `Valuation.map_add_of_distinct_val`, `Valuation.zero_iff`, `mem_adicCompletionIntegers`,
   `Filter.eventually_cofinite`, `Filter.Eventually.of_forall`, `Subtype.ext (funext …)`.
   Keep the pin's `filter_upwards […] with v …` and `split` structure; the `rename_i` names must
   be kept or replaced consistently.
4. `Gauss`: `Matrix.det_mul`, `det_fin_two_of`, `Units.val_mul`, `mul_inv_rev`, `group`.
5. `Approximation`: `Submodule.IsPrincipal.generator`, `Ideal.span_singleton_generator`,
   `intValuation_singleton`, `intValuation_eq_one_iff`, `HeightOneSpectrum.ext`,
   `Units.mk0`, `zpow_ne_zero`, `Finset.prod_eq_single`, `valuation_of_algebraMap`,
   `WithZero.exp_zsmul`, `_root_.one_zpow`.

## 6. Verification

| check | expected |
|---|---|
| tier-0 edit loop, all six modules | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.NumberTheory.AdelicLevel.StrongApproxRat` | green (builds all five engine modules) |
| checker before | 10343 identical / 0 mismatched / 0 missing / 42 own / 294 registered (10679) |
| checker after | **10344** identical — delta **+1**, exactly the headline |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` |
| `python3 tools/deps/unwired_register.py --check` | current after the five modules' 45 `-- pin:` markers and a `--rebuild` |
| `git status` | only the six new modules (the manager wires the checker and the register) |

## 7. Report shape

1. The six module paths, final line counts, and the declaration names as landed (per module).
2. Each module's exact import block, and why each import is there.
3. Every proof adaptation (pin line → port spelling) with pin line numbers, and the two §4 name
   paths if you had to change the call site.
4. Tier-0 results per module and the tier-1 result, with wall times.
5. The 45 `-- pin:` markers' line numbers, for the register check.
6. Anything left undone, and any promotion you judged necessary (you should have stopped and
   asked instead).

## 8. Results as landed (2026-10-18)

| | |
|---|---|
| engine | `StrongApprox/{Elementary,Membership,Conjugation,Gauss,Approximation}.lean` — 164 / 234 / 416 / 109 / 213 lines, 14 / 15 / 8 / 3 / 5 = 45 declarations, tier 3 |
| façade | `NumberTheory/AdelicLevel/StrongApproxRat.lean` — 49 lines, 1 headline |
| checker | 10,343 → **10,344 identical**, 0 mismatched / 0 missing, 42 own, 294 registered-unwired (10,680 checked) |
| axioms | headline + `exists_map_mul_mem_finiteIntegralGL2` + `exists_gauss_decomposition` + `finiteIdele_exists_global_profile`: `[propext, Classical.choice, Quot.sound]` |
| tier-0 | all six modules exit 0, 0 warnings (4.2–7.1 s each) |
| tier-1 | `… lake build FLTForHuman.NumberTheory.AdelicLevel.StrongApproxRat` green, 3790 jobs |
| register | 134 modules / 4100 public / 3796 with a pin counterpart (was 129 / 4055 / 3751) |
| existing modules edited | none |

Four corrections to this order, all from the landing:

1. **§4's call-site rename is the only name change.** Confirmed by `#check`: the pin's
   `NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers` is an unknown constant in the
   port; the proof calls `algebraMap_mem_adicCompletionIntegers v n` bare (resolving to the
   `NumberField.AdelicLevel` copy, `(v) (r)` explicit, `R K` implicit).
2. **Two imports the order did not list**, both measured necessary: `Mathlib.Tactic` in
   `Elementary.lean` (the entrywise `fin_cases`/`ring`/`linear_combination` proofs;
   `ConstantTerm` does not bring the tactic set in) and
   `Mathlib.NumberTheory.NumberField.ClassNumber` in the façade.
3. **One suppression, and one suppression avoided.** `linter.style.haveILetI` fires on the pin's
   `haveI` in `exists_primeGenerator` (the `have`/`letI` rewrite the linter proposes is not
   available: the instance feeds `Ideal.span_singleton_generator`), so that declaration carries
   `set_option linter.style.haveILetI false in` — declaration-scoped. On the façade the same
   lint had a clean alternative and got it: the `IsPrincipalIdealRing (𝓞 ℚ)` instance stands at
   file scope as a `local instance`, the proof has no `haveI`, and no `set_option` is used. The
   pin's in-proof `haveI` is a proof shape, not a statement.
4. **`local instance` does not leak**: importing the façade, `inferInstance` for
   `IsPrincipalIdealRing (𝓞 ℚ)` fails as it should, so no importer is polluted.

The full record is [logs/gl2-strong-approximation.md](../../../logs/gl2-strong-approximation.md).
