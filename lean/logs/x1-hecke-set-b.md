# SET-X1-B — the X₁ function-field transcendence (`JOneES`)

Work order: SET-X1-B of
[TOPIC-x1-hecke-diamond-inputs.md](../topics/hecke/TOPIC-x1-hecke-diamond-inputs.md) §5.
Pin: `aa2d8b3` (mathlib `v4.34.0`). Analytic core; no Hecke/diamond nodes.

**Result.** 3 new modules (1,551 lines), 2 checker wirings, 1 consumer zone.
Checker `4424 → 4431 identical (150 promoted), 0 mismatched, 0 missing, 30 own`
(delta **+7**, reconciled below). Consumer
`spec/ModularCurveHeckeConsumer.lean` Zone X1-FF error+warning count `0`.
Whole-tree `lake build` green (4957 jobs). Axioms on both headlines and on
`ModularCurve.isIntegralQExp_iff`: `[propext, Classical.choice, Quot.sound]`.

## 1. Scout gate, and the pre/post estimate

`tmp/Scratch.lean` imported `X1/Defs`, `X1/Integral`, `JqAnalyticModel`, mathlib
`NormTrace`/`Cusps`/`Lagrange`/`Homogenize`/`PrimitiveElement`/`LaurentSeries`
and `#check`ed the names the work order listed. Result: **every name exists at
the pin's shape** modulo three mechanical drifts (all found in the scout and
recorded in §5):

| probed name | scout result |
|---|---|
| `ModularForm.norm`, `ModularForm.coe_norm`, `norm_ne_zero`, `norm_eq_zero_iff` | present; `[𝒢.IsFiniteRelIndex ℋ]` instance synthesises from `[Γ.FiniteIndex]` |
| `SlashInvariantForm.quotientFunc`, `quotientFunc_mk`, `ModularForm.prod_slash` | present |
| `cuspFunction`, `cuspFunction_mul`, `cuspFunction_add`, `analyticAt_cuspFunction_zero` | present |
| `ModularForm.qExpansion_pow`, `qExpansion_mcast` | **protected**; the pin's unqualified `qExpansion_pow` is `ModularForm.qExpansion_pow` (the hypothesis-form `qExpansion_add/mul/sub/smul` are unqualified) |
| `Cos` quotient/Fintype | `Finite (↥𝒮ℒ ⧸ …)` is an instance; `Fintype` needs the pin's `Fintype.ofFinite _` (as a `noncomputable instance`) |
| `E_qExpansion_coeff`, `E_qExpansion_coeff_zero` | present, exact pin shape |
| `IsIntegralQExp.coeff/iff/unique/one/zero` | absent before this set; landed in `X1/Integral.lean` |
| `Lagrange.*`, `coeff_prod_of_natDegree_le`, `homogenize_finsetProd` | present; `eval_homogenize_eq_sum`/`nice_*` are the pin's own helpers |
| `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`, `HahnSeries.ofPowerSeries_C/_injective`, `C_eq_algebraMap`, `C_mul_eq_smul`, `coeffEmb_coeff` | present |
| `IntermediateField.liftAlgEquiv`/`lift_adjoin_simple`/`extendScalars`/`extendScalars_adjoin`/`finiteDimensional_adjoin`, `Module.Finite.of_equiv_equiv`, `coeffEmb_mem_laurentBaseChange`, `algebraMap_laurentSeries_eq_single`, `charZero_of_injective_algebraMap` | present |

**Estimate.** Pre-scout: `846` content (pin `S_…qExpFunctionFieldC.lean`) plus
`261` (base change). Post-scout: **no structural drift** — the general-`Γ`
norm/`Cos` route elaborates and the monomial-span argument needed no replacement
mathlib lemma. Corrected estimate **≈850 content** for node 1 (the only
reduction is the dedup of the pin's `P4` into `eisenstein4`) and **≈286** for
node 2. Measured (same `import/namespace/open/…` filter as the plan, so module
doc bodies count): mine `915` / pin `846`, and mine `286` / pin `261`; the
difference is the added module/decaration doc comments.

## 2. Per-module line counts

| module | lines | pin source |
|---|---:|---|
| `FLTForHuman/ModularCurve/X1/Integral.lean` | 53 | `Definitions/Def_ModularCurve_X1.lean:37–63` (`Integral` block) |
| `FLTForHuman/ModularCurve/X1/FunctionField.lean` | 1,141 | `P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean` (1,050) |
| `FLTForHuman/ModularCurve/X1/FunctionFieldBaseChange.lean` | 357 | `P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean` (316) |
| **new total** | **1,551** | |

Edits:

| file | +/− | content |
|---|---|---|
| `spec/check_flt_statements.py` | +12/−0 | two `SOURCES` and three `PORT_FILES` entries appended last |
| `spec/ModularCurveHeckeConsumer.lean` | +65/−0 | one import + Zone X1-FF (`[x1-ff]`) |

## 3. Checker

```
before: 4424 statements identical (150 promoted …), 0 mismatched, 0 missing, 30 own
after:  4431 statements identical (150 promoted …), 0 mismatched, 0 missing, 30 own
delta:  +7 identical
```

The `+7` reconciles exactly:

| block | n |
|---|---:|
| `X1/Integral.lean` (`IsIntegralQExp.coeff`, `isIntegralQExp_iff`, `IsIntegralQExp.unique`, `isIntegralQExp_one`, `isIntegralQExp_zero`) | 5 |
| `X1/FunctionField.lean` (headline) | 1 |
| `X1/FunctionFieldBaseChange.lean` (headline) | 1 |
| **total** | **7** |

One-token mutation check: `(n : ℕ) → (n : ℤ)` in `X1/Integral.lean:IsIntegralQExp.coeff`
gave `4430 identical / 1 mismatched / 0 missing` (the `MISMATCH` diff printed the
`ℤ`/`ℕ` binder difference), then reverted → `4431 / 0 / 0`.

`SOURCES` appended last:
`Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean`,
`Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean`.
`PORT_FILES` appended the three new modules. No `OWN_PROOFS` entries: every
public declaration resolves by name and every helper is `private`.

## 4. Consumer

`spec/ModularCurveHeckeConsumer.lean`, Zone X1-FF (`[x1-ff]`), appended before `end`:

- `private theorem gammaOneTwo_T_mem : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 2`
  by the pinned `Gamma1_mem` membership test (`decide` on the three `ZMod 2` entries);
- node 1 at `Γ = Γ₁(2)` (`[Γ.FiniteIndex]` from the ported `CongruenceSubgroup`
  instance, no local instance needed): the headline's exact existential;
- node 2 at `L = AlgebraicClosure ℚ` and the same `Γ₁(2)`: the base-changed
  headline's exact existential;
- the executed composition: destruct node 1 to a concrete `x` with
  `Transcendental ℚ x` and `FiniteDimensional ℚ⟮x⟯ _`, destruct node 2 to a
  concrete `y` at `L = ℚ̄`, and consume **all four** facts in the returned
  nested existential.

No `#check`, no `sorry`, no unported hypothesis.

```
cd lean && timeout 90 lake env lean spec/ModularCurveHeckeConsumer.lean 2>&1 | grep -c 'error\|warning'
0
```
(ran in 21.2s; the shell `grep -c` reports `[exit code: 1]` when the count is 0 —
the printed count is the metric).

## 5. Build times (wall / user / sys)

| step | command | time |
|---|---|---|
| `X1/Integral` | `timeout 90 lake env lean` | 4.5s |
| `X1/Integral` | `flock … timeout 200 lake build` | 4.4s / 4.1s / 3.9s (module 3.9s) |
| `X1/FunctionField` (pre-fix, 9 errors) | `timeout 500 lake env lean` | 4m27.8s / 4m36.6s / 3.1s |
| `X1/FunctionField` (post-fix) | `timeout 500 lake env lean` | 34.2s / 20.2s / 8.6s |
| `X1/FunctionField` | `flock … timeout 300 lake build` | 16.1s / 22.1s / 8.2s (module 13s) |
| `X1/FunctionFieldBaseChange` | `timeout 300 lake env lean` | 13.2s / 16.7s / 2.7s |
| `X1/FunctionFieldBaseChange` + `X1/Integral` | `flock … timeout 300 lake build` | 15.7s / 20.8s / 6.1s (module 14s) |
| consumer | `timeout 200 lake env lean spec/…` | 21.2s / 21.6s / 2.6s |
| whole tree | `flock … timeout 300 lake build` | 4.0s / 2.6s / 3.4s — green (4957 jobs) |

The pre-fix 4m27.8s with only 9 errors is the failed-`private`-constant
elaboration blow-up of §6 item 3; once fixed, the module is 34s.

## 6. Per-declaration table

`P` = public, `p` = private. Pin line numbers are from the file named in the
section header.

### `ModularCurve/X1/Integral.lean` — pin `Definitions/Def_ModularCurve_X1.lean`

| declaration | vis | pin |
|---|---|---|
| `IsIntegralQExp.coeff` | P | 40 |
| `isIntegralQExp_iff` | P | 46 |
| `IsIntegralQExp.unique` | P | 52 |
| `isIntegralQExp_one` | P | 58 |
| `isIntegralQExp_zero` | P | 61 |

### `ModularCurve/X1/FunctionField.lean` — pin `P2M/Sol/S_…qExpFunctionFieldC.lean`

Public surface: **one** headline, `ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC`
(the pin's `solution`, S_ line 1043; wrapper
`Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean:9`).

All helpers are `private`:

| declaration | vis | pin |
|---|---|---|
| `JOneESAlg.valuation_algebraMap_le_one` | p | 16 |
| `JOneESAlg.valuation_le_one_of_isAlgebraic` | p | 23 |
| `JOneESAlg.eq_C_of_isAlgebraic` | p | 42 |
| `JOneESAlg.transcendental_of_coeff_ne_zero` | p | 75 |
| `JOneESAlg.linearIndependent_map` | p | 88 |
| `JOneESAlg.finiteDimensional_of_forall_aeval_eq_zero` | p | 145 |
| `JOneESLevelOne.q4` / `q6` | p | 177 / 178 |
| `JOneESLevelOne.monomialSpan` | p | 180 |
| `JOneESLevelOne.monomial_mem` | p | 183 |
| `JOneESLevelOne.q4_coeff_zero` / `q6_coeff_zero` | p | 187 / 190 |
| `JOneESLevelOne.qExpansion_discriminant` | p | 193 |
| `JOneESLevelOne.qExpansion_mem_monomialSpan` | p | 209 |
| `JOneESNorm.Cos` | p | 293 |
| `JOneESNorm` Fintype instance | p | 295 |
| `JOneESNorm.one_mem_strictPeriods` | p | 299 |
| `JOneESNorm.quotientFunc_smul_sub` | p | 309 |
| `JOneESNorm.norm_smul_sub_apply` | p | 320 |
| `JOneESNorm.charPolyAt` / `eval_charPolyAt` | p | 329 / 332 |
| `JOneESNorm.natDegree_linear_le` / `card_cos` / `natDegree_charPolyAt_le` / `coeff_charPolyAt_card` | p | 339 / 344 / 347 / 354 |
| `JOneESNorm.node` / `node_injOn` / `lag` / `charPolyAt_eq_sum` | p | 365 / 367 / 372 / 375 |
| `JOneESNorm.coeffForm` / `coe_finset_sum` / `coeffForm_apply` / `coe_coeffForm_card` | p | 389 / 393 / 397 / 402 |
| `JOneESNorm.eval_homogenize_linear` / `eval_homogenize_eq_sum` | p | 406 / 411 |
| `JOneESNorm.sum_coeffForm_mul_pow_eq_zero` | p | 421 |
| `JOneESNorm.Nice` + `Nice.mul/add/pow/sum` | p | 440–479 |
| `JOneESNorm.nice_one` / `nice_zero` | p | 452 / 457 |
| `JOneESNorm.qExpansion_pow'` / `qExpansion_sum'` | p | 466 / 481 |
| `JOneESNorm.nice_of_modularForm` / `nice_of_levelOne` | p | 495 / 499 |
| `JOneESNorm.sum_qExpansion_coeffForm_mul_pow_eq_zero` | p | 502 |
| `JOneESNorm.qExpansion_coeffForm_card_ne_zero` | p | 528 |
| `JOneESRat.P6` | p | 551 |
| `JOneESRat.isIntegralQExp_E4` | p | 555 (dedup: `eisenstein4`, ours) |
| `JOneESRat.isIntegralQExp_E6` | p | 566 |
| `JOneESRat.A12` / `B12` | p | 578 / 583 |
| `JOneESRat.isIntegralQExp_A12` / `_B12` | p | 587 / 592 |
| `JOneESRat.constantCoeff_P6` | p | 600 |
| `JOneESRat.coeff_one_eisenstein4` | p | 604 (pin's `coeff_one_P4`, dedup) |
| `JOneESRat.coeff_one_P6` | p | 608 |
| `JOneESRat.intSeriesC_ne_zero_of_constantCoeff` | p | 612 |
| `JOneESRat.xq` / `intSeriesC_P4_cube_ne_zero` / `xq_mem` / `xq_transcendental` | p | 622 / 624 / 628 / 635 |
| `JOneESRat.intSeriesC_add` / `intSeriesC_neg` | p | 655 / 660 |
| `JOneESRat.hper` | p | 669 |
| `JOneESRat.mul_mem_intFormRatiosC` / `add_mem_intFormRatiosC` / `neg_mem_intFormRatiosC` / `inv_mem_intFormRatiosC` | p | 674 / 688 / 703 / 713 |
| `JOneESRat.algebraMap_mem_intFormRatiosC` | p | 724 |
| `JOneESRat.mem_qExpFunctionFieldC_iff` | p | 756 |
| `JOneESRat.coeffEmb_intSeriesC` / `coeffEmb_eq_map` | p | 782 / 790 |
| `JOneESRat.sum_div_pow_eq` / `monomial_eq` | p | 796 / 812 |
| `JOneESRat.exists_rat_relation` | p | 818 |
| `JOneESRat.exists_transcendental_finiteDimensional` | p | 947 |

### `ModularCurve/X1/FunctionFieldBaseChange.lean` — pin `P2M/Sol/S_…laurentBaseChange.lean`

Public surface: **one** headline, `ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`
(the pin's `solution`, S_ line 305; wrapper
`Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean:9`).

| declaration | vis | pin |
|---|---|---|
| `JOneESAlgBC.valuation_algebraMap_le_one` | p | 17 (duplicate of node 1's, pin duplicates too) |
| `JOneESAlgBC.valuation_le_one_of_isAlgebraic` | p | 24 |
| `JOneESAlgBC.eq_C_of_isAlgebraic` | p | 43 |
| `JOneESAlgBC.transcendental_of_coeff_ne_zero` | p | 76 |
| `JOneESBC.eq_C_of_forall_coeff_eq_zero` | p | 95 |
| `JOneESBC.charZero_L` | p | 102 |
| `JOneESBC.transcendental_coeffEmb` | p | 105 |
| `JOneESBC.algebraMap_rat_eq_C` / `coeffEmb_C` | p | 123 / 125 |
| `JOneESBC.coeffEmb_mem_adjoin_of_mem_adjoin` | p | 133 |
| `JOneESBC.finiteDimensional_adjoin_of_extendScalars` | p | 149 |
| `JOneESBC.finite_adjoin_of_le` / `finite_extendScalars_of_adjoin` | p | 168 / 176 |
| `JOneESBC.finite_extendScalars` | p | 183 |
| `JOneESBC.exists_transcendental_finiteDimensional_laurentBaseChange` | p | 267 |

## 7. Friction log

Appended as hit, in order.

1. **`IsGLPos.smul_apply`/`coe_smul` and `ModularForm.coe_sub/add/neg/zero`,
   `if_neg` are deprecated in `v4.34.0`.** The pin uses the old names. Switched
   before the first clean build to `smul_apply` / `FunLike.coe_smul`,
   `FunLike.coe_sub/add/neg/zero`, and `ite_eq_right` (the documented
   replacement; identical signature `¬c → (if c then a else b) = b`).

2. **The node-1 `one_mem_strictPeriods` entry proof does not survive the port's
   `CoeFun` for `GL`.** The pin's
   `ext i j <;> fin_cases … <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]`
   leaves the four entry goals unsolved: the goal's `↑(mapGL ℝ T) i j` is the
   reducible `Matrix.GeneralLinearGroup.instCoeFun` application, and
   `Matrix.SpecialLinearGroup.mapGL_coe_matrix` (about the `Coe` to `Matrix`)
   does not fire on it. Fix (in place, statement unchanged): prove
   `upperRightHom 1 = mapGL ℝ ModularGroup.T` by `apply Units.ext` + two
   `change`s (`!![1,1;0,1]` on the left; `(algebraMap ℤ ℝ).mapMatrix …` on the
   right) + `ext i j; fin_cases …; norm_num [RingHom.mapMatrix_apply, Matrix.map_apply]`,
   then `rw [h]; exact Subgroup.mem_map_of_mem _ hT`.

3. **`A12 Γ`/`B12 Γ` mis-parsed, and the cascade.** `Γ` is an implicit section
   variable, so `A12 Γ` was read as coercing the `ModularForm` to `ℍ → ℂ` and
   applying it to `Γ` (`Application type mismatch … expected ℍ`), and `rw [A12]`
   then failed. The pin's `variable (Γ) in` before both defs is the fix. Until
   fixed, this cascaded into a spurious `(deterministic) timeout at whnf` in the
   neighbouring `xq_mem` and a kernel error
   `unknown constant '_private…JOneESRat.xq_mem'` (the proof's private constant
   was never registered); both vanished with the binder fix. Lesson for
   SET-X1-C: a `private` helper whose elaboration fails can surface as a *kernel*
   complaint on a later declaration, not at the failing line.

4. **`one_mem_strictPeriods` had a spurious `[Γ.FiniteIndex]` binder.** Without
   the pin's `omit [Γ.FiniteIndex] in`, the helper carried the instance argument,
   so `hper` (declared with `omit`) failed with `synthInstanceFailed Γ.FiniteIndex`.
   Added the `omit`.

5. **`eisenstein4` dedup and the local coefficient lemma.** Per the dispatch
   dedup rule, the pin's `P4` is `ModularCurve.eisenstein4` and its
   `isIntegralQExp_E4` is `qExpansion_E4_eq_map_eisenstein4.symm`; the pin's
   `constantCoeff_P4` is the already-public `constantCoeff_eisenstein4`. The
   pin's `coeff_one_P4 = 240` has a private ported copy
   (`JqCoefficients.lean:112 coeff_eisenstein4_one`), so a private
   `coeff_one_eisenstein4` is proved locally (2 lines, `PowerSeries.coeff_mk` +
   `norm_num`). `P6` has no ported integral series, so the pin's `P6` is defined
   and `isIntegralQExp_E6` proved from `EisensteinSeries.E_qExpansion_coeff`
   verbatim (including `bernoulli 6 = 1 / 42 by decide +kernel`, which works
   under `v4.34.0`).

6. **`JOneESAlgBC` re-states the node-1 `JOneESAlg` A1 block.** The pin duplicates
   these four `LaurentSeries` lemmas byte-for-byte in its second `S_` file, and
   because every helper is `private` in its own module they cannot be imported.
   Transcribed as the pin does; the near-duplicate (`valuation_algebraMap_le_one`,
   `valuation_le_one_of_isAlgebraic`, `eq_C_of_isAlgebraic`,
   `transcendental_of_coeff_ne_zero`, ~60 lines) is recorded here for a later
   refactor round that could expose them once (e.g. in `X1/Integral.lean`).

7. **`Gamma1Basis.lean:810` keeps a private `isIntegralQExp_iff`.** The port now
   publishes `ModularCurve.isIntegralQExp_iff` (and `.coeff`) in
   `X1/Integral.lean`, but `Gamma1Basis` is a large module that does not import
   the X₁ tree, and its private `isIntegralQExp_coeff` has the same body. Left
   untouched (as the work order permits); recorded for a later refactor round.

8. **The work order's `JOneESNorm` "generalise the `CosetQ`/`normCusp` block in
   its home" option was declined.** The port's private block
   (`Gamma1Vanishing.lean:519–560`) is specialised to `Γ₁(M) ≤ Γ₀(M)` with the
   `CuspForm` carrier; the pin's `JOneESNorm` needs the general-`Γ`
   `ModularForm`-carrier `Cos`/`quotientFunc`/norm and the `Nice` analyticity
   predicate, and the two do not line up cheaply (the port's block builds a
   `CuspForm Γ₀(M) (k * Nat.card 𝒬)` and never states the `charPolyAt` /
   `coeffForm` Lagrange block). The pin's block was transcribed instead; the
   generalisation is recorded as a near-duplicate, not as a reuse.

## 8. What SET-X1-C must know

- The two headlines are in place with the wrappers' exact binders, so
  `ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC`
  and `…_laurentBaseChange` can be imported directly. Both carry only
  `[propext, Classical.choice, Quot.sound]`.
- `X1/Integral.lean` now publishes `IsIntegralQExp.coeff`,
  `isIntegralQExp_iff`, `IsIntegralQExp.unique`, `isIntegralQExp_one`,
  `isIntegralQExp_zero` — the `P4`/`P6` `IsIntegralQExp` witnesses and
  `qExpand_image_intFormRatiosC_subset` should use these, not reinline them.
  Concretely, the pin's
  `S_ModularCurve_qExpand_image_intFormRatiosC_subset.lean:135` calls
  `ModularCurve.isIntegralQExp_iff`, which is exactly the public copy landed
  here; that module needs no `P4`/`P6`.
- `P4` does **not** exist as a name: the integral `E₄` series is
  `ModularCurve.eisenstein4` (`coeff 1 = 240`, `constantCoeff = 1`). `P6` is
  `private` in `X1/FunctionField.lean`; a public `P6`-shaped series is the
  (private) `Gamma0Rationality.P6`/`Gamma0Integral.P6`, so SET-X1-C must not
  expect an importable `P6`.
- The four `JOneESAlg`/`JOneESAlgBC` A1 lemmas remain `private` in their two
  modules; if a later set needs them outside, promote one copy rather than
  writing a third.
- No file of SET-X1-A or of `Transcendence.lean`/`Transport.lean`/
  `JqIntegralRatios.lean` was touched.

Public URLs use the pin:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean>.
