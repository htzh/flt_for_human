# SET-X1-A — the X₁ function-field/Jacobian vocabulary, the Hecke-operator and diamond definitions, and the two generic `Along` facts

Work order: SET-X1-A of
[TOPIC-x1-hecke-diamond-inputs.md](../topics/hecke/TOPIC-x1-hecke-diamond-inputs.md) §5.
Pin: `aa2d8b3` (mathlib `v4.34.0`). No headline theorem proofs; definitions-first.

**Result.** 4 new modules (523 lines), 3 edits, 2 promotions, 1 reconciliation.
Checker `4368 → 4424 identical (150 promoted), 0 mismatched, 0 missing, 30 own`.
Consumer `spec/ModularCurveHeckeConsumer.lean` error count `0`. Whole-tree
`lake build` green (4952 jobs).

## 1. Per-module line counts

| module | lines | role | pin source |
|---|---:|---|---|
| `FLTForHuman/ModularCurve/X1/Defs.lean` | 144 | X₁ function fields + Jacobian abbrevs | `Definitions/Def_ModularCurve_X1.lean:95–218` |
| `FLTForHuman/ModularCurve/X1/HeckeOperator.lean` | 209 | α/β degeneracy maps, the Hecke correspondence, `HeckeInputsOneAlong` | `Definitions/Def_ModularCurve_X1HeckeOperator.lean:59–228` |
| `FLTForHuman/ModularCurve/X1/Diamond.lean` | 127 | `IsBaseChangeAutOf`/`baseChangeAut`, `slashQExpC`, `IsDiamondAut`/`diamondAut`, `diamondAutBar` | `Definitions/Def_ModularCurve_X1Diamond.lean` |
| `FLTForHuman/ModularCurve/X1/HeckeModule.lean` | 43 | `HeckeDiamondInputsAll` only | `Definitions/Def_ModularCurve_X1HeckeModule.lean:58–65` |
| **new total** | **523** | | |

Edits (numstat):

| file | +/− | content |
|---|---|---|
| `AlgebraicCurve/PrincipalDivisors/Transcendence.lean` | +14/−0 | public `Divisor.pushforwardNormFormula` wrapper over the surviving private `_of_finiteDimensional` |
| `AlgebraicCurve/WeilExchange/Transport.lean` | +50/−0 | imports + `fundamentalIdentityAlong` + `normFormulaAlong` + the private `fiber` bridge |
| `ModularCurve/JqIntegralRatios.lean` | +16/−9 | `restrictForm`/`coe_restrictForm` promoted to public in a `section Restrict`; `restrictForm_apply` added |
| `ModularForms/WeightOne/IntegralWeightOneForm.lean` | +9/−13 | deleted its duplicate `private restrictForm`/`coe_restrictForm` (collision reconciliation, §6) |
| `spec/check_flt_statements.py` | +48/−1 | new `SOURCES`/`PORT_FILES` entries |
| `spec/ModularCurveHeckeConsumer.lean` | +72/−1 | one import + Zone X1-DEF |

## 2. Checker

```
before: 4368 statements identical (150 promoted …), 0 mismatched, 0 missing, 30 own
after:  4424 statements identical (150 promoted …), 0 mismatched, 0 missing, 30 own
delta:  +56 identical
```

The +56 reconciles exactly as

| block | n |
|---|---:|
| `X1/Defs.lean` | 14 |
| `X1/HeckeOperator.lean` | 23 |
| `X1/Diamond.lean` | 12 |
| `X1/HeckeModule.lean` | 1 |
| `JqIntegralRatios.lean` (`restrictForm`, `coe_restrictForm`, `restrictForm_apply`) | 3 |
| `Transcendence.lean` (`Divisor.pushforwardNormFormula`) | 1 |
| `Transport.lean` (`fundamentalIdentityAlong`, `normFormulaAlong`) | 2 |
| **total** | **56** |

One-token mutation check: `slashQExpC (k : ℤ) → (k : ℕ)` in `X1/Diamond.lean`
gave `4423 identical / 1 mismatched / 0 missing`; reverted → `4424 / 0 / 0`.

`SOURCES` appended last: `Definitions/Def_ModularCurve_X1HeckeOperator.lean`,
`Definitions/Def_ModularCurve_X1Diamond.lean`,
`Definitions/Def_ModularCurve_X1HeckeModule.lean`,
`Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula.lean`,
`Theorems/Thm_AlgebraicCurve_fundamentalIdentityAlong.lean`,
`Theorems/Thm_AlgebraicCurve_normFormulaAlong.lean`
(`Definitions/Def_ModularCurve_X1.lean` was already listed).
`PORT_FILES` appended the four X₁ modules.
No `OWN_PROOFS` entries were needed: every new public declaration resolves by
name, and all helpers are `private`.

## 3. Consumer

`spec/ModularCurveHeckeConsumer.lean`, Zone X1-DEF (`[x1]`), appended before `end`:

- X₁ layer field at `M = 2`: `x1FunctionFieldC_rat`, `x1x0FunctionFieldC_one`,
  `x1FunctionFieldC_le_x1x0`, `x1FunctionFieldC_le_of_dvd`;
- `x1FunctionFieldBar 2` inhabited (`example : x1FunctionFieldBar 2 := 1`,
  `Inhabited (x1FunctionFieldBar 2)`);
- `AddCommGroup (JOne 2)` and `AddCommGroup (JOneC 2 ℂ)` by `inferInstance`;
- the definitional bridges `coe_heckeAlphaOneBar 2 3 x`,
  `coe_heckeBetaOneBar 2 3 h x` at `M = 2`, `ℓ = 3`;
- `Divisor.pushforwardNormFormula`, `fundamentalIdentityAlong`,
  `normFormulaAlong` at the concrete bar field `modularFunctionFieldBar 1`
  (m11's unconditional `HasPrincipalDivisors`, `φ = AlgHom.id`), with the
  integrality discharged from `Algebra.IsIntegral.of_finite` and the instance
  supplied by a `private instance` local to the zone.

No `#check`, no `sorry`, no unported hypothesis in the zone's examples.

```
cd lean && timeout 90 lake env lean spec/ModularCurveHeckeConsumer.lean 2>&1 | grep -c error
0
```
(the shell `grep -c` reports `[exit code: 1]` when the count is 0; the printed
count is the metric.)

## 4. Build times (wall / user / sys)

| step | command | time |
|---|---|---|
| `JqIntegralRatios` (after promotion) | `flock … timeout 90 lake build` | 30.9s / 6.8s / 12.2s (module 26s) |
| `X1/Defs` | `timeout 60 lake env lean` | 7.8s |
| `X1/Defs` | `flock … timeout 90 lake build` | 11.2s / 6.2s / 7.1s |
| `X1/HeckeOperator` | `timeout 60 lake env lean` | 17.8s (deprecated-`dif` warnings) |
| `X1/Diamond` | `timeout 60 lake env lean` | 7.8s |
| three X₁ modules | `flock … timeout 90 lake build A B C` | 28.6s / 31.8s / 11.3s |
| `Transcendence` | `flock … timeout 90 lake build` | 11.5s / 13.8s / 4.6s (module 8.7s) |
| `Transport` | `timeout 60 lake env lean` | 6.1s |
| `Transport` + dependents (`HeckeCommuteBar`, `CuspDichotomy`, `Reduction`, `Integrality`, X₁) | `flock … timeout 300 lake build …` | 1m26.2s / 4m24.1s / 1m6.5s |
| `IntegralWeightOneForm` (collision fix) | `flock … timeout 120 lake build` | 5.4s |
| whole tree, attempt 1 | `flock … timeout 300 lake build` | 3m38.7s / 8m40.4s / 1m12.3s — **failed** on the `restrictForm` collision |
| whole tree, retry | `flock … timeout 300 lake build` | 3.3s / 2.5s / 3.2s — green (4952 jobs) |

## 5. Per-declaration table

`P` = public, `p` = private. Line numbers are the pin's.

### `ModularCurve/X1/Defs.lean`

| declaration | vis | pin |
|---|---|---|
| `one_mem_intFormRatiosC` | P | 95 |
| `intFormRatiosC_mono` | P | 116 |
| `qExpFunctionFieldC_mono` | P | 124 |
| `x1FunctionFieldC` | P | 134 |
| `x1FunctionField` (abbrev) | P | 137 |
| `x1FunctionFieldC_rat` | P | 140 |
| `x1x0FunctionFieldC` | P | 142 |
| `x1FunctionFieldC_le_x1x0` | P | 145 |
| `x1x0FunctionFieldC_one` | P | 148 |
| `Gamma1_le_of_dvd` | P | 158 |
| `x1FunctionFieldC_le_of_dvd` | P | 172 |
| `x1FunctionFieldBar` (abbrev) | P | 182 |
| `JOne` (abbrev) | P | 186 |
| `JOneC` (abbrev) | P | 209 |

### `ModularCurve/X1/HeckeOperator.lean`

| declaration | vis | pin |
|---|---|---|
| `heckeAlphaOneBar` | P | 66 |
| `coe_heckeAlphaOneBar` | P | 73 |
| `heckeAlphaOneBar_eq_inclusion` | P | 79 |
| `HeckeBetaOneDefined` | P | 84 |
| `heckeBetaOneBarRingHomOf` | P | 89 |
| `heckeBetaOneBarOf` | P | 100 |
| `coe_heckeBetaOneBarOf` | P | 109 |
| `heckeBetaOneBar` | P | 116 |
| `heckeBetaOneBar_eq` | P | 121 |
| `heckeBetaOneBar_of_not` | P | 125 |
| `coe_heckeBetaOneBar` | P | 129 |
| `HeckeAlphaOneBarIntegral` | P | 139 |
| `HeckeBetaOneBarIntegral` | P | 144 |
| `heckeDivOneBar` | P | 151 |
| `heckePic0OneBar` | P | 156 |
| `heckeDivOneBarTranspose` | P | 164 |
| `heckePic0OneBarTranspose` | P | 169 |
| `HeckeInputsOneAlong` | P | 183 |
| `heckeOperatorOneAlong` | P | 192 |
| `heckeInputsOneAlong_intro` | P | 203 |
| `HeckeInputsOneAlong.betaOneDefined` | P | 211 |
| `heckeOperatorOneAlong_eq` | P | 214 |
| `heckeOperatorOneAlong_of_not` | P | 224 |

### `ModularCurve/X1/Diamond.lean`

| declaration | vis | pin |
|---|---|---|
| `IsBaseChangeAutOf` | P | 17 |
| `baseChangeAut` | P | 24 |
| `isBaseChangeAutOf_baseChangeAut` | P | 33 |
| `baseChangeAut_of_not` | P | 39 |
| `slashQExpC` | P | 50 |
| `IsDiamondAut` | P | 53 |
| `IsDiamondAut.coprime` | P | 63 |
| `diamondAut` | P | 66 |
| `isDiamondAut_diamondAut` | P | 73 |
| `diamondAut_of_not` | P | 79 |
| `diamondAut_of_not_coprime` | P | 84 |
| `diamondAutBar` | P | 94 |

### `ModularCurve/X1/HeckeModule.lean`

| declaration | vis | pin |
|---|---|---|
| `HeckeDiamondInputsAll` | P | 58 |

### Edits

| declaration | module | vis | pin |
|---|---|---|---|
| `ModularCurve.restrictForm` | `ModularCurve/JqIntegralRatios.lean` | P (promoted from `private`) | `Def_ModularCurve_X1.lean:18` |
| `ModularCurve.coe_restrictForm` | `ModularCurve/JqIntegralRatios.lean` | P (promoted) | 25 |
| `ModularCurve.restrictForm_apply` | `ModularCurve/JqIntegralRatios.lean` | P (new) | 29 |
| `AlgebraicCurve.Divisor.pushforwardNormFormula` | `AlgebraicCurve/PrincipalDivisors/Transcendence.lean` | P (wrapper over `private pushforwardNormFormula_of_finiteDimensional`) | `Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula.lean:9` |
| `AlgebraicCurve.fundamentalIdentityAlong` | `AlgebraicCurve/WeilExchange/Transport.lean` | P | `Theorems/Thm_AlgebraicCurve_fundamentalIdentityAlong.lean:14` |
| `AlgebraicCurve.normFormulaAlong` | `AlgebraicCurve/WeilExchange/Transport.lean` | P | `Theorems/Thm_AlgebraicCurve_normFormulaAlong.lean:9` |
| `AlgebraicCurve.sum_ramificationIndex_mul_inertiaDeg_fiber` | `AlgebraicCurve/WeilExchange/Transport.lean` | p (bridge, §6) | none (our own) |

## 6. Friction log

Appended as hit, in order.

1. **`one_mem_intFormRatiosC` has no `isIntegralQExp_one` in the port.** The pin's
   Integral block (`Def_ModularCurve_X1.lean:40–61`: `IsIntegralQExp.coeff`,
   `isIntegralQExp_iff`, `IsIntegralQExp.unique`, `isIntegralQExp_one`,
   `isIntegralQExp_zero`) is not ported — only the `IsIntegralQExp` `def` is
   (`WeightOne/Gamma0Integral.lean:98`). The work order's deliverable list omits
   those five, so `X1/Defs.lean` **inlines** the one-line `isIntegralQExp_one`
   proof inside `one_mem_intFormRatiosC` (`rw […, IsIntegralQExp, map_one,
   qExpansion_one]`) instead of declaring a helper. No new declaration, no
   checker impact.

2. **`restrictForm`/`coe_restrictForm`/`restrictForm_apply` binders.** First
   promotion kept the port's explicit `{Γ Γ' : …} {k : ℤ}` binders; the checker
   then reported 3 `MISMATCH`es because the pin declares them under
   `section Restrict` + `variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}`, so the
   pin's declaration text starts at `(h : Γ' ≤ Γ)`. Fix: wrap the promotion in the
   pin's `section Restrict`/`variable` block (`JqIntegralRatios.lean:38–55`).

3. **`diff_pos`/`dif_neg` deprecation.** The pin uses the deprecated
   `dif_pos`/`dif_neg`; the port convention (`Defs/AtkinLehner.lean` header, drift
   checklist) is `dite_eq_left`/`dite_eq_right`. Switched all four occurrences
   (`HeckeOperator.lean` ×2, `Diamond.lean` ×2) before the first clean build.

4. **The mandated `KFamily` import for `fundamentalIdentityAlong` is an import
   cycle.** The work order says to use `Place.sum_ramificationIndex_mul_inertiaDeg`
   (`AlgebraicCurve/ResidueTheorem/KFamily.lean:49`). `KFamily` transitively
   imports `WeilExchange/Transport` itself:
   `KFamily → KRatFunc → P1/Core → … → Canonical/HasCanonicalDivisor →
   WeilExchange/Bifibre → Transport`. Importing it is rejected. Fix: use the
   port's *other* copy of the same sum, `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`
   (`WeilExchange/FiberOverCount.lean:33`), which is acyclic and lighter, plus a
   3-line private bridge at the `fiber` shape the `SumRamificationInertia` field
   needs:
   `rw [show v.fiber F' = v.fiberOver F' by ext w; rw [Place.mem_fiber, Place.mem_fiberOver]]`.
   `FiberOverCount` needs no `[HasPrincipalDivisors K F']`; the class's own
   hypothesis is already in scope. The statement of `fundamentalIdentityAlong` is
   unchanged (the pin's wrapper verbatim).

5. **`restrictForm` promotion collided with a third copy.** After the promotion,
   `ModularForms/WeightOne/IntegralWeightOneForm.lean` failed to compile:
   it *imports* `JqIntegralRatios` and also declares `private def
   ModularCurve.restrictForm` / `private theorem ModularCurve.coe_restrictForm`
   (lines 51/58). Lean rejects a `private` re-declaration when the imported public
   name exists ("a non-private declaration … has already been declared"). Fix: the
   duplicate private def/theorem are deleted (the file already imports
   `JqIntegralRatios`, and its only use `restrictForm hle f` at line 413 now resolves
   to the public copy); the header comment was updated. This is the SET-X1-A
   reconciliation of the promotion and is recorded here rather than in
   `CARRY-FORWARD.md` (the manager owns that file). The file was not in the
   work order's edit list.

6. **`Transport`/`Transcendence` were independent — good.** `Transcendence` is not
   in `Transport`'s closure and vice versa, so `import
   FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence` in `Transport` is
   acyclic (verified mechanically before editing).

7. **Consumer concrete pair.** The obvious pair `ℚ ⊆ RatFunc ℚ` is an instance
   diamond: `Algebra ℚ (RatFunc ℚ)` resolves to `DivisionRing.toRatAlgebra` while
   `RationalFunctionField.hasPrincipalDivisors` is stated with
   `RatFunc.instAlgebraOfPolynomial`, so the `haveI` did not unify. Switched the
   three `Along`/norm-formula instantiations to the port's concrete bar field
   `modularFunctionFieldBar 1` (m11's unconditional
   `hasPrincipalDivisors_modularFunctionFieldBar`), with `φ = AlgHom.id` (a
   degree-one self-extension) and a `private instance` local to the spec zone so
   the `FundamentalIdentityAlong`/`NormFormulaAlong` *types* elaborate.

8. **Consumer call spellings.** `x1FunctionFieldC_rat`/`x1x0FunctionFieldC_one`
   take `M` (and `K`) explicitly (the pin's `variable`), and the pin's
   `coe_heckeAlphaOneBar`/`coe_heckeBetaOneBar` take `M`, `ℓ` explicitly (`L`
   stays implicit because the pin's `variable (L) in` scopes only the `def`s).
   Calls are `… 2 3 x` / `… 2 3 h x`.

## 7. Boundary and deferred surface (manager-owned)

Accepted by the manager as out of SET-X1-A. Not ported, not in `PORT_FILES`:

| declaration | pin |
|---|---|
| `ModularCurve.JOne.torsionGaloisRep` | `Def_ModularCurve_X1.lean:192` |
| `ModularCurve.JOne.torsionGaloisRep_apply` | 198 |
| `ModularCurve.JOne.coe_torsionGaloisRep_apply` | 203 |
| `ModularCurve.diamondOneBar` | `Def_ModularCurve_X1Diamond.lean:98` |
| `ModularCurve.diamondOneBar_apply` | 101 |

Prerequisite (unported; decided homes named in the port's own headers):
`Pic0.torsion`/`mem_torsion`/`instModuleZModTorsion`
(`Def_AlgebraicCurve_DivisorClassGroup.lean` ~247–…), the whole
`SemilinearAut` Divisor/`Pic0` action-and-torsion block including
`SemilinearAut.torsionRep` (`Def_AlgebraicCurve_BaseChangeGalois.lean:206–356`,
home `AlgebraicCurve/Defs/SemilinearAut.lean`), and `ModularCurve.PicAction`
(`Def_ModularCurve_ArithmeticGalois.lean:85–105`, home
`ModularCurve/Defs/ArithmeticGalois.lean`). None of the five is on the
`heckeDiamondInputsAll` cone; they belong to the successor targets
(`heckeDiamondCommuteBar` / `rationalRankTwoNebentypus_family`), which must port
the prerequisite first.

The pin's two `example`s (`Def_ModularCurve_X1.lean:189,212`) and the two in
`section ModularInstance` (`Def_ModularCurve_X1HeckeOperator.lean:234,240`) are
dropped as typecheck-only.

Public URLs use the pin:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeOperator.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1Diamond.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean>.

## 8. Manager review (independent re-run, 2026-10-02)

- **Checker re-run:** `4424 statements identical (150 promoted), 0 mismatched,
  0 missing, 30 own-proof exempted (4454 checked)` — reproduces the worker's
  figure exactly.
- **Consumer re-run:** the zone was `0 errors / 1 warning`; the warning was the
  `linter.style.haveILetI` on `barOne_id_isIntegral` (a `haveI` in a Prop goal
  whose instance is genuinely used by `Algebra.IsIntegral.isIntegral`). Fixed at
  review with a local `set_option linter.style.haveILetI false in` (playbook §6),
  not by weakening the proof; the file is now `0 errors / 0 warnings`.
- **Axioms re-run:** `Divisor.pushforwardNormFormula`,
  `fundamentalIdentityAlong`, `normFormulaAlong` all
  `[propext, Classical.choice, Quot.sound]`.
- **Import-cycle claim (friction 4) verified mechanically:** `KFamily →
  KRatFunc/KCotrace → … → Canonical/HasCanonicalDivisor → WeilExchange/Bifibre →
  Transport`; the `FiberOverCount` route is correct and acyclic.
- **Deviation 2 (friction 5) reviewed:** the deleted `private restrictForm` in
  `WeightOne/IntegralWeightOneForm.lean` had one use (`restrictForm hle f`), which
  now resolves to the public promoted copy; the header was updated. Accepted as
  the promotion's reconciliation.
- **Verdict:** land accepted, no defects found. The two review decisions are
  folded into `topics/hecke/TOPIC-x1-hecke-diamond-inputs.md` §2/§3/§5.
