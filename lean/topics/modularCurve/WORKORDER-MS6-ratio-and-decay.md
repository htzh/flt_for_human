# WORKORDER MS-6 — the ratio dictionary and the index bound, and cusp decay under integrality

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U6 + U8, §1, §2, §3, §4.
**Story**: U6 + U8. **Silo**: 1,342 (166 + 442 + 734). **Net**: ≈905.
**Homes**: one insertion, two new modules.

| row | silo | home | checker |
|---|---:|---|---:|
| `exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC` | 166 | insert `ModularCurve/X1/CoeffMap.lean` | **93 → 94** |
| `finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index` | 442 | **new** `ModularCurve/X1/FunctionFieldIndex.lean` | absent → 1 ok |
| `eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow` | 734 | **new** `ModularCurve/Analytic/CuspDecay.lean` | absent → 1 ok |

Imports (verified against the rows' full need sets):

- `X1/FunctionFieldIndex.lean`: `ModularCurve.X1.FunctionFieldResidue`, `…X1.CoeffMap`,
  `…X1.FunctionFieldDegree`, `…JqIntegralRatios`, `…Degree.PhiDegree`,
  `FLTForHuman.NumberTheory.FrobeniusAtPlace`.
- `Analytic/CuspDecay.lean`: `…JqIntegralRatios`, `FLTForHuman.ModularForms.JqAnalyticModel`,
  `FLTForHuman.ModularForms.QCoeffLevelOne`, `…Analytic.QParamUnique`,
  `FLTForHuman.ModularForms.HeckeQCoeff`.
- The insertion needs none.

## The declarations (verbatim wrappers)

`Theorems/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC.lean`:

```
theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
    ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 ∧
      x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
```

`Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean`:

```
theorem ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index
```

`Theorems/Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean`:

```
theorem ModularCurve.eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ)
    (hm : 1 ≤ m) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (M : ℕ)
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.jqModC ℂ ^ (m * M + 1) *
        (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M)))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∣[k + 14 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ ≤
        ε * ‖((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∣[k + 12 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖
```

## The pin proofs

| row | pin file | lines / decls | namespace and sections |
|---|---|---|---|
| 166 | `P2M/Sol/S_…_of_mem_laurentBaseChange_qExpFunctionFieldC.lean` | 166 / 20 | `ModularCurve.RatioFieldOfLevelG` (17–153, one section) |
| 442 | `P2M/Sol/S_…_qExpFunctionFieldC_le_index.lean` | 442 / 16 | `P2MKcQExpDeg`: `Transfer` 32–266, `Residue` 268–326, `CharZero` 328–344, `Bound` 346–405 |
| 734 | `P2M/Sol/S_…_adjoin_jqModC_inv_pow.lean` | 734 / 53 | `ANb` twice (22–291, 294–490) |

**The residue block is already in the port.** 442's `Transfer`/`Residue` sections' declarations —
`isAlgebraic_residueField` (59 lines), `residueTopHom` (17), `map_mem_adjoin` (15),
`image_intFormRatiosC` (14), `map_mem_qExpFunctionFieldC` (12) — are **public** in
`X1/FunctionFieldIsAlgClosed.lean` (MC-3's module): import and reuse. The one exception is
`Φ_injective` (15 lines): the port's declaration of that name is a **private** `WeightOne/Gamma1Basis`
Φ over a different map, so **re-prove** the pin's `Φ_injective` (it is 4 lines: `coeffMap_coeff` +
`φ.injective`).

## Vocabulary

- `ModularCurve.qExpFunctionFieldC`, `jqModC` — `Defs/Jq.lean`, `X1/Defs.lean`.
- `ModularCurve.laurentBaseChange`, `coeffMap` — `Defs/Laurent.lean`; the `_of_T_mem` twin
  `exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem` is
  **already in** `X1/CoeffMap.lean` and is the statement to sit beside (do not dedup the two: the
  twin states `ModularForm Γ k` for `Γ : Subgroup SL(2, ℤ)`, this row the `GL (Fin 2) ℝ`-coerced form
  with `[Γ.FiniteIndex]`).
- `ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_…_le_index` (a premise) —
  `X1/FunctionFieldDegree.lean`; `exists_transcendental_finiteDimensional_…_residueField` —
  `X1/FunctionFieldResidue.lean`; `transcendental_jqModC` — `Degree/PhiDegree.lean`;
  `ValuationSubring.exists_liesOverPrime_algebraicClosure_rat` —
  `FLTForHuman/NumberTheory/FrobeniusAtPlace.lean`.
- 734's premises: `jqModC_eq_qExpansion_E4_cube_div_discriminant` (`JqIntegralRatios.lean`),
  `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (`ModularForms/JqAnalyticModel.lean`),
  `levelOne_weight_four/six_qCoeff_one`, `levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant`
  (`ModularForms/QCoeffLevelOne.lean`), `tendsto_atImInfty_of_hasSum_qParam`
  (`Analytic/QParamUnique.lean`).

## Traps

1. **442's pin `S_` sets `maxHeartbeats 6400000` and `synthInstance.maxHeartbeats 1600000`, and 734's
   sets 3,200,000.** The port has never needed a pin cap (FR-0067): **do not copy any of them**. If a
   declaration will not fit at 200k, diagnose the inference (`set_option trace.Meta.synthInstance
   true` on that one declaration); a genuine long proof is restructured, not exempted.
2. 442's `Bound` section is the finrank/index comparison: `bound_of_isAlgClosed`, the `Γ'.index`
   comparison through `finrank_adjoin_…_le_index`, and the `liesOverPrime` transport. Read
   `exists_transcendental_finiteDimensional_…_residueField` first.
3. **734's `Nice`/`niceSubalgebra` engine is ALREADY PORTED — reuse it, do not transcribe it**
   (correction, 2026-10-28, after the brief was written). The pin's 734 `S_` file's namespace is
   `ANb`, and `lean/FLTForHuman/ModularCurve/Analytic/ANb.lean` is that namespace: `Nice`
   (Periodic ∧ MDifferentiable ∧ IsBoundedAtImInfty), `Nice.mul/.add/.const`, `niceSubalgebra`,
   `an`, `qexpHom`, `ψ`, `toC`, `analyticAt_toC`, `nice_of_modularForm`, `ofMF`, `𝔞`. Add
   `import FLTForHuman.ModularCurve.Analytic.ANb` and reuse them (qualified, or `open
   ModularCurve.ANb`). **Do not declare a new `Nice`**: the port also has
   `ModularCurve.Nice` in `X1/FunctionField.lean:530`, a *different* predicate over the same
   argument type, so a third copy is a collision hazard and a `dedup.py` cluster. What remains of
   734 is the decay part (`coeffEmb_jq_eq_jqModC` … `coreC`, the headline) — check each name against
   `ANb.lean` and `port_advise`'s 160 in-port lines first.
4. 734's `coreC` is the domination step: `J_sub_mul_D`, `order_le_of_identity`, `J_ne_zero`,
   `Jinv_mul_A_cube`, `tendsto_nice`, `norm_le_of_monic_relation` — the `E₄²E₆` vs `Δ` comparison at
   i∞. Its statement is a `∀ᶠ` at `atImInfty`; keep the `‖·‖` and the `∣[k + 14m]`/`∣[k + 12m]`
   weights exactly.
5. 166 is short (20 declarations) but its `hx` binder and `[Γ.FiniteIndex]` are statement-level; the
   `_of_T_mem` twin does not have the `FiniteIndex` instance, so the insertion must compile both.
6. The insertion must **append** (new section + two `spec-pin:` lines) without disturbing
   `X1/CoeffMap.lean`'s 93 existing verdicts.

## Gates

1. Edit loop per file: `cd lean && timeout 120 lake env lean -DautoImplicit=false
   -DmaxHeartbeats=200000 <file>` → silent, zero warnings.
2. Build each under the **workspace** lock: `flock tmp/lean-build.lock lake build
   FLTForHuman.ModularCurve.X1.FunctionFieldIndex` / `…ModularCurve.Analytic.CuspDecay` /
   `…ModularCurve.X1.CoeffMap`; long builds as background jobs with logs in `tmp/ms6/` (FR-0072).
3. `python3 spec/check_port.py --force <file>` → CoeffMap **94 ok**, each new module **1 ok**, all
   `0 mismatch / 0 missing / 0 own`.
4. `#print axioms` on all three → `[propext, Classical.choice, Quot.sound]`.
5. Two `spec-pin:` lines per file (wrapper + `S_`).
6. `cd tools/deps && python3 dedup.py --targets <stem> --within --tier shape` per module (dry run,
   report only).
7. No `sorry`/`admit`/`axiom`/`native_decide`, **no `set_option`**, no linter suppression, no other
   file, no git, no tree build; every command under 2 minutes.
8. Report per file: declarations (public/private), lines, checker line, axioms, build result, every
   deviation (including any place you had to add a mathlib import the brief did not name).
