# WORKORDER MS-7 — the toric-point dictionary at both levels, and `Φ = Φ₂`

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U4 + U5, §1, §2, §3, §4 — the order
whose manager lane is **already landed** ([SET-MSDEF.md](SET-MSDEF.md)). **Story**: U4 + U5.
**Silo**: 951 (373 + 168 + 410). **Net**: ≈780.
**Homes**: two new modules.

| row | silo | home | checker |
|---|---:|---|---:|
| `exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq` | 373 | **new** `ModularCurve/TateSlots/ToricPointDictionary.lean` | absent → 2 ok (with 168) |
| `c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` | 168 | same module | (counted above) |
| `ModularPolynomialData.phi_eq_phiTwo` | 410 | **new** `ModularCurve/ModularPolynomialLevelTwo.lean` | absent → 1 ok |

Imports (verified against the rows' full need sets):

- `TateSlots/ToricPointDictionary.lean`: `…TateSlots.Invariants`, `…Degree.FinrankAdjoinJqNModC`,
  `…Defs.TateFormal`, `FLTForHuman.ModularForms.JqAnalyticModel`, `…X1.Defs`, `…X1.Integral`,
  `…Defs.XHDiamondModL`.
- `ModularPolynomialLevelTwo.lean`: `…JqCoefficients`, `…ModularPolynomialUniquenessIrreducible`,
  `…PhiGenSplitsAnyField`, `…Defs.ClassicalModularPolynomials`.

## The two manager-lane items are in (do not re-do them)

`ModularCurve.IsDiamondPullbackModL` (+ `coe_apply_eq`) is public in
`ModularCurve/Defs/XHDiamondModL.lean` (checker 2 ok) and
`ModularCurve.qExpansion_E6_eq_map_mk` is public in `X1/IntegralityJqNModC.lean` (the `EisensteinCube`
namespace was re-opened after it; the statement is at the pin's root name). Both are premises of
373-XH — **import them, do not restate them**.

## The declarations (verbatim wrappers)

`Theorems/Thm_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean`:

```
theorem ModularCurve.exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ w₁ w₂ : (ZMod M)ˣ → qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (∀ t : (ZMod M)ˣ, (w₁ t : LaurentSeries K) =
        (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
          (tateLaurent K).c₆) ∧
      (∀ t : (ZMod M)ˣ, (w₂ t : LaurentSeries K) =
        ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
            6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄) ∧
      ∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M) (t : (ZMod M)ˣ),
          ρ γ (w₁ t) = w₁ (t * (CohCarrier.gamma0Units M γ)⁻¹) ∧
            ρ γ (w₂ t) = w₂ (t * (CohCarrier.gamma0Units M γ)⁻¹)
```

`Theorems/Thm_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.lean`:

```
theorem ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 ζ).1) / (tateLaurent K).c₆ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) ∧
      ((toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄ ∈ qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)
```

`Theorems/Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean`:

```
theorem ModularCurve.ModularPolynomialData.phi_eq_phiTwo (data : ModularPolynomialData 2) :
    data.Φ = phiTwo
```

## The pin proofs

| row | pin file | lines / decls | namespace and sections |
|---|---|---|---|
| 373-XH | `P2M/Sol/S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean` | 373 / 45 | `W769` (section `Field`, 106–335) |
| 168 | `P2M/Sol/S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.lean` | 168 / 16 | `WeberCusp`: `Forms` 25–58, `Series` 60–92 |
| 410 | `P2M/Sol/S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean` | 410 / 44 | `ModularCurve.PhiTwoCalc` (two blocks: 23–197 and 200–404) |

## Vocabulary

- `tateLaurent` (+ `c₄`, `c₆`, `a₄`), `toricPoint` — `ModularCurve/Defs/TateFormal.lean`,
  `…TateSlots.lean`; the toric-point/tate-series API is the leaves wave's.
- `qExpFunctionFieldC` — `X1/Defs.lean`; `CohCarrier.GammaH`, `CohCarrier.gamma0Units` —
  `ModularForms/Defs/GammaH.lean`.
- `exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum` — `TateSlots/Invariants.lean` (the
  637-line MC-2 row: it is the engine both of these rows sit on); `c4_tatePowerSeries`,
  `c6_tatePowerSeries` — `Degree/FinrankAdjoinJqNModC.lean`; `qExpansion_E4_eq_map_eisenstein4`,
  `qExpansion_E6_eq_map_mk` (now **public**, see above) — `ModularForms/JqAnalyticModel.lean` and
  `X1/IntegralityJqNModC.lean`.
- 410: `ModularPolynomialData`, `data.Φ` — `Defs/Polynomial.lean`; `phiTwo` and `phiTwoC0/C1/C2` —
  `Defs/ClassicalModularPolynomials.lean`; `coeff_jNum_le_six`,
  `eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero` — `JqCoefficients.lean`;
  `natDegree_coeff_le` — `ModularPolynomialUniquenessIrreducible.lean` (MC-1b);
  `PhiGen.splits_prime_of_isPrimitiveRoot` — `PhiGenSplitsAnyField.lean`.

## Traps

1. **The gate is landed but only just**: `IsDiamondPullbackModL` is used by 373-XH's *statement*, so
   a misspelt binder will not even elaborate — that is the def module's job to prevent, and it does.
2. **373-XH's conclusion is a two-level dictionary**: the `w₁`/`w₂` formulas (the `c₄`- and
   `c₄`-normalised toric coordinates), then the `ρ`-equivariance with the *inverse* unit
   `(CohCarrier.gamma0Units M γ)⁻¹` and the `t * …` multiplication in `(ZMod M)ˣ`. Keep every
   coercion: `(t : ZMod M).val`, `(w₁ t : LaurentSeries K)`, `IsPrimitiveRoot ζ M`.
3. **168 is the Γ₁-level twin** of 373-XH's first two conjuncts: same two ratios, membership in
   `qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)` instead of the `Γ_H M ⊥`-valued functions.
   Expect the pin's `WeberCusp.Forms`/`Series` sections to be the reusable half of both; write the
   shared part once inside the module if the two proofs coincide, else keep them separate and say so.
4. **410's pin sets 3,200,000 heartbeats** — do not copy it (FR-0067). The statement is one line; the
   proof is a long coefficient computation: `LowCoeffs`/`conv`/`NF`/`LJ`/`L2`/`nf_*` blocks and then
   `phiTwo_coeff`, `natDegree_phiTwoC`, `qExpandand_evalAtJ_phiTwoC` (the pin's spelling), `eval`,
   `coeff_identities`, `cubic_expand`. Check which of the three coefficient declarations the port's
   `Defs/ClassicalModularPolynomials.lean` already has (`phiTwoC2/C1/C0`, `phiTwo`) before writing
   them.
5. Do not transcribe `p2m_*`, the `P2MW.S_` namespaces, or any `attribute` prelude. No `sorry`.
6. Each new module: two `spec-pin:` lines (wrapper + `S_` copy); the header records the
   public/private split. The toric module has **two** headlines — 2 ok there is the target; its
   shared engine, if any, stays `private`.

## Gates

1. Edit loop per file: `cd lean && timeout 120 lake env lean -DautoImplicit=false
   -DmaxHeartbeats=200000 <file>` → silent, zero warnings.
2. Build each under the **workspace** lock (`flock tmp/lean-build.lock lake build …`), logs in
   `tmp/ms7/` (FR-0072).
3. `python3 spec/check_port.py --force <file>` → ToricPointDictionary **2 ok**, LevelTwo **1 ok**,
   `0 mismatch / 0 missing / 0 own` each.
4. `#print axioms` on all three → `[propext, Classical.choice, Quot.sound]`.
5. `cd tools/deps && python3 dedup.py --targets <stem> --within --tier shape` per module (dry run).
6. No `sorry`/`admit`/`axiom`/`native_decide`, **no `set_option`**, no linter suppression, no other
   file, no git, no tree build; every command under 2 minutes.
7. Report per file: declarations (public/private), lines, checker line, axioms, build result, every
   deviation, and — for the toric module — whether the two headlines share an engine.
