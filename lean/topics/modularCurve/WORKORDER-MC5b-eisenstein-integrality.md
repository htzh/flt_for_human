# WORKORDER MC-5b — the weight-3 Eisenstein form's integral q-expansion

**SET**: [SET-MC5.md](SET-MC5.md) §0–§5. **Story**: M4. **Silk**: 220. **Net**: ≈188.
**Home**: **new** `lean/FLTForHuman/ModularCurve/SiegelUnit/Eisenstein.lean`.

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion.lean`:

```
theorem ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
    (N : ℕ) (hN : 3 ≤ N) :
    ∃ (E : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 3) (a : ℕ),
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff n)) ∧
      (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)
```

Pin proof: `P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion.lean`
(220 lines): build `E` from the Eisenstein series of weight 3 (`eisensteinG`) on `Γ₁(N)`, then the
integrality of `N^a · coeff n` (and of the constant term's inverse), and the same for the `S`-slash
evaluated at `N`.

## Vocabulary

- `ModularCurve.EisensteinSeries.eisensteinG` and the two lemmas
  `exists_modularForm_coe_eq_eisensteinG`, `qExpansion_eisensteinG_coeff` —
  `ModularForms/EisensteinSeries.lean` (premises).
- `eisensteinG_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral` (the integrality engine) —
  `ModularForms/Eisenstein/ConstTermCubeIntegral.lean` (premise).
- `UpperHalfPlane.qExpansion`, `IsIntegral`, `ModularForm`'s `∣[k]` slash — ported/mathlib.

## Traps

1. The statement is the pin's **five-clause** existential: transcribe it verbatim, including
   `(N : ℂ) ^ a`, the inverse of `coeff 0`, and the `qExpansion (N : ℝ)` third clause. A missing
   clause is a MISMATCH.
2. The three premises are `Thm_` headlines, already ported — import them; do not re-prove the
   integrality engine.
3. `hN : 3 ≤ N` is only used to make `Γ₁(N)` non-trivial; keep the binder.
4. Do not reproduce the pin's `attribute [-simp]` prelude.

## Gates

As WORKORDER-MC5a's §Gates, with: `check_port` → the headline `ok`; **two** `spec-pin:` lines
(its `Thm_` wrapper and `S_` copy); one module build; axioms; silent; no `set_option`; no other file.
