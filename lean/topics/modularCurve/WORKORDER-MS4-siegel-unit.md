# WORKORDER MS-4 — the Siegel unit: its integral `q`-expansion, its peaked exponent, its product law

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U2, §1, §2, §3, §4. **Story**: U2.
**Silo**: 1,621 (1,057 + 373 + 191). **Net**: ≈1,557 — the set's most expensive story per silo.
**Homes**: one new module and two insertions.

| row | silo | home | checker |
|---|---:|---|---:|
| `SiegelUnit.exists_isIntegral_hasSum_siegelFun` | 1,057 | **new** `ModularCurve/SiegelUnit/Integrality.lean` | module absent → 1 ok |
| `SiegelUnit.exists_peaked_exponent` | 373 | insert `ModularCurve/SiegelUnit/BernoulliWeight.lean` | **67 → 68** |
| `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul` | 191 | insert `ModularCurve/SiegelUnit/Basic.lean` | **9 → 10** |

Imports (verified against the rows' full need set): the new module needs
`FLTForHuman.ModularCurve.SiegelUnit.Basic` + `FLTForHuman.ModularCurve.Analytic.QParamUnique`
(acyclic — `QParamUnique` imports no port module); the two insertions need none.

## The declarations (verbatim wrappers)

`Theorems/Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean`:

```
theorem ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun (N : ℕ) (r s : ℤ)
    (hr : 0 ≤ r) (hrN : r < N) (hs : r = 0 → ¬ (N : ℤ) ∣ s) :
    ∃ c : ℕ → ℂ, (∀ n : ℕ, IsIntegral ℤ (c n)) ∧
      c 0 = (if r = 0 then 1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) / (N : ℂ)) else 1) ∧
      IsIntegral ℤ ((N : ℂ) * (c 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          (siegelFun N r s (τ : ℂ) /
            (-Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
              Complex.exp (2 * Real.pi * Complex.I *
                (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
                  (12 * (N : ℂ) ^ 2))))) ∧
      Filter.Tendsto (…) UpperHalfPlane.atImInfty (nhds (c 0))
```

`Theorems/Thm_ModularCurve_SiegelUnit_exists_peaked_exponent.lean`:

```
theorem ModularCurve.SiegelUnit.exists_peaked_exponent (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (m : ZMod N → ZMod N → ℕ) (Ord : ZMod N → ZMod N → ℤ),
      (∀ x y : ZMod N, Ord x y = ∑ r : ZMod N, ∑ s : ZMod N,
        (m r s : ℤ) * (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
          - 6 * (N : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (N : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧ (∀ r s : ZMod N, m r (s + r) = m r s) ∧ 0 < Ord 1 0 ∧
      ∀ x y : ZMod N, (∃ a b : ZMod N, a * x + b * y = 1) → ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) →
        ¬ (y = 1 ∨ y = -1) → Ord 1 0 < Ord x y
```

`Theorems/Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.lean`:

```
theorem ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) :
    (∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
              (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
            ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
              (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
            (τ : ℂ) ^ (12 * N * e r s)) ∧
    ((∀ r s : ZMod N, e r (s + r) = e r s) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma1 N →
        ∀ τ : UpperHalfPlane,
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
            ∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)))
```

## The pin proofs

**1,057** — `P2M/Sol/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean`, 1,057 lines,
117 declarations, in `ModularCurve.SiegelUnit.SEXP1`, namespace `EulerProdFam`:

| section | pin lines | content |
|---|---|---|
| `Formal` | 22–138 | `fac`, `pp`, `pp_zero`/`pp_succ`, `coeff_fac_sub_one`, `order_fac_sub_one`, `coeff_mul_fac_of_le`, `coeff_prod_range_fac`, `coeff_pp_stable`, `map_fac`, `multipliable_fac`, `coeff_W` (+ `W`), `continuous_map`, `constantCoeff_W`; then `Pabs`, `Cst`, `Cst_nonneg`, `coeff_Pabs*`, `zero_mem_support`, `eval_sub_one_eq`, `norm_eval_sub_one_le`, `eval_Pabs*`, `one_le_eval_Pabs`, `Mfam`, `norm_coeff_mul_le`, `norm_coeff_expand_le`, `norm_coeff_pp_le`, `coeff_pp_Mfam_*`, `coeff_le_coeff_mul`, `coeff_expand_Pabs_*`, `dom`, `Mfam_coeff_zero`, `norm_coeff_pp_le_dom`, `sum_coeff_le_eval`, `eval_pp`, `Bd` |
| `Topological` | 86–136 | `summable_pow_succ`, `prod_eval_Pabs_le`, `summable_dom`, `summable_norm_eval_sub_one`, `multipliable_eval`, `tprod_eval_ne_zero`, `tsum_coeff_pp_mul_pow`, `hasSum_coeff_W`, `R₀` |
| `Analytic` | 140–427 | `isIntegral_zeta`, `zeta0`, `Pz`, `Pz_coeff_zero`, `qN`/`qN_eq_qParam`/`qN_ne_zero`/`norm_qN_lt_one`/`tendsto_qN`/`exists_qN_eq`, `rho_pow`, `N_mul_inv_one_sub`, `isIntegral_exp_of_pow`, `isIntegral_N_mul_inv_one_sub`, `q_eq`/`qa_eq`/`qpow_mul_qa*`, `pref_eq`, `E_pow`, `multipliable_one_sub_mul_pow`, `tprod_ite_natCast_eq*`, `neg_natCast_eq`, `siegel_streams`, `siegelFun_div_eq_streams`, `tprod_Pc_eval`, `zeta`/`zeta_ne_zero`/`norm_zeta`/`norm_zeta_inv`/`isIntegral_zeta*`/`zeta_inv_eq_pow` |
| `ArchSkel` (436+) | 436–1,036 | `Pc`, `M2`, `coeff_one_sub_C_mul_X`, `Pc_coeff_zero`, `M2_coeff_zero`, `Pc_eval`, `norm_coeff_ite_le`, `Pc_dom`, the `CoeffInt` structure (`.one`, `.mul`, `.expand`, `.one_sub_C_mul_X`, `.ite`), `coeffInt_Pc`, `coeffInt_pp`, `isIntegral_coeff_W`, `SEXP1.tprod_Pc_eval`, `siegelFun_div_eq`, `coef`, `hasSum_coef`, `isIntegral_coef`, `coef_zero`, `zeta_ne_one`, `isIntegral_N_mul_inv_coef_zero`, `main`, `solution` |

**373** — `P2M/Sol/S_ModularCurve_SiegelUnit_exists_peaked_exponent.lean`, 373 lines, 12 declarations,
namespace `Peak`: `sums` (29–108) — `mem_span_levelBernoulliWeight_dilate_iff_even`,
`sum_levelBernoulliWeight_add_mul`, `sum_totient_mul_levelBernoulliWeight_dilate_eq_zero` (all
**ported**, in `SiegelUnit/BernoulliWeight.lean`); `construction` (114–157) — the `m`/`Ord`
construction and the inequality chain over `ZMod N`.

**191** — `P2M/Sol/S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.lean`, 191
lines, 13 declarations, namespace `SiegelTransport`: the `S`/`T`-decomposition transport of the
double product, `siegelFun_add_level` and `siegelFun_specialLinearGroup_smul` (both **ported**, in
`SiegelUnit/Basic.lean`).

## Vocabulary

- `ModularCurve.siegelFun`, `siegelFun_def` — `ModularCurve/Defs/SiegelFunction.lean`.
- `siegelFun_specialLinearGroup_smul`, `siegelFun_add_level`, the `qC`/`siegelFun_eq` q-product
  prelude — `ModularCurve/SiegelUnit/Basic.lean` (MC-5a).
- `mem_span_levelBernoulliWeight_dilate_iff_even`, `sum_levelBernoulliWeight_add_mul`,
  `sum_totient_mul_levelBernoulliWeight_dilate_eq_zero` — `SiegelUnit/BernoulliWeight.lean` (leaves
  wave).
- `ModularCurve.tendsto_atImInfty_of_hasSum_qParam` — `Analytic/QParamUnique.lean` (the one premise
  of 1,057).
- `UpperHalfPlane.atImInfty`, `Filter.Tendsto`, `IsIntegral`, `tprod`/`HasSum` — mathlib.

## Traps

1. **1,057 is a self-contained analytic engine with a single premise and nothing in the port.** It is
   the set's only analytic risk: budget it as one work item, and expect the pin's 117 declarations to
   come over nearly whole (port_advise: `in port 0`). The engine's spine is
   `fac`/`pp`/`multipliable_fac` (the q-product), `Pabs`/`Mfam`/`norm_coeff_pp_le_dom` (absolute
   convergence and the domination bound), `summable_pow_succ`/`prod_eval_Pabs_le`
   (`tprod_eval_ne_zero`), then the arithmetic layer (`zet`a, `qN`, `CoeffInt`) and the final
   `siegelFun_div_eq` → `coef` → `main`.
2. **The exact `c 0` and the `N·c 0⁻¹` integrality are part of the statement** — do not replace the
   `if r = 0` case by a generic exponential: the pin's `1 - exp(2πi s/N)` and the `(N : ℂ) * (c 0)⁻¹`
   integrality are both used downstream (the Siegel product/peaked-form chain).
3. The `siegelFun_div_eq_streams` rewrite uses the port's `siegelFun_def` q-product
   (`SiegelUnit/Basic.lean`); read that module's `qC`/`siegelFun_eq` before re-deriving any stream.
4. **191's statement is two clauses**: (i) for *every* `e : ZMod N → ZMod N → ℕ` and every `β`, the
   double product is invariant with the permuted index; (ii) *under the hypothesis*
   `∀ r s, e r (s + r) = e r s` and for `γ ∈ Γ₁(N)`, the product is `γ`-invariant. Keep both, and
   keep the `ZMod`-valued index dance (`(… : ℤ) : ZMod N).val`) exactly.
5. **373 constructs `m` and `Ord`**; its hypotheses (`m 0 0 = 0`, the `s + r`-invariance, `0 < Ord 1 0`,
   and the strict inequality off the four excluded cosets) are all part of the conclusion — do not
   weaken the `¬ (y = 0 ∧ (x = 1 ∨ x = -1))`/`¬ (y = 1 ∨ y = -1)` exclusions.
6. No pin cap on any of the three files (`set_option autoImplicit false` only). If something does not
   fit at 200k, diagnose; never add `set_option maxHeartbeats`.
7. The two insertions must **append** (a new section + two `spec-pin:` lines) and must not disturb the
   hosts' existing verdicts (67 and 9) or their private preludes.

## Gates

1. Edit loop per file: `cd lean && timeout 120 lake env lean -DautoImplicit=false
   -DmaxHeartbeats=200000 <file>` → silent, zero warnings.
2. Build each file under the **workspace** lock: `flock tmp/lean-build.lock lake build
   FLTForHuman.ModularCurve.SiegelUnit.Integrality` (then `…SiegelUnit.BernoulliWeight`,
   `…SiegelUnit.Basic`); long builds as background jobs with logs in `tmp/ms4/` (FR-0072).
3. `python3 spec/check_port.py --force <file>` → the new module **1 ok**, BernoulliWeight **68**,
   Basic **10**, each `0 mismatch / 0 missing / 0 own`.
4. `#print axioms` on all three → `[propext, Classical.choice, Quot.sound]`.
5. Two new `spec-pin:` lines per file (wrapper + `S_`); the new module gets exactly two.
6. `cd tools/deps && python3 dedup.py --targets <stem> --within --tier shape` per module (dry run,
   report only; 1 intra cluster of the pin's own wrapper-over-engine shape is acceptable if recorded).
7. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression, no
   `attribute`/`p2m_*` prelude, no other file, no git, no tree build; every command under 2 minutes.
8. Report per file: declarations (public/private), lines, checker line, axioms, build result, every
   deviation. If 1,057 cannot be finished, land 373 and 191 and report the state of the new module —
   do not leave a non-compiling file behind.
