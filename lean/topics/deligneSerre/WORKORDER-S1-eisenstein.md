# Work order — S1: the weight-one Eisenstein series (5 nodes)

**Status: ready to dispatch once phase H closes (2026-09-29).** The first theorem
set of the Deligne–Serre weight-one port. Method handbook:
`lean/porting-playbook.md` (§2.4 dedup, §3.1–§3.5 module-as-role / build ladder,
§4 faithfulness, §6 proof failure modes). This file is the scope. The mathematics
is `math/019-deligne-serre-weight-one.md` §3.

## 0. Scope

The `E₁(1, χ)` multiplier: for a primitive odd Dirichlet character `χ` mod `L`,
build the weight-one Eisenstein series whose `q`-expansion has constant term
`-∑ a·χ(a)/(2L)` and coefficients `∑_{d ∣ n} χ(d)`, from the cotangent expansion of
the Weierstrass `ζ`-function and its quasi-periods.

**Explicitly not this set:** the Hecke / `Γ₁` vanishing (S2), the relèvement and
the lifting (S3), anything in S4–S8. Edit only files under
`FLTForHuman/ModularForms/Eisenstein/` (plus the checker config).

## 1. The five public targets — statements verbatim from the pin wrappers

```lean
theorem EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 (τ : UpperHalfPlane) (z : ℂ)
    (hz : ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) :
    HasSum (fun m : ℕ => π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) +
        π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ)))
      (EisensteinSeries.weierstrassZeta τ z - z * EisensteinSeries.G2 τ -
        π * Complex.cot (π * z))
```

```lean
theorem EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul (τ : UpperHalfPlane) :
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + 1) =
          EisensteinSeries.weierstrassZeta τ z + EisensteinSeries.G2 τ) ∧
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + τ) =
          EisensteinSeries.weierstrassZeta τ z +
            ((τ : ℂ) * EisensteinSeries.G2 τ - 2 * π * Complex.I)) ∧
    (∀ (γ : SL(2, ℤ)) (z : ℂ),
        EisensteinSeries.weierstrassZeta (γ • τ) (z / UpperHalfPlane.denom γ τ) =
          UpperHalfPlane.denom γ τ * EisensteinSeries.weierstrassZeta τ z)
```

```lean
theorem EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) :
    (∀ (γ : SL(2, ℤ)) (v : Fin 2 → ℤ),
        EisensteinSeries.eisensteinG1 N v (γ • τ) =
          UpperHalfPlane.denom γ τ *
            EisensteinSeries.eisensteinG1 N (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ) ∧
    (∀ v w : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        EisensteinSeries.eisensteinG1 N (v + (N : ℤ) • w) τ =
          EisensteinSeries.eisensteinG1 N v τ)
```

```lean
theorem EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1 (N : ℕ) [NeZero N] :
    (∀ v : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.eisensteinG1 N v)) ∧
    (∀ (b : ℤ), ¬ (N : ℤ) ∣ b → ∀ τ : UpperHalfPlane,
        HasSum (fun n : ℕ => (if n = 0 then π / N * Complex.cot (π * b / N) else
            -(2 * π * Complex.I) / N * ∑ k ∈ n.divisors,
              (Complex.exp (2 * π * Complex.I * b * k / N) -
                Complex.exp (-(2 * π * Complex.I * b * k / N)))) *
            Complex.exp (2 * π * Complex.I * τ) ^ n)
          (EisensteinSeries.eisensteinG1 N ![0, b] τ))
```

```lean
theorem ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
    (L : ℕ) [NeZero L] (χ : DirichletCharacter ℂ L) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    ∃ E : ModularForm (Gamma1 L) 1,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ τ : UpperHalfPlane,
        E (γ • τ) =
          χ ((γ 1 1 : ℤ) : ZMod L) *
            ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) * E τ)) ∧
      ModularFormClass.qCoeff E 0 =
        -(∑ a ∈ Finset.range L, (a : ℂ) * χ (a : ZMod L)) / (2 * L) ∧
      ∀ n : ℕ, 0 < n → ModularFormClass.qCoeff E n = ∑ d ∈ n.divisors, χ (d : ZMod L)
```

`p2m_*` / `P2M.Util` scaffolding in the pin is **not** ported (playbook §1).

## 2. Homes and dependency order

Already on disk and to be imported, not re-proved:

- `FLTForHuman/ModularForms/Eisenstein/WeierstrassZeta.lean` (phase D) —
  `EisensteinSeries.weierstrassZeta`, `EisensteinSeries.eisensteinG1`; mathlib's
  `EisensteinSeries.G2` comes from `…EisensteinSeries.E2.Defs`.
- `FLTForHuman/ModularForms/Eisenstein/Cotangent.lean` (phase H1) — the shared
  cotangent/lattice prelude, namespace `EisensteinSeries`:
  `norm_pi_cot_add_le`, `pi_cot_add_eq`, `norm_pi_cot_sub_le`, `norm_cexp_two_pi_I`,
  `add_intCast_mul`, `add_intCast`, `cot_neg`, `NotLat`, `pval`, `ser`, `zterm`,
  `om`, `om_smul`, `om_injective`, `weierstrassZeta_eq`. **`hasSum_ser` is *not*
  in the home**: its pin proof appeals to `hasSum_weierstrassZeta_sub_mul_G2`, so
  it is ported inside this set, in `WeierstrassZetaQuasiPeriod.lean` (WZB) after
  WZA. Confirm the exact exported names against the file before writing.

New modules, one per pin `S_` file, in the pin's import order (each imports the
previous target's module, **not** the pin `Thm_` wrapper). All in namespace
`EisensteinSeries`; the pin's per-file `WZ*`/`WZE` namespaces are scaffolding and
are not ported.

| pin `S_` | new port module | public target landed |
|---|---|---|
| `…hasSum_weierstrassZeta_sub_mul_G2` | `ModularForms/Eisenstein/WeierstrassZetaSum.lean` | `EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2` |
| `…weierstrassZeta_add_one_and_add_tau_and_smul` | `ModularForms/Eisenstein/WeierstrassZetaQuasiPeriod.lean` | `EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul` |
| `…eisensteinG1_apply_smul_and_eisensteinG1_add` | `ModularForms/Eisenstein/EisensteinG1Transform.lean` | `EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add` |
| `…isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1` | `ModularForms/Eisenstein/EisensteinG1QExpansion.lean` | `EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1` |
| `S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` | `ModularForms/Eisenstein/WeightOneMultiplier.lean` | `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` |

The last module keeps the pin's `ModularForm.*` namespace on its public target;
its helpers stay `EisensteinSeries`/`private`.

## 3. Route and reuse

- **Reuse, do not re-prove, the H1 blocks.** Every occurrence the appendix marks
  `**shared → H1**` is imported from `Cotangent.lean`. If a needed helper is absent
  from it, prefer a `private` local restatement and log it — do **not** edit the
  closed H1 file (work order `TOPIC-port-order.md` §2).
- **Mathlib map (verify each before use; keep a recorded negative for a miss):**
  cotangent identities `Complex.cot_pi_eq_exp_ratio`, `Complex.norm_exp`,
  `Complex.cot_neg`; the `HasSum`/`Summable`/`tsum` API; `UpperHalfPlane.denom`,
  `UpperHalfPlane.IsBoundedAtImInfty`; `EisensteinSeries.G2`, `e2Summand`;
  `DirichletCharacter` primitivity/oddness, Gauss sums (`gaussSum`), `ZMod`
  character sums; `SlashInvariantForm`, `ModularForm`, `ModularFormClass.qCoeff`,
  `MDifferentiable`.
- **The `q`-expansion module (W1) is the risk.** Its pin proof is 703 lines of
  Gauss-sum and `q`-series analysis; if a step needs mathematics mathlib lacks,
  stop and report rather than weaken a statement.
- Keep proofs faithful to the pin's route; a blow-up is bisected (§6 of the
  playbook), never waited on.

## 4. Verification, build discipline, closing

- Checker wiring: append each new module to `PORT_FILES` and each pin
  `P2M/Sol/S_*.lean` to `SOURCES` in `spec/check_flt_statements.py` (closing `]` at
  lines 1607 and 1248); append last. Run `python3 spec/check_flt_statements.py`
  after each module; it must stay 0 mismatched / 0 missing.
- Edit loop: `timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`.
  File done: `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.<Dotted.Path>`.
  One build per module; **no bare whole-tree `lake build`**; never raise
  `maxHeartbeats`/`maxRecDepth`; no `sorry`/`admit`/`axiom`/`native_decide`; no
  `import Mathlib` in a library module.
- A module is closed when it builds green, the checker is 0/0, `#print axioms` on
  its headline is `[propext, Classical.choice, Quot.sound]`, no `sorry` remains,
  and any locally-resolved share is in `lean/logs/deligne-serre-friction.md`.
- Do not run writing git commands. Stop and report if a statement cannot be
  transcribed faithfully, a build blows up after the cheap remedies, or a proof
  needs unported mathematics.

---

## Appendix — per-file pin declaration inventory

#### WZA — pin `P2M/Sol/S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean` (539 lines, 46 declarations)

| decl | kind | line | lines to next | note |
|---|---|---:|---:|---|
| `om` | def | 18 | 2 | **shared → H1** |
| `zterm` | def | 20 | 3 | **shared → H1** |
| `weierstrassZeta_eq` | lemma | 23 | 2 | **shared → H1** |
| `om_ne_zero` | lemma | 25 | 10 |  |
| `om_zero` | lemma | 35 | 2 |  |
| `norm_om_ge` | lemma | 37 | 3 |  |
| `zterm_eq_of_ne` | lemma | 40 | 8 |  |
| `eventually_le_norm` | lemma | 48 | 7 |  |
| `zterm_isBigO` | lemma | 55 | 48 |  |
| `summable_zterm` | lemma | 103 | 3 |  |
| `summable_zterm_prod` | lemma | 106 | 3 |  |
| `row` | def | 109 | 2 |  |
| `summable_row` | lemma | 111 | 3 |  |
| `summable_zterm_right` | lemma | 114 | 3 |  |
| `tsum_zterm_eq_tsum_row` | lemma | 117 | 10 |  |
| `cot_neg` | lemma | 127 | 3 | **shared → H1** |
| `intComp_add_ne_zero` | lemma | 130 | 5 |  |
| `summable_inv_mul_linear` | lemma | 135 | 11 |  |
| `hasSum_inv_linear_sub` | lemma | 146 | 34 |  |
| `IsLatticePt` | def | 180 | 2 |  |
| `intComp_of_not_isLatticePt` | lemma | 182 | 6 |  |
| `intComp_self_of_not_isLatticePt` | lemma | 188 | 5 |  |
| `ne_zero_of_not_isLatticePt` | lemma | 193 | 4 |  |
| `intComp_mul_of_ne_zero` | lemma | 197 | 11 |  |
| `E2row` | def | 208 | 2 |  |
| `summable_E2row_summand` | lemma | 210 | 3 |  |
| `E2row_eq_e2Summand` | lemma | 213 | 5 |  |
| `row_of_ne_zero` | lemma | 218 | 26 |  |
| `azero` | def | 244 | 2 |  |
| `tsum_azero` | lemma | 246 | 24 |  |
| `row_zero` | lemma | 270 | 26 |  |
| `norm_cexp_two_pi_I` | lemma | 296 | 5 | **shared → H1** |
| `pi_cot_add_eq` | lemma | 301 | 12 | **shared → H1** |
| `norm_pi_cot_add_le` | lemma | 313 | 22 | **shared → H1** |
| `norm_pi_cot_sub_le` | lemma | 335 | 9 | **shared → H1** |
| `crow` | def | 344 | 4 |  |
| `row_eq_crow_add` | lemma | 348 | 6 |  |
| `im_int_mul` | lemma | 354 | 2 |  |
| `summable_crow_nat` | lemma | 356 | 44 |  |
| `summable_crow_neg` | lemma | 400 | 47 |  |
| `summable_crow` | lemma | 447 | 3 |  |
| `not_isLatticePt_half` | lemma | 450 | 17 |  |
| `summable_E2row` | lemma | 467 | 11 |  |
| `hasSum_E2row` | lemma | 478 | 10 |  |
| `hasSum_weierstrassZeta_sub` | theorem | 488 | 42 |  |
| `solution` | theorem | 530 | 10 |  |

#### WZB — pin `P2M/Sol/S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean` (284 lines, 27 declarations)

| decl | kind | line | lines to next | note |
|---|---|---:|---:|---|
| `om` | def | 21 | 2 | **shared → H1** |
| `zterm` | def | 23 | 3 | **shared → H1** |
| `weierstrassZeta_eq` | lemma | 26 | 2 | **shared → H1** |
| `om_smul` | lemma | 28 | 6 | **shared → H1** |
| `vecMulEquiv` | def | 34 | 10 |  |
| `vecMul_eq_zero_iff` | lemma | 44 | 11 |  |
| `zterm_smul` | lemma | 55 | 18 |  |
| `weierstrassZeta_smul` | theorem | 73 | 11 |  |
| `cot_neg` | lemma | 84 | 3 | **shared → H1** |
| `cot_pi_add_one` | lemma | 87 | 6 |  |
| `cot_pi_add_intCast` | lemma | 93 | 8 |  |
| `norm_cexp_two_pi_I` | lemma | 101 | 5 | **shared → H1** |
| `pi_cot_add_eq` | lemma | 106 | 12 | **shared → H1** |
| `norm_pi_cot_add_le` | lemma | 118 | 22 | **shared → H1** |
| `norm_pi_cot_sub_le` | lemma | 140 | 9 | **shared → H1** |
| `tendsto_pi_cot_add` | lemma | 149 | 30 |  |
| `tendsto_pi_cot_sub` | lemma | 179 | 8 |  |
| `NotLat` | def | 187 | 4 | **shared → H1** |
| `NotLat.add_intCast` | lemma | 191 | 6 |  |
| `NotLat.add_intCast_mul` | lemma | 197 | 9 |  |
| `ser` | def | 206 | 3 | **shared → H1** |
| `pval` | def | 209 | 2 | **shared → H1** |
| `hasSum_ser` | lemma | 211 | 3 | not in H1 — port in S1 (after WZA) |
| `weierstrassZeta_add_one` | theorem | 214 | 14 |  |
| `telescope` | lemma | 228 | 9 |  |
| `weierstrassZeta_add_tau` | theorem | 237 | 35 |  |
| `solution` | theorem | 272 | 13 |  |

#### WZC — pin `P2M/Sol/S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean` (212 lines, 17 declarations)

| decl | kind | line | lines to next | note |
|---|---|---:|---:|---|
| `om` | def | 19 | 2 | **shared → H1** |
| `om_smul` | lemma | 21 | 6 | **shared → H1** |
| `coe_smul_eq` | lemma | 27 | 6 |  |
| `denom_eq` | lemma | 33 | 4 |  |
| `G2_smul` | lemma | 37 | 10 |  |
| `det_eq` | lemma | 47 | 6 |  |
| `eisensteinG1_smul` | theorem | 53 | 39 |  |
| `NotLat` | def | 92 | 4 | **shared → H1** |
| `NotLat.add_intCast` | lemma | 96 | 6 |  |
| `NotLat.add_intCast_mul` | lemma | 102 | 9 |  |
| `weierstrassZeta_add_int` | lemma | 111 | 16 |  |
| `weierstrassZeta_add_int_mul` | lemma | 127 | 17 |  |
| `weierstrassZeta_add_lattice` | lemma | 144 | 7 |  |
| `om_injective` | lemma | 151 | 18 | **shared → H1** |
| `notLat_of_not_dvd` | lemma | 169 | 14 |  |
| `eisensteinG1_add` | theorem | 183 | 22 |  |
| `solution` | theorem | 205 | 8 |  |

#### WZD — pin `P2M/Sol/S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean` (532 lines, 37 declarations)

| decl | kind | line | lines to next | note |
|---|---|---:|---:|---|
| `cot_neg` | lemma | 20 | 3 | **shared → H1** |
| `norm_cexp_two_pi_I` | lemma | 23 | 5 | **shared → H1** |
| `pi_cot_add_eq` | lemma | 28 | 12 | **shared → H1** |
| `norm_pi_cot_add_le` | lemma | 40 | 22 | **shared → H1** |
| `norm_pi_cot_sub_le` | lemma | 62 | 9 | **shared → H1** |
| `hasSum_pi_cot_add` | lemma | 71 | 19 |  |
| `om` | def | 90 | 2 | **shared → H1** |
| `NotLat` | def | 92 | 2 | **shared → H1** |
| `om_injective` | lemma | 94 | 18 | **shared → H1** |
| `notLat_of_not_dvd` | lemma | 112 | 14 |  |
| `pval` | def | 126 | 2 | **shared → H1** |
| `ser` | def | 128 | 3 | **shared → H1** |
| `hasSum_ser` | lemma | 131 | 3 | not in H1 — port in S1 (after WZA) |
| `eisensteinG1_eq` | lemma | 134 | 11 |  |
| `dvd_of_dvd_reduce` | lemma | 145 | 8 |  |
| `exists_reduce` | lemma | 153 | 19 |  |
| `rho` | def | 172 | 2 |  |
| `rho_nonneg` | lemma | 174 | 2 |  |
| `rho_lt_one` | lemma | 176 | 3 |  |
| `Kof` | def | 179 | 2 |  |
| `Kof_pos` | lemma | 181 | 3 |  |
| `norm_ser_le` | lemma | 184 | 62 |  |
| `norm_pval_le` | lemma | 246 | 8 |  |
| `norm_pi_cot_le_of_im` | lemma | 254 | 23 |  |
| `isBoundedAtImInfty_eisensteinG1` | theorem | 277 | 53 |  |
| `Fterm` | def | 330 | 4 |  |
| `norm_cexp_real` | lemma | 334 | 12 |  |
| `summable_Fterm` | lemma | 346 | 17 |  |
| `hasSum_Fterm_row` | lemma | 363 | 38 |  |
| `tsum_Fterm_eq_pval` | lemma | 401 | 13 |  |
| `coef` | def | 414 | 3 |  |
| `tsum_regroup` | lemma | 417 | 21 |  |
| `summable_regroup` | lemma | 438 | 19 |  |
| `hasSum_regroup` | lemma | 457 | 5 |  |
| `coef_eq` | lemma | 462 | 9 |  |
| `hasSum_eisensteinG1` | theorem | 471 | 50 |  |
| `solution` | theorem | 521 | 12 |  |

#### W1 — pin `P2M/Sol/S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean` (703 lines, 58 declarations)

| decl | kind | line | lines to next | note |
|---|---|---:|---:|---|
| `three_le` | lemma | 23 | 11 |  |
| `factorsThrough_inv` | lemma | 34 | 5 |  |
| `conductor_inv` | lemma | 39 | 10 |  |
| `isPrimitive_inv` | lemma | 49 | 4 |  |
| `ψL` | abbrev | 53 | 2 |  |
| `gs` | def | 55 | 2 |  |
| `sum_inv_mul_psi` | lemma | 57 | 8 |  |
| `gaussSum_ne_zero_of_isPrimitive` | lemma | 65 | 13 |  |
| `gs_ne_zero` | lemma | 78 | 3 |  |
| `inv_ne_one` | lemma | 81 | 7 |  |
| `sum_inv_eq_zero` | lemma | 88 | 3 |  |
| `chi_neg` | lemma | 91 | 5 |  |
| `inv_mul_unit` | lemma | 96 | 7 |  |
| `sum_mul_pow_eq` | lemma | 103 | 23 |  |
| `pi_cot_eq_sum` | lemma | 126 | 55 |  |
| `vb` | def | 181 | 2 |  |
| `E0` | def | 183 | 4 |  |
| `vb_not_dvd` | lemma | 187 | 7 |  |
| `inv_zero_eq` | lemma | 194 | 5 |  |
| `isUnit_entry` | lemma | 199 | 11 |  |
| `vb_vecMul_eq` | lemma | 210 | 27 |  |
| `E0_smul` | theorem | 237 | 30 |  |
| `denom_eq` | lemma | 267 | 6 |  |
| `E0SIF` | def | 273 | 14 |  |
| `E0SIF_apply` | lemma | 287 | 2 |  |
| `coe_E0SIF` | lemma | 289 | 4 |  |
| `E0_slash` | lemma | 293 | 12 |  |
| `not_dvd_vecMul` | lemma | 305 | 13 |  |
| `isBoundedAtImInfty_E0_slash` | theorem | 318 | 30 |  |
| `cb` | def | 348 | 5 |  |
| `hasSum_G` | lemma | 353 | 9 |  |
| `A` | def | 362 | 2 |  |
| `hasSum_E0` | theorem | 364 | 16 |  |
| `cexp_eq_psi` | lemma | 380 | 19 |  |
| `cst` | def | 399 | 2 |  |
| `cst_ne_zero` | lemma | 401 | 5 |  |
| `A_of_ne_zero` | theorem | 406 | 20 |  |
| `A_zero` | theorem | 426 | 43 |  |
| `norm_cb_le` | lemma | 469 | 31 |  |
| `K0` | def | 500 | 2 |  |
| `norm_A_le` | lemma | 502 | 16 |  |
| `differentiableOn_qseries` | lemma | 518 | 31 |  |
| `E0_mdifferentiable` | theorem | 549 | 25 |  |
| `E1` | def | 574 | 4 |  |
| `E1_smul` | lemma | 578 | 6 |  |
| `E1_slash` | lemma | 584 | 7 |  |
| `E1SIF` | def | 591 | 14 |  |
| `E1_mdifferentiable` | theorem | 605 | 3 |  |
| `isBoundedAtImInfty_E1_slash` | theorem | 608 | 5 |  |
| `E1MF` | def | 613 | 9 |  |
| `E1MF_apply` | lemma | 622 | 2 |  |
| `coe_E1MF` | lemma | 624 | 2 |  |
| `T_mem_Gamma1` | lemma | 626 | 4 |  |
| `periodic_E1MF` | lemma | 630 | 20 |  |
| `hasSum_E1` | theorem | 650 | 8 |  |
| `qExpansion_coeff_E1MF` | theorem | 658 | 9 |  |
| `main` | theorem | 667 | 26 |  |
| `solution` | theorem | 693 | 11 |  |
