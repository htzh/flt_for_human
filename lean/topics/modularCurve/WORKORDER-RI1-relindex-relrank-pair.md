# WORKORDER-RI1 — the degeneracy-cover degree: the two `RelIndex` bodies

Port the pair

* `ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC`
  (`P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean`, 1,214 pin
  lines, 161 declarations);
* `ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex`
  (`P2M/Sol/S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean`, 545 pin lines,
  63 declarations)

as **two modules, one public declaration each**.

The manager has already done the shared ground (§2) and it is green and frozen. Do not
re-open it, do not edit `JqIntegralRatios.lean`, and do not edit the four ground modules.
Planning record and the dedup reasoning: [TOPIC-relIndex-relrank.md](TOPIC-relIndex-relrank.md);
the methods note: [../TOPIC-dedup-refactoring.md](../TOPIC-dedup-refactoring.md).

Pin `aa2d8b3`:
[`RelIndex` `S_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean),
[`RelIndex` `Thm_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean),
[`RelrankNorm` `S_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean),
[`RelrankNorm` `Thm_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean).

## 1. What to deliver

**Body A** — `lean/FLTForHuman/ModularCurve/RelIndex/LeRelrank.lean`

One public declaration, in `namespace ModularCurve`, at the wrapper's name and statement:

```lean
theorem ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (N : ℕ) [NeZero N] :
    (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
      IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N)
          {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}))
```

**Body B** — `lean/FLTForHuman/ModularCurve/RelIndex/LeRelIndex.lean`

One public declaration, in `namespace ModularCurve`:

```lean
theorem ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex
    (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hind : Γ'.relIndex Γ ≠ 0) :
    IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}) ≤
      (Γ'.relIndex Γ : Cardinal)
```

Everything else in both modules is `private`, at the pin's own signatures and names. Both
modules carry a `spec-pin:` header naming their `S_` and `Thm_` files:

```
spec-pin: Theorems/Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
spec-pin: P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
```

(the same pair for body B). **Do not** carry the pin's `attribute [-instance]` /
`attribute [-simp]` blocks, its `set_option linter.unusedSectionVars`, or its
`p2m_reactivate` lines.

Both stories are `change`-able to the ground's `ratioSet` — verified, see §4:

```lean
  change (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
    IntermediateField.relrank (IntermediateField.adjoin ℂ (RelIndex.ratioSet Γ))
      (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N) (RelIndex.ratioSet Γ)))
```

and for B

```lean
  change relrank (adjoin ℂ (RelIndex.ratioSet Γ)) (adjoin ℂ (RelIndex.ratioSet Γ')) ≤ _
```

## 2. The frozen ground — green, built, and not to be edited

`lake env lean` on each module is clean and `lake build` of each is in the oleans.

| module | namespace | what it holds |
|---|---|---|
| `FLTForHuman/ModularCurve/Analytic/AnalyticAtCusp.lean` | `ModularCurve` | `AnalyticAtCusp` (the pin's `Nice`/`An1`), `AnalyticAtCusp.{mul,add,pow,sum}`, `analyticAtCusp_one`, `analyticAtCusp_zero`, `qExpansion_pow'`, `qExpansion_sum'`, `analyticAtCusp_of_modularForm` |
| `FLTForHuman/ModularCurve/RelIndex/Hermite.lean` | `ModularCurve.RelIndex` | `dMul`, `det_dMul`, `dMul_eq`, `exists_hermite`, `hδ`, `hA`, `hB`, `hD`, `hermite_spec`, `hA_pos`, `hB_nonneg`, `hB_lt`, `hD_pos`, `hA_mul_hD`, `dMul_eq_hermite`, `nA`, `nB`, `nD`, `nA_cast`, `nB_cast`, `nD_cast`, `nA_ne_zero`, `nD_ne_zero`, `nB_lt_nD`, `nA_mul_nD`, `mul_inv_mem_Gamma0_of_hermite_eq` |
| `FLTForHuman/ModularCurve/RelIndex/LevelRaise.lean` | `ModularCurve.RelIndex` | `one_mem_strictPeriods`, `natCast_mem_strictPeriods`, `hP`, `val_hP`, `heckeDiag_mul_eq`, `heckeDiag_smul_smul`, `coe_upperRightHom_smul`, `coe_hP_smul`, `hP_smul_heckeDiag_smul`, `one_mem_strictPeriods_conj`, `heckeDiag_conj_upperRightHom`, `one_mem_strictPeriods_conjDiag`, `raise`, `raise_apply`, `coe_raise`, `coeff_qExpansion_raise`, `Ux`, `twist`, `twist_apply`, `coe_twist`, `one_mem_strictPeriods_twist`, `qParam_Ux_smul`, `coeff_qExpansion_twist`, `expU`, `val_expU`, `twRaiseFn`, `twRaiseFn_eq` |
| `FLTForHuman/ModularCurve/RelIndex/RatioField.lean` | `ModularCurve.RelIndex` | `qC_ne_zero_iff`, `ratioSet`, `mem_ratioSet`, `ratioSet_mono`, `qC_mul`, `qC_coe_mul`, `qC_add`, `qC_neg`, `qExpansion_const`, `qC_const`, `mul_mem_ratioSet`, `add_mem_ratioSet`, `neg_mem_ratioSet`, `inv_mem_ratioSet`, `algebraMap_laurentSeries_eq_C`, `algebraMap_mem_ratioSet`, `ratioField`, `mem_ratioSet_of_mem_adjoin`, `common_denominator`, `coe_finset_sum`, `qC_eq_qExpand_of_coeff`, `qC_raise`, `qC_twist`, `qC_twRaiseFn` |
| `FLTForHuman/ModularCurve/JqIntegralRatios.lean` | `ModularCurve` | **promoted** (public now): `e4cube`, `delta`, `isIntegralQExp_e4cube`, `coe_delta`, `isIntegralQExp_delta`, `intSeriesC_delta_ne_zero`, `jqModC_mul_delta`, `jqModC_eq_div` — the ℂ-`jqModC` block, at general `Γ` and general field `K`. The module is now **wired by its own `spec-pin:` lines** (its `PORT_FILES` entry is gone); `spec/check_port.py` reads it 23 ok / 0 mismatch |

Beware the binder shapes: the ground takes `hT : ModularGroup.T ∈ Γ` as an **explicit**
argument (`qC_mul hT …`, `raise_apply t f τ`, …), and `raise`/`qC_raise`/`twist` are general in
the subgroup (`Γg : Subgroup (GL (Fin 2) ℝ)`), not in `SL(2, ℤ)`.

The ground's `qC` is `ModularCurve.DiamondLift.qC` — body A and B both want
`open ModularCurve.DiamondLift (qC)` (or fully qualify).

## 3. Reuse map — import, never re-prove

| pin declaration(s) | call |
|---|---|
| `qC` | `DiamondLift.qC` |
| `restrictForm`, `coe_restrictForm` | `ModularCurve.restrictForm`, `ModularCurve.coe_restrictForm` (`JqIntegralRatios.lean:43`) |
| `isIntegralQExp_E4` | `ModularCurve.isIntegralQExp_E4` |
| `AF`/`e4cube`, `DF`/`delta`, `isIntegralQExp_AF`, `coe_DF`, `isIntegralQExp_DF` | `ModularCurve.e4cube`, `ModularCurve.delta`, `ModularCurve.isIntegralQExp_e4cube`, `ModularCurve.coe_delta`, `ModularCurve.isIntegralQExp_delta`, instantiated at `Γ := ⊤`; write the pin's `AF`/`DF` as two-line `abbrev`s of them if the pin's names help the transcription |
| `jqModC_mul_delta`, `jqModC_eq_jC`, `XD_ne_zero` | `ModularCurve.jqModC_mul_delta`, `ModularCurve.jqModC_eq_div` (+ `intSeriesC_delta_ne_zero`) |
| `one_mem_strictPeriods`, `hSL1`, `natCast_mem_strictPeriods`, `one_mem_strictPeriods_{conj,conjDiag,twist}` | `RelIndex.*` (ground) |
| `An1`, `An1.{one,zero,add,mul,pow,sum}`, `An1.of_form`, `qExpansion_{pow,sum}'`, `cuspFunction_{one,zero}'` | `ModularCurve.AnalyticAtCusp` and its API; `cuspFunction_one'`/`cuspFunction_zero'` are mathlib-shaped — see §5 |
| `Nice`, `Nice.{mul,add,pow,sum}`, `nice_one`, `nice_zero`, `nice_of_GG`, `nice_of_HH` | the same ground (`analyticAtCusp_of_modularForm` covers the three "a form is nice" lemmas) |
| `S`, `SField`, `mem_S_iff`, `qC_ne_zero_iff`, `qC_mul`, `qC_add`, `qC_neg`, `mul_mem_S`, `add_mem_S`, `neg_mem_S`, `inv_mem_S`, `qC_const`, `algebraMap_mem_S`, `mem_S_of_mem`, `common_denominator` | `RelIndex.ratioSet`, `RelIndex.ratioField`, `RelIndex.mem_ratioSet`, `RelIndex.qC_*`, `RelIndex.*_mem_ratioSet`, `RelIndex.qC_const`, `RelIndex.algebraMap_mem_ratioSet`, `RelIndex.mem_ratioSet_of_mem_adjoin`, `RelIndex.common_denominator` |
| `ratioSet`, `ratioField`, `mem_ratioSet`, `ratioSet_mono`, `ratioSet_mono`, `mem_ratioSet_of_mem_adjoin`, `algebraMap_laurentSeries_eq_C` | the same |
| `coe_finset_sum` | `RelIndex.coe_finset_sum` (function form; the pointwise form is one `funext`) |
| `Q`, `card_Q`, `rep`, `rep_spec`, `rho_rep_injective`'s `Finite (Q Γ N)` | ground has none — see §4 |
| `dMul` … `mul_inv_mem_Gamma0_of_hermite_eq` | `RelIndex.*` (ground) |
| `raise`, `raise_apply`, `coe_raise`, `coeff_qExpansion_raise`, `qC_raise`, `twist`, `coe_twist`, `expU`, `twRaiseFn`, `qC_twist`, `qC_twRaiseFn`, `hP`, `heckeDiag_mul_eq`, `heckeDiag_smul_smul`, `coe_hP_smul`, `hP_smul_heckeDiag_smul`, `qParam_Ux_smul`, `coeff_qExpansion_twist` | `RelIndex.*` (ground) |
| `heckeDiagMatrix`, `val_heckeDiagMatrix`, `coe_heckeDiagMatrix_smul`, `slash_heckeDiagMatrix_apply`, `upperTriangularGL` | `ModularForm.*` in `ModularForms/Defs/HeckeOperator.lean` |
| `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` | `ModularForms/HeckeQCoeff.lean` |
| `qExpand`, `qExpand_coeff_mul`, `qExpand_coeff_of_not_dvd`, `qExpand_injective` | `ModularCurve.Defs/Laurent.lean` |
| `qTwist`, `qTwist_coeff` | `ModularCurve.Defs/Twist.lean` |
| `qExpansion_{mul,add,neg,one,zero,smul}`, `hasSum_qExpansion`, `qExpansion_coeff_unique`, `qExpansion_eq_zero_iff` | mathlib `UpperHalfPlane` / `ModularForm` |
| `SlashInvariantForm.slash_action_eqn_SL''` | mathlib, as used in `XH/Relrank.lean:698` |
| `ModularForm.norm`, `coe_norm`, `norm_ne_zero`, `SlashInvariantForm.quotientFunc` | mathlib `NumberTheory/ModularForms/NormTrace.lean` |
| `Lagrange.basis`, `Lagrange.interpolate`, `Lagrange.eq_interpolate` | mathlib `LinearAlgebra/Lagrange.lean` |
| `homogenize`, `homogenize_finsetProd` | mathlib `Algebra/Polynomial/Homogenize.lean` |
| `IntermediateField.exists_lt_finrank_of_infinite_dimensional`, `Field.exists_primitive_element`, `Polynomial.coeff_prod_of_natDegree_le` | mathlib; all four verified present at `v4.34.0` |

## 4. What to write — the two bodies

### Body A (`RelIndex/LeRelrank.lean`)

1. **`LevelOne`** (`S_` 25–120). After the reuse map this is: `SLtop` (already the pin's
   `abbrev`), `intSeriesC_eq_qC`, `XA`, `XD`, `jC`, `XD_ne_zero`, `jqModC_eq_jC`, `XA_ne_zero`,
   `jC_ne_zero`, `jC_coeff_neg_one`, `jC_coeff_of_lt` — all one-to-seven-line consequences of the
   promoted `jqModC_eq_div` and of `ModularCurve.coeff_jqModC_neg_one` /
   `coeff_jqModC_pow_of_lt`.
2. **`Groups` remainder** (`S_` 222–282) is in the ground; nothing to write except the two
   `abbrev`s `GamGL`/`Gam'GL` (`S_` 540–542) and `T_mem_inf`, `hΓ1`, `hΓ'1`, `gam'_le_conj`.
3. **`Core`** (`S_` 536–995): `conjMat`/`det_conjMat`/`conjSL`/`dvd_of_mem_Gamma0`/
   `heckeDiag_mul_mul_inv` are **not** in this set's ground — the port's copies live in
   `XH/HeckeInputs.lean` at level `ℓ` with an extra `hℓ : ℓ ≠ 0`. Import them and supply
   `NeZero.ne N`; if a binder shape resists, write the pin's two-line version `private` and
   say so in the record. Then: `LA`/`LD` (+`_apply`, `qC_LA`, `qC_LD`), `weight_eq`, the
   `termF`/`Phi` block, `rel_at_P`, `rel_twisted`, `RHom`/`rel_R`, `rho`, `rho_eq_div`,
   `rho_coeff_mul`, `rho_coeff_of_not_dvd`, `rho_coeff_neg_sq`, `nA_eq_of_rho_eq`,
   `expU_xOf_eq`, `mul_inv_mem_of_rho_eq`, `Q`, `card_Q`, `rep`, `rep_spec`,
   `rho_rep_injective`, `core`.
   * `Q Γ N` is `↥Γ ⧸ (Gamma0 N).subgroupOf Γ`; the pin's
     `scoped instance : Finite (Q Γ N) := Subgroup.finite_quotient_of_finiteIndex` works —
     `infer_instance` finds `((Gamma0 N).subgroupOf Γ).FiniteIndex` (verified).
   * `isRoot_of_rel`, `coeff_sum_C_mul_X_pow`, `natDegree_sum_le` are `private` here
     (mathlib's `Polynomial.natDegree_sum_le_of_forall_le` covers the last in one line).
4. **`Ratio`** (`S_` 997–1115) is in the ground, except the two spellings: use
   `ratioSet`/`ratioField`. `mem_S_iff`, `qC_ne_zero_iff`, `mem_S_of_mem`,
   `common_denominator` all exist.
5. **`Final` + headline** (`S_` 1117–1212): `jqNModC_eq`, `theta_mem`, `le_insert`,
   `linearIndependent_pow_theta`, then the headline's `change` and
   `IntermediateField.relrank_eq_rank_of_le` + `LinearIndependent.cardinal_le_rank`.

### Body B (`RelIndex/LeRelIndex.lean`)

1. **`Setup`** (`S_` 15–38): `HH`, `GG`, `Cos`, `relIndex_GG_HH`, `natCard_cos`,
   `isFiniteRelIndex`. `one_mem_strictPeriods` is ground.
2. **`Norm`** (`S_` 40–272): the `Cos`-indexed norm/characteristic-polynomial engine
   (`quotientFunc_smul_sub`, `norm_smul_sub_apply`, `charPolyAt`, `eval_charPolyAt`,
   `natDegree_linear_le`, `card_cos`, `natDegree_charPolyAt_le`, `coeff_charPolyAt_card`,
   `node`, `node_injOn`, `lag`, `charPolyAt_eq_sum`, `coeffForm`, `coeffForm_apply`,
   `coe_coeffForm_card`, `eval_homogenize_linear`, `eval_homogenize_eq_sum`,
   `sum_coeffForm_mul_pow_eq_zero`), the `Nice` block (**use the ground**
   `AnalyticAtCusp`), `nice_of_GG`/`nice_of_HH`, `sum_qExpansion_coeffForm_mul_pow_eq_zero`,
   `qExpansion_coeffForm_card_ne_zero`.
3. **`Ratio`** is ground, except `mem_ratioSet`, `ratioSet_mono`,
   `algebraMap_laurentSeries_eq_C` (ground too).
4. **`Degree`** (`S_` 393–456): `sum_div_pow_eq`, `exists_polynomial`.
5. **`Bound`** (`S_` 458–503): `finiteDimensional_of_forall_aeval_eq_zero`,
   `rank_le_of_forall_aeval_eq_zero`.
6. **headline** (`S_` 505–543).

## 5. Drifts and traps already known

* `An1`/`Nice` are **one** ground predicate, `AnalyticAtCusp`; the pin's two spellings do not
  both exist. `An1.of_form` (`hΓ` + a form) is `analyticAtCusp_of_modularForm`.
* `cuspFunction_one'`/`cuspFunction_zero'` (pin) are mathlib's
  `UpperHalfPlane.cuspFunction_one`-shaped facts; check mathlib first and do not re-prove them.
* `Nice.pow` in the pin is `∀ n, Nice (F ^ n)` (recursion on `n`), not `Nice (F ^ n)` for a
  given `n` — the ground follows the pin.
* the pin's `S`/`SField` and `ratioSet`/`ratioField` are one object here; both `mem_S_of_mem`
  and `mem_ratioSet_of_mem_adjoin` are `mem_ratioSet_of_mem_adjoin`.
* `common_denominator` in the ground takes `hT` **first** and returns `qC g ≠ 0` (not
  `qExpansion 1 g ≠ 0`): `qC_ne_zero_iff` converts.
* body A's `rho_rep_injective` and body B's `qExpansion_coeffForm_card_ne_zero` both need
  `one_mem_strictPeriods` at a *conjugated* subgroup — the ground's
  `one_mem_strictPeriods_conjDiag` / `one_mem_strictPeriods_twist` are for that.
* the pin's `attribute [-instance]`/`[-simp]` blocks are **not** carried, and neither is
  `set_option maxHeartbeats` (no module in this column carries one; if a proof resists, the
  build-cost note's probe ladder applies, not a bump).
* the pin's `ModularGroup.sl_moeb` is used inside the ground already; in the bodies prefer
  `ModularGroup.sl_moeb` (mathlib).

## 6. Gates

1. `lake env lean` clean on your module, **zero warnings** (`if_pos`/`if_neg` are deprecated:
   `ite_eq_left`/`ite_right`; `haveI` → `have` where the linter complains).
2. `lake build FLTForHuman.ModularCurve.RelIndex.LeRelrank` (resp. `LeRelIndex`) in the oleans.
3. `python3 spec/check_port.py --force lean/FLTForHuman/ModularCurve/RelIndex/LeRelrank.lean`
   → **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw**. If the headline reads `mismatch`, the
   statement is not the pin's — fix the statement, never the marker.
4. `#print axioms ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` must be
   `[propext, Classical.choice, Quot.sound]`.
5. Report: module path, lines, declaration count, the checker line, the build jobs/time, the
   axiom line, and every place you had to deviate from a mechanical transcription (with the
   reason). Do not touch the ground modules, `JqIntegralRatios.lean`, or any other module.
