# Topic m4 — the `Γ₀`-invariant core and the Fricke/inclusion headlines (M8)

**Status: work order drafted (pending the SET-M1 review).** First topic of
[SET-M2](SET-M2.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Three modules:

- `FLTForHuman/ModularCurve/Analytic/Gamma0InvariantCore.lean` — the pin's
  651-content-line prelude, written **once**.
- `FLTForHuman/ModularCurve/Analytic/FrickeInvariance.lean` — the three headline
  targets plus `fricke_transport`, `modularUnitSeries_mem_modularFunctionField(Full)`,
  `isIntegral_adjoin_jq_modularUnitSeries(_inv)`,
  `coe_frickeInvolutionFull_modularUnitSeries`.
- (If the core grows past ~900 lines, split the pure `RealL`/interpolation part
  into `Analytic/Interpolation.lean`; record the split.)

**Why this topic, and the dedup.** The three pin files

| file | raw | content |
|---|---|---|
| `S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant` | 870 | 656 |
| `S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant` | 870 | 656 |
| `S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant` | 1,155 | 913 |

share the block at lines 50–861 / 50–861 / 53–863. The first two differ by **12
lines** (all `p2m_*` namespace strings plus the final `solution`); the third's
prelude differs from the first's by **2 lines**. Content: **651 lines × 3**,
written once. Measured with:

```bash
cd ~/proj/fermats-last-theorem/P2M/Sol
diff S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant.lean \
     S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant.lean | grep -c '^[<>]'   # 12
diff <(sed -n '50,860p' S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant.lean) \
     <(sed -n '53,863p' S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean) | grep -c '^[<>]'  # 2
```

## 1. What goes in the core (the prelude), and what is imported

**Already ported — import, do not rewrite.** The pin's `RealL` block (lines
262–417) is `ModularForms/Hauptmodul.lean:230–`'s `RealL` + its closure
(`add`, `neg`, `sub`, `mul`, `single`, `C`, `one`, `zero`, `congr`, `prod`,
`coeff_prod_X_sub_C`). The port promoted it for exactly this reuse.

**Write in the core** (in rough dependency order; names verbatim):

`interpPoly`, `conjPoly` and their lemmas (`prod_erase_perm`, `interpPoly_map`,
`conjPoly_map`, `interpPoly_perm`, `conjPoly_perm`, `interpPoly_eval`,
`conjPoly_eval`, `conjPoly_monic`, `conjPoly_natDegree`, `eval_eq_sum_coeff`);
`slotH`, `liftPerm`, `coeffMap_qTwist`, `units_map_zeta_pow`, `coeffMap_slotH`,
`coeffMap_conj`, `zeta_pow_ell`, `zeta_mul_zeta_pow`, `qTwist_slotH`,
`qTwist_conj`, `interpK`, `conjK`, `exists_interpK_coeff_eq`,
`exists_conjK_coeff_eq`; the three missing `RealL` lemmas `RealL.sum`,
`RealL.interpPoly_coeff`, `RealL.conjPoly_coeff` (the port has the others);
`realL_one_of_realL_qExpand`, `realL_qExpand_of_realL_one`, `expRoot`,
`isPrimitiveRoot_expRoot`, `expRoot_pow_zpow`, `qParam_T_pow_smul`,
`realL_twist`; `jt`, `jtN`, `castC`, `coeffMap_sigma_coeffEmb`, `cosetRep`,
`slotF`, `slotJ`, `realL_fC`, `realL_gC`, `realL_slotH`, `coeffMap_conj_zero_eq`,
`realL_jqC`, `heckeDiag_smul_S_T_pow_smul`, `realL_conj`; `interpFun`,
`conjFun`, `jtN_smul`, `slots_smul`, `interpFun_smul`, `conjFun_smul`,
`mem_adjoin_of_interpK_coeff_eq`, `mem_adjoin_of_conjK_coeff_eq`; `iota`,
`iota_apply`, `coeffEmb_injective'`, `iota_injective`, `iota_eq_slotH_zero`,
`iota_jqN`; `dHat`, `dHat_ne_zero`, `exists_sum_eq_mul_dHat`; then the two
internal workhorses `mem_modularFunctionField_of_data`, `isIntegral_of_data`,
and `sigma`, `sigma_zeta`, `mem_modularFunctionField`, `isIntegral_adjoin_jq`.

**Seam/dedup notes.**
- `iota` is `(coeffEmb K).comp (qExpand ℚ ℓ)`; `iota_jqN` should dedup to the
  ported `Defs/TS.lean`/`Defs/Twist.lean` facts (`qExpand_TS`, `qTwist_TS`,
  `qExpand_qTwist_TS`) where they overlap. `iota_injective` may be the ported
  `Defs/Laurent.lean` `iota_injective` — check before writing.
- `RealL.conjPoly_coeff` / `RealL.interpPoly_coeff` sit on top of the ported
  `RealL.coeff_prod_X_sub_C`; write them, do not re-inline.
- Namespace: the pin puts the prelude in `ModularCurve.QExpN`. Match it (the
  checker's dotted fallback resolves the promoted names) or publish under
  `ModularCurve`; either way record the choice.

## 2. The headline targets (verbatim)

```lean
theorem ModularCurve.mem_modularFunctionField_of_hasSum_of_gamma0_invariant
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) :
    f ∈ ModularCurve.modularFunctionField ℓ

theorem ModularCurve.isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : …) (hG : …) (hinv : …) :
    IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) f

theorem ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : …) (hG : …) (hinv : …) (hf : f ∈ ModularCurve.modularFunctionFieldFull ℓ) :
    ((ModularCurve.frickeInvolutionFull ℓ ⟨f, hf⟩ : ModularCurve.modularFunctionFieldFull ℓ) :
      LaurentSeries ℚ) = g
```

The first two are the pin's *same 860-line development* with two different final
`solution` lines; the third adds `fricke_transport` and `coe_frickeInvolutionFull_modularUnitSeries`.

The small targets (verbatim):

```lean
theorem ModularCurve.modularUnitSeries_mem_modularFunctionField (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ
theorem ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull (N : ℕ) [NeZero N] :
    ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionFieldFull N
theorem ModularCurve.isIntegral_adjoin_jq_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ)
theorem ModularCurve.isIntegral_adjoin_jq_modularUnitSeries_inv (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ)⁻¹
theorem ModularCurve.coe_frickeInvolutionFull_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hmem : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionFieldFull ℓ) :
    ((ModularCurve.frickeInvolutionFull ℓ ⟨ModularCurve.modularUnitSeries ℓ, hmem⟩ :
      ModularCurve.modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = (ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹
```

## 3. The third file's distinctive block

`natDegree_interpPoly_lt`, `realL_jtN_S`, `realL_sum_qExpand_mul_jq_pow`,
`coeffMap_castC_injective`, `embW` (+ `embW_apply`, `embW_of_mem_adjoin`), and
the 137-content `fricke_transport` (the `IsFrickeAutFull` transport of the
`qParam`-invariant `f` to its `q ↦ q^ℓ` transform `g`). Then the headline.

**Risk.** `fricke_transport` is the topic's one hard block; build the core first,
then scout it in `Scratch.lean`.

## 4. Imports

`Analytic/ModularUnitQExpansion.lean` (m3), `Analytic/QParamUnique.lean` (m3),
`Analytic/Gamma0Cosets.lean` (m3), `Defs/ModularUnit.lean`, `Defs/AtkinLehner.lean`,
`Defs/{Jq,Laurent,TS,Twist,PhiGen}.lean`, `ModularForms/Hauptmodul.lean`
(`RealL`, `hasSum_qParam_mul_laurent`), `ModularForms/JqAnalyticModel.lean`
(`hasSum_jq_qParam`, `qExpansion_discriminant_...`), `ModularForms/HeckeQExpansion.lean`,
plus mathlib's `NumberTheory.ModularForms.{CongruenceSubgroups,Discriminant,EisensteinSeries.Basic}`,
`FieldTheory.Galois.Basic`, `GroupTheory.Perm.Fin`, `RingTheory.RootsOfUnity.Complex`.

## 5. Verification

- Append the three wrappers to `SOURCES`, the new modules to `PORT_FILES`. The
  pin `S_` files may also be appended for the promoted `QExpN` names.
- checker: 0 mismatched, 0 missing (identical ≥ 802).
- `#print axioms` on the three headlines + `fricke_transport`.
- Consumer Zone C `[analytic]`: the three headlines instantiated at `ℓ = 2` with
  concrete `f`/`g` (`modularUnitSeries 2`), and `frickeInvolutionFull` applied.
- `grep -c` each prelude name to show it occurs once.

## 6. Budget

**3 goal rounds.** Round 1: the core's interpolation/`RealL` half and
`mem_modularFunctionField_of_data`/`isIntegral_of_data`. Round 2: the core's
`iota`/`dHat`/`sigma` half, `fricke_transport`, the first two headlines. Round 3:
the third headline, the five small targets, log/README/consumer.

**Stop early on**: a `RealL` lemma the port lacks that belongs in
`Hauptmodul.lean` (prove it locally, record; do not edit that module); the
`fricke_transport` transport resisting the ported `IsFrickeAutFull` shape; or the
`QExpN` namespace colliding in the checker (report the collision).

## 7. Reporting back

1. Module/line/decl table and checker before/after.
2. **The dedup**: the 651-line prelude's single copy, the `diff` counts, and the
   line count of `Hauptmodul.RealL` reused.
3. `fricke_transport`'s route and where it bit.
4. Any `RealL`/interpolation lemma proved locally, with the reason it was not
   imported.
5. The SET-M3 hand-off (which declarations m5/m7/m9 import).
