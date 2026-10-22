# WORKORDER-RI2 — the Hecke-compositum degree: one body, two headlines

Port the twin pair

* `ModularCurve.relfinrank_xHHeckeCompositum_eq_mul`
  (`P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean`, 994 pin lines, 75
  declarations) — **the body**;
* `ModularCurve.relfinrank_x1HeckeCompositum_eq_mul`
  (`P2M/Sol/S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean`, 884 pin lines, 70) — **not a
  body: a corollary**, see §1.

The manager has done the shared ground (§2) and it is green and frozen. Do not edit it, do not
re-open it, and **do not transcribe the `x1` file**.

Planning record: [TOPIC-hecke-compositum.md](TOPIC-hecke-compositum.md). Methods:
[../TOPIC-dedup-refactoring.md](../TOPIC-dedup-refactoring.md). Pin `aa2d8b3`:
[`xH` `S_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean),
[`xH` `Thm_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean),
[`x1` `S_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean),
[`x1` `Thm_`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean).

## 1. What to deliver

> **Addendum (as landed).** The body was delivered as `ModularCurve/XH/HeckeCompositum.lean` and
> then moved to **`ModularCurve/HeckeCompositum.lean`**, which now carries **both** headlines: the
> `x1` corollary was first written as its own six-line module, then as an append to
> `X1/FunctionFieldDegree.lean`; both were rejected (a module for a façade; and the import edge
> perturbs an unrelated proof there). The corollary lives at the bottom of the same module, and the
> module is named for the subject rather than for one level. Everything below about the body still
> holds; only the path and the second headline changed.

`lean/FLTForHuman/ModularCurve/XH/HeckeCompositum.lean` — **one public declaration**, in
`namespace ModularCurve`, at the wrapper's name and statement:

```lean
theorem ModularCurve.relfinrank_xHHeckeCompositum_eq_mul
    (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))
```

(copy it from the wrapper, do not retype it). Everything else `private`. The module carries

```
spec-pin: Theorems/Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean
```

**Why the `x1` file is not transcribed.** Its headline is this theorem at `H := ⊥`:
`CohCarrier.GammaH M ⊥ = Gamma1 M` is the ported `GammaH_bot`
(`ModularForms/Defs/GammaH.lean:137`), and the three field objects follow by `rfl`
(`xHFunctionFieldC K M ⊥ = x1FunctionFieldC K M`, and the same for the `Top`/`x0` pair). The
manager writes the `x1` façade — fifteen lines — from your module after it is green. So the
`x1` file is a *cross-check for your reading*, not a source: whenever the two pin files differ,
the difference is the group (`CohCarrier.GammaH M H` ↝ `Gamma1 M`) and nothing else.

## 2. The frozen ground — built, green, not to be edited

This round **handed four legacy modules over to their own `spec-pin:` wires** (their `PORT_FILES`
entries are gone) and extended each with the block the pin writes for this node:

| module | new declarations | checker |
|---|---|---|
| `ModularCurve/Defs/Laurent.lean` | `qExpAlg`, `qExpAlg_apply`, `coe_qExpAlg`, `adjoin_qExpand_image`, `charZero_of_algebraRat`, `coeffEmb_apply`, `powerSeries_map_map` | **45 ok / 0 / 0** |
| `ModularCurve/JqIntegralRatios.lean` | `map_ofPowerSeries`, `coeffEmb_intSeriesC`, `intSeriesC_eq_zero_iff`, `coeffEmb_image_intFormRatiosC` | **27 ok / 0 / 0** |
| `ModularCurve/Degree/LaurentGlue.lean` | `laurentBaseChange_map`, `laurentBaseChange_sup`, `laurentBaseChange_qExpFunctionFieldC` | **11 ok / 0 / 0** |
| `ModularCurve/Degree/Relfinrank.lean` | `RelFinrankKit.{finite_extendScalars_of_relfinrank_ne_zero, relfinrank_sup_le, isIntegral_and_natDegree_minpoly_le, finrank_adjoin_simple_le_of_le, relrank_adjoin_insert_eq, isIntegral_and_finrank_adjoin_le_relfinrank, relfinrank_le_of_relrank_le, relfinrank_adjoin_simple_eq_finrank, transcendental_map, transcendental_coe}` and `relfinrank_laurentBaseChange_eq` | **14 ok / 0 / 0** |

`RelFinrankKit` and the base-change transport are stated at the pin's names in `namespace
ModularCurve` (`RelFinrankKit` for the ten), so `open ModularCurve.RelFinrankKit` gives the pin's
call sites verbatim.

## 3. Reuse map — import, never re-prove

| pin declaration(s) | call |
|---|---|
| `anSet` | `ModularCurve.RelIndex.ratioSet` (definitionally the same set) |
| `AA` | `abbrev AA (Γ) := IntermediateField.adjoin ℂ (RelIndex.ratioSet Γ)` — one line here |
| `FF` | `qExpFunctionFieldC` (already ported) |
| `qExpAlg`, `adjoin_qExpand_image`, `charZero_of_algebraRat`, `coeffEmb_apply`, `powerSeries_map_map`, `map_ofPowerSeries`, `coeffEmb_intSeriesC`, `intSeriesC_eq_zero_iff`, `coeffEmb_image_intFormRatiosC`, `laurentBaseChange_map`, `laurentBaseChange_sup`, `laurentBaseChange_qExpFunctionFieldC` | ground (§2) |
| the whole `XHLDField` block and `relfinrank_laurentBaseChange_eq` | `ModularCurve.RelFinrankKit.*`, `ModularCurve.relfinrank_laurentBaseChange_eq` |
| `relfinrank_mul_relfinrank`, `relfinrank_map_map`, `relfinrank_eq_finrank_of_le`, `extendScalars_*` | mathlib (`FieldTheory/Relrank`, `IntermediateField/Adjoin/Algebra`) |
| `conj_hyp_GammaH` | `ModularCurve.DiamondLift.XH.cocycle` (`ModularCurve/XH/DiamondLift.lean:70`) — the same statement with `ℓ` for `t` |
| `T_mem_GammaH`, `T_mem_infH`, `Gamma0_mul_inf_Gamma0_mul`, `Gamma0_le_of_dvd`, `mem_Gamma0_iff_dvd`, `T_zpow_mem_Gamma1`, `T_mem_Gamma1` | check first: `CongruenceSubgroup.{Gamma0_le_of_dvd,...}`, `ModularForm.Level.T_mem_Gamma1`, `CuspForm.PetHeckeAdj.T_zpow_mem_Gamma1`, `CohCarrier.translation_mem_GammaH`; a two-line local `private` copy is acceptable where the binder shape fights |
| `Gamma1_le_of_dvd`, `Gamma1_in_Gamma0` | already ported |
| `qExpansion_div_mem_laurentBaseChange_xHFunctionField` | `ModularCurve/X1/QExpansionDiv.lean` |
| `x1FunctionFieldC_le_x1x0`, `xHFunctionFieldC_le_top`, `qExpFunctionFieldC_mono` | `X1/Defs.lean`, `XH/FunctionField.lean` |
| **`relIndex_gamma0_le_relrank_adjoin_insert_jqNModC`**, **`relrank_adjoin_qExpansion_div_le_relIndex`** | **`ModularCurve/RelIndex/LeRelrank.lean` and `LeRelIndex.lean` — the two headlines landed last set. They are this node's engine: `main_C` calls both.** |
| `jqNModC`, `qExpand_qExpand`, `laurentBaseChange`, `qExpansion_{mul,add}`, `ModularForm.norm` | ported / mathlib |

## 4. What to write

| pin section | lines | what |
|---|---:|---|
| `XHLDGroups` remainder | 27–112 | `Gamma0_mul_inf_Gamma0_mul`, `exists_isCoprime_add_mul`, `exists_mul_eq_of_mem_Gamma1`, `relIndex_le_relIndex_inf`, `exists_delta`, `exists_mul_eq_of_mem_GammaH`, `relIndex_le_relIndex_infH` (the `Γ₁` ones are needed by the `Γ_H` proofs; transcribe both, they are one development) |
| `FF` layer | 635–752 | `AA_GammaH_eq` (uses `laurentBaseChange_qExpFunctionFieldC` from the ground + `qExpansion_div_mem_laurentBaseChange_xHFunctionField`), `FF_le_AA`, `jqNModC_mem_FF`, `map_FF_GammaH_le` |
| `Fields` | 753–779 | the five `abbrev`s (`GA`, `GB`, `QQ`, `BP`, `roof`) and the four `⊆` lemmas |
| `OverC` | 782–877 | `theta_mem_BP`, `Gamma0_inf_GA`, `relIndex_GB_le`, `relIndex_GB_ne_zero`, `relfinrank_FF1_FFB_le`, `main_C` |
| `BaseChange` | 881–954 | `FF_eq_bc`, `QQ_eq_bc`, … , `main_L` |
| `solution` | 962–992 | the headline: a `change` to the `Fields` abbreviations + `main_L` |

`main_C` is the heart: it invokes
`ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (GA M H ℓ) (T_mem_infH …) (ℓ * (M * ℓ'))`
and `ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex …` and sandwiches them with the tower
law. Both are already proved; do not re-derive either bound.

## 5. Traps

* `anSet`/`AA` — use `RelIndex.ratioSet`; the pin's `AA` is `adjoin ℂ (anSet Γ)` and
  `AA_GammaH_eq` is the identity `adjoin ℂ (ratioSet Γ_H) = qExpFunctionFieldC ℂ Γ_H`.
* `conj_hyp_GammaH` is `DiamondLift.XH.cocycle`; `conj_hyp_top` is not needed by the `xH` file.
* the `x1` file proves `exists_mul_eq_of_mem_Gamma1`/`relIndex_le_relIndex_inf` in a `Γ₁` form and
  the `xH` file the `Γ_H` form; both are needed here, and the `Γ₁` ones are *not* derivable from
  the `Γ_H` ones without `H := ⊥` — transcribe them.
* `qExpansion 1 (⇑f)` vs `qExpansion 1 (f : ℍ → ℂ)`: the checker's `norm` handles the spelling,
  but keep the pin's in statements.
* the pin's `p2m_open`/`p2m_reactivate`/`attribute`/`set_option linter.unusedSectionVars` are not
  carried; `import Mathlib` is not carried (targeted imports only). If a section variable is
  unused, use an explicit binder or `omit`.
* zero warnings: `if_pos`/`if_neg` are deprecated (`ite_eq_left`/`ite_right`), `haveI` → `have`
  where the linter complains.

## 6. Gates

1. `cd lean && lake env lean FLTForHuman/ModularCurve/XH/HeckeCompositum.lean` — silent, 0 warnings.
2. `lake build FLTForHuman.ModularCurve.XH.HeckeCompositum` (single module; no wave).
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/XH/HeckeCompositum.lean` →
   `1 ok / 0 mismatch / 0 missing / 0 own / 0 kw`.
4. `#print axioms ModularCurve.relfinrank_xHHeckeCompositum_eq_mul` →
   `[propext, Classical.choice, Quot.sound]`.

Report: module path, lines, declaration counts, the four gate readings verbatim, every deviation
(one line each), every local helper you wrote instead of a ground declaration.
