# WORKORDER MS-1 — the Fricke pull-back on the base-changed `X_H` field and its Galois twist

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U1, §2, §3, §4. **Story**: U1.
**Silo**: 1,176. **Net**: ≈1,008 — the set's largest single row.
**Home**: **new** `lean/FLTForHuman/ModularCurve/XH/FrickeGalois.lean`.

Imports (verified: the union's closure contains every module the row's statement and proof name):

```lean
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularCurve.XH.FrickeSlash
```

## The declaration

Wrapper `Theorems/Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.lean`,
verbatim:

```
theorem ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ∀ d : (ZMod M)ˣ, ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H, ModularCurve.IsDiamondAutHBar M H d σ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar M H,
      (∀ (x : ModularCurve.xHFunctionFieldBar M H) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
          ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
          ModularCurve.coeffMap ι ((w x : ModularCurve.xHFunctionFieldBar M H) :
                LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : ModularCurve.xHFunctionFieldBar M H,
            w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
              ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
                ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))
```

## The pin proof

`P2M/Sol/S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.lean`,
1,176 lines / 125 declarations, in `namespace P2MW.S_…` then `namespace A2FRE`. Thirteen sections;
transcribe in order, one module section per pin section:

| section | pin lines | content |
|---|---|---|
| `Groups` | 19–131 | `one_mem_strictPeriods_of_T_mem`, `frickeGL`/`val_frickeGL`/`det_frickeGL`/`det_frickeGL_pos`/`eq_frickeGL`, `mapGL_eq_coe`, `frickeGL_mul_mul_inv`, `le_conj_frickeGL`; `frickeForm`/`coe_frickeForm`; `scalarGL`/`val_scalarGL`/`det_scalarGL`/`scalarGL_smul`/`slash_scalarGL`; `frickeGL_mul_frickeGL`, `frickeSqConst`(+`_ne_zero`), `slash_frickeGL_frickeGL` |
| `QExp` | 133–279 | the `qC` block: `qC`, `qC_mul`/`_add`/`_smul`, `qC_eq_zero_iff`, `qC_zero`/`_one`, `coe_smul_form`, `qC_const_mul`, `mul_eq_mul_of_qC`, `intSeriesC_add'` |
| `Coeff` | 281–315 | `mul_mem_ratios`, `add_mem_ratios`, `inv_mem_ratios`, `isIntegralQExp_const`, `algebraMap_mem_ratios`, `ratioField`, `mem_ratios_of_mem` |
| `Spec` | 317–360 | `coeffMap_injective`, `_root_.A2FRE.coeffMap_coeffEmb`, `coeffMap_intSeriesC`, `coeffMap_coeffEmb_intSeriesC`, `coeffMap_C`, `LBC` |
| `Rep` | 362–408 | `gen`/`coe_gen`, `qC_ne_zero_of_witness`, `gen_rep`, `algHom_ext_gen`, `rep_add`/`rep_mul`/`rep_inv`, `qC_const`, `qC_one_form` |
| `Diamond` | 410–588 | `cross_mul_eq`, `le_conj_gamma0`, `slashForm`/`coe_slashForm`/`coe_slashForm_mul`/`slashForm_ne_zero`, the `DiaP` block (`DiaP.apply_rep`, `.add`, `.mul`, `.zero`, `.inv`, `diaP_algebraMap`, `diaP_gen`, `diaP_all`), `frickeForm_ne_zero`, `qC_frickeForm_ne_zero`, `exists_gamma0_upperLeft`, `pow_eq_pow_mod`, `invExp`/`natCast_invExp`/`mul_invExp_mod`, `symm_apply_eq_pow`, `res1`, `coeffMap_ofPowerSeries`, `qCHom` |
| `LawTwo` | 590–625 | `exists_rep_slash_frickeGL`, `qW`/`qW_def`/`qW_eq_qC_frickeForm`, `coe_mul_slash_frickeGL`, `qW_mul`/`qW_add`/`qW_zero`/`qW_ne_zero` |
| `Cyclo` | 627–659 | `frickeOneConst`, `const_slash_frickeGL`, `qW_const`, `qW_one`, `specW_add`, `specW_mul`, `qW_cross` |
| `Span` | 661–721 | `FrP` block (`FrP.apply_rep`, `.add`, `.mul`, `.zero`, `.inv`, `frP_algebraMap`, `frP_gen`, `frP_all`), `exists_transport`, `wfun_spec`, `wfun_unique`, `exists_rep`, `wfun_add`/`_mul`/`_algebraMap` |
| `FrickeQ` | 723–924 | `wAlg`, `wAlg_comp_wAlg`, `wAlg_wAlg`, `wEquiv`, `wEquiv_frickeSpec`, `exists_series_slash_frickeGL` |
| `Construction` | 926–1032 | the `w` construction from `wEquiv`/`exists_series_slash_frickeGL` |
| `GaloisLaw` | 1034–1141 | `galois_gen`, `conjAlgHom`(+`_apply`), `galois_law` |
| head | 1143–1148 | `solution` (the headline) |

## Vocabulary (all ported — import, never re-derive)

- `ModularCurve.xHFunctionFieldBar` — `XH/FunctionField.lean` (reached through `XH/Operators`).
- `ModularCurve.IsDiamondAutHBar`, `diamondAutHBar`, `diamondHBar` — `XH/Operators.lean`.
- `ModularCurve.arithmeticGalois` — `Defs/ArithmeticGalois.lean`.
- `ModularCurve.coeffMap`, `laurentBaseChange` — `Defs/Laurent.lean`.
- `ModularCurve.IsIntegralQExp`, `intSeriesC`, `intFormRatiosC` — `X1/Integral.lean`,
  `JqIntegralRatios.lean`.
- `CohCarrier.GammaH` — `ModularForms/Defs/GammaH.lean`; `frickeMat`/`frickeEquiv`/`frickeH1` —
  `ModularForms/CohCarrier/Fricke.lean`.
- `ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` — `XH/FrickeSlash.lean`
  (the same module that hosts this row's home's sibling).
- `ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0` —
  `ModularForms/FrickeReciprocity.lean` (in `XH/FrickeSlash`'s closure).
- `HahnSeries.ofPowerSeries`, `UpperHalfPlane.qExpansion`, `ZMod.unitOfCoprime` — mathlib.

## Traps

1. **`frickeGL`**: use the public `ALTraceIdentity.frickeGL M (NeZero.ne M)`
   (`ModularForms/HeckeFrickeTrace.lean:44`, in the closure). `XH/FrickeSlash.lean:91` holds the
   same object `private`; it is not importable and must not be copied. The pin declares
   `frickeGL` per-`S_`-file (`P2MW.S_…`), so there is no pin node at `ModularCurve.frickeGL` and
   no public obligation — only the dedup rule.
2. **`A2FRE` is the pin's inner namespace, not a port namespace.** Its `coeffMap_*` lemmas are the
   port's `ModularCurve.coeffMap` API (`Defs/Laurent.lean`, `X1/CoeffMap.lean`): import, do not
   re-prove. Keep whatever local engine you do need in one inner namespace and do not export it.
3. Never transcribe `p2m_open`/`p2m_export`/`p2m_reactivate`, the `P2MW.S_` namespace, or any
   `attribute [-simp]`/`attribute [-instance]` prelude.
4. **The second conjunct is the Galois *twist***: `w` intertwines `arithmeticGalois … σ` with
   `diamondAutHBar M H (ZMod.unitOfCoprime c hc)`. Keep `ZMod.unitOfCoprime c hc` and the
   `σ ζ = ζ ^ c` hypothesis; do not replace the diamond index by `c` or by a product.
5. `hW` is a *matrix* equality on `W : GL (Fin 2) ℝ`; the pin's `eq_frickeGL` is the route from
   `hW` to `W = frickeGL M`. Do not re-derive `det`-positivity by hand if `det_frickeGL_pos` (the
   pin's, transcribed) does it.
6. Keep the pin's private/public split: the wire has **one** statement, so the 124 helpers stay
   `private` (record the split in the header, as `SiegelUnit/Basic.lean` did). The surface gate
   (recipe §5) is the reviewer's, not yours.
7. The pin sets no `maxHeartbeats` on this file. If a declaration will not fit at the 200k edit
   cap, that is an inference symptom — diagnose (`set_option trace.Meta.synthInstance true` on
   that one declaration), never add `set_option maxHeartbeats`.
8. `port_advise` prices 146 of the 1,154 declaration lines as already in the port; the three
   largest are the `mem_ratios`/`coeffMap` block. Check each against the port before writing
   (FR-0069: a shape-tier match is not an import).

## Gates

1. Edit loop: `cd lean && timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
   FLTForHuman/ModularCurve/XH/FrickeGalois.lean` → silent, zero warnings.
2. `flock tmp/lean-build.lock timeout 90 lake build FLTForHuman.ModularCurve.XH.FrickeGalois` →
   success (serialize; other agents share the lock).
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/XH/FrickeGalois.lean` → the
   headline `ok`, **0 mismatch / 0 missing**.
4. `#print axioms ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul`
   → `[propext, Classical.choice, Quot.sound]`.
5. Exactly **two** `spec-pin:` lines: the `Thm_` wrapper and its `S_` copy.
6. `cd tools/deps && python3 dedup.py --targets <module-stem> --within --tier shape` (dry run, report only; `move_dead.py` is optional here).
7. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression, no other
   file touched, no git, no tree build; every command under 2 minutes.
8. Report: declarations added (public/private), lines, checker line, axioms, build result, and
   every deviation from this brief.
