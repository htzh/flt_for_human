# WORKORDER MS-5 — the complex-place dictionary: existence, the `Γ₀(M)` pull-back, and conjugation

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U3, §1, §2, §3, §4. **Story**: U3.
**Silo**: 1,773 (441 + 684 + 648). **Net**: ≈1,130 — the set's largest story by silo and its cheapest
per line.
**Home**: **new** `lean/FLTForHuman/ModularCurve/ComplexPlaceDictionaryAction.lean`.

Imports (verified: the union's closure contains every module the three rows name):

```lean
import FLTForHuman.ModularCurve.ComplexPlaceDictionaryOf
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.AlgebraicCurve.Place.ValueDictionary
import FLTForHuman.GaloisRep.Defs.ComplexConjugation
```

## The declarations (verbatim wrappers)

`Theorems/Thm_ModularCurve_exists_complexPlaceDictionaryOf.lean` (441):

```
theorem ModularCurve.exists_complexPlaceDictionaryOf (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ) :
    Nonempty (ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
```

`Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.lean` (684):

```
theorem ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hσ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0),
        ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
              ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))))
    (τ : UpperHalfPlane) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ)
```

`Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean` (648):

```
theorem ModularCurve.ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ) (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (τ : UpperHalfPlane) :
    ModularCurve.arithmeticGalois F₀ complexConjAlgEquiv • D.pt τ = D.pt (UpperHalfPlane.J • τ)
```

## The pin proofs — and the one engine they share

| row | pin file | lines / decls | namespace |
|---|---|---|---|
| 441 | `P2M/Sol/S_ModularCurve_exists_complexPlaceDictionaryOf.lean` | 441 / 48 | `ComplexPlaceDictionaryOfExistence` (section `OrderFunction`, 250–413) |
| 684 | `P2M/Sol/S_…_ofAlgAut_smul_pt_eq_pt_inv_smul.lean` | 684 / 59 | (the `CF`/`pres`/`mu` engine, then `gammaH_le_conj` → `slashForm` → `IsPullbackAlong` → `moeb` → `Key` → `mem_smul_place_iff` → `smul_pt_eq`) |
| 648 | `P2M/Sol/S_…_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean` | 648 / 62 | `ConjPlaceTransport` (sections `Presented` 249–294, `IntegralReal` 296–335, `Key` 337–569, `Place` 571+) |

**The shared engine (write it ONCE, publicly in the new module).** All three `S_` files re-prove the
same 19 declarations — the `qL`/`Pres`/`realize_*` block: `qL`, `Pres` (with `Pres.mul`, `Pres.add`,
`Pres.const`), `one_mem_strictPeriods`, `map_coe_nhdsNE`, `eventually_nhdsNE_coe_iff`,
`isBoundedUnder_nhdsNE_coe_iff`, `analyticAt_comp_ofComplex`, `coe_eq_zero_iff`, `eventually_ne_zero`,
`eventually_ne_zero_ofComplex`, `meromorphicOrderAt_comp_ofComplex_ne_top`, `qL_ne_zero`,
`realize_eventuallyEq`, `meromorphicAt_div`, `meromorphicAt_realize`, `meromorphicOrderAt_realize_eq`,
`qL_mul`, `qL_add`, `qL_const`, `mul_ne_zero_of_ne_zero`, `realize_*_eventuallyEq` (mul/add/const/
smul/neg/inv). Pin duplication: **511 lines** in the three files, of which **161** is the once-cost
(the rest is the same block re-spelled). This is the set's largest dedup win — do not write it twice.

## Vocabulary

- `ModularCurve.ComplexPlaceDictionaryOf` (+ `pt`, `realizeOf`, `realizeOf_eq_div`) —
  `ModularCurve/ComplexPlaceDictionaryOf.lean`; `ModularCurve.ComplexPlaceDictionary` —
  `ComplexPlaceDictionary.lean`.
- `ModularCurve.arithmeticGalois` — `Defs/ArithmeticGalois.lean`; `AlgebraicCurve.SemilinearAut.ofAlgAut`
  — `AlgebraicCurve/Defs/SemilinearAut.lean`.
- `ModularCurve.coeffMap`, `laurentBaseChange` — `Defs/Laurent.lean`; `IsIntegralQExp`, `intSeriesC`,
  `coeffEmb`, `coeffEmb_mem_laurentBaseChange`, `div_mem_qExpFunctionFieldC` —
  `X1/Integral.lean` / `X1/CoeffMap.lean` / `JqIntegralRatios.lean` (all in the closure).
- `ModularCurve.xHFunctionField`, `xHFunctionFieldBar` — `XH/FunctionField.lean`.
- `AlgebraicCurve.Place.exists_of_orderMap` — `AlgebraicCurve/Place/ValueDictionary.lean` (the one
  premise of 441 that is not an MC module: import it, do not re-derive).
- `UpperHalfPlane.J` (mathlib), `complexConjAlgEquiv` — `GaloisRep/Defs/ComplexConjugation.lean`.

## Traps

1. **The engine is the work.** Write the `qL`/`Pres`/`realize_*` block once, at the top of the new
   module, and prove the three headlines on top of it. A second copy is a `dedup.py` cluster and a
   review rejection.
2. **441** is the existence: `Pres` (the presheaf of local functions at the place), `mu` (the
   meromorphic-order function), `exists_mu_pos`, `mu_smul`, `mu_nonneg_iff`, `exists_place` — the
   last step is `AlgebraicCurve.Place.exists_of_orderMap`.
3. **684**'s statement's `hσ` is a *hypothesis* about `σ` (the `γ`-twist of every integral q-expansion
   ratio), not a conclusion: the row is the place-level consequence
   `SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ)`. Keep `ofAlgAut` and the `γ⁻¹ • τ` action
   (`SL(2, ℤ)` on `ℍ`, not `ℂ`).
4. **648**'s `•` on `D.pt τ` is the `arithmeticGalois` action of `complexConjAlgEquiv` (a
   `SemilinearAut`), and `UpperHalfPlane.J • τ` is the conjugation action — the pair must stay paired.
   Its `Key` section (337–569) is the longest; read it before the `Place` section.
5. Do not transcribe `p2m_open/export/reactivate`, the `P2MW.S_` namespaces, or any
   `attribute [-simp]`/`[-instance]` prelude. No `set_option` in any of the three pin files.
6. The new module's header records the engine/headline split and carries **six** `spec-pin:` lines
   (three wrappers + three `S_` copies) — but the shared engine is the pin's own private prelude, so
   only the three headlines are `ok`; say so in the prose.
7. If the shared engine has to be `private` for the wire to read 3 ok, keep it `private` and record
   that choice (the surface gate is the reviewer's, and a later promotion of the engine is a
   one-token edit).

## Gates

1. Edit loop: `cd lean && timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
   FLTForHuman/ModularCurve/ComplexPlaceDictionaryAction.lean` → silent, zero warnings.
2. Build under the **workspace** lock: `flock tmp/lean-build.lock lake build
   FLTForHuman.ModularCurve.ComplexPlaceDictionaryAction`; long builds as background jobs with logs
   in `tmp/ms5/` (FR-0072).
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/ComplexPlaceDictionaryAction.lean` →
   **3 ok / 0 mismatch / 0 missing / 0 own**.
4. `#print axioms` on all three → `[propext, Classical.choice, Quot.sound]`.
5. Six `spec-pin:` lines (three wrappers, three `S_` copies).
6. `cd tools/deps && python3 dedup.py --targets ComplexPlaceDictionaryAction --within --tier shape`
   (dry run): the *expected* result is 0 clusters, because the three pin copies became one — a
   cluster here means the engine was written twice.
7. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression, no other file,
   no git, no tree build; every command under 2 minutes.
8. Report: declarations (public/private), lines, checker line, axioms, build result, the dedup count,
   and every deviation. Leave no non-compiling file behind.
