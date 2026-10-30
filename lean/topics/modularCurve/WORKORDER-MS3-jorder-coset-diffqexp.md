# WORKORDER MS-3 — the j-order at τ, the coset translate, and `qExpansionDiffAlong`

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U9/U10/U11, §2, §3, §4.
**Story**: U9 + U10 + U11. **Silo**: 817 (611 + 144 + 62). **Net**: ≈734.
**Homes**: **three insertions**, no new module. Each host has today **zero** dependents in the
port's import graph, so an insertion re-elaborates one module and nothing else.

| row | silo | host | baseline → target |
|---|---:|---|---|
| U9 | 611 | `lean/FLTForHuman/ModularCurve/TateSlots/Invariants.lean` | **91 ok** / 0 / 0 → 92 |
| U10 | 144 | `lean/FLTForHuman/ModularCurve/ModularPolynomialCoset.lean` | **16 ok** / 0 / 0 → 17 |
| U11 | 62 | `lean/FLTForHuman/ModularCurve/Period/QExpansionDiff.lean` | **3 ok** / 0 / 0 → 4 |

Two of the three insertions need **one added import each** (stated here so it is not a discovery):

- U10: `import FLTForHuman.ModularCurve.Analytic.QParamUnique` into
  `ModularPolynomialCoset.lean`. Checked acyclic: `Analytic/QParamUnique.lean` imports **no** port
  module (mathlib only).
- U11: `import FLTForHuman.ModularCurve.Defs.HeckeDifferential` into `Period/QExpansionDiff.lean`.
  Checked acyclic both ways; the file already imports `Period/QExpansionDerivative` (its other
  premise's home), so that one is not needed again.
- U9 needs **no** new import: its one premise, `exists_smul_eq_of_E4_cube_div_discriminant_eq`, is
  declared in `TateSlots/Invariants.lean` itself.

## The declarations

All three wrappers, verbatim.

`Theorems/Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.lean`:

```
theorem ModularCurve.meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
    (τ : ℍ) :
    meromorphicOrderAt
        (fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 /
            ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) (τ : ℂ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ)
```

`Theorems/Thm_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.lean`:

```
theorem ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst {N a b d : ℕ} (hN : N ≠ 0)
    (had : a * d = N) [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (F G : ℍ → ℂ) (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hFbd : UpperHalfPlane.IsBoundedAtImInfty F)
    (hG : ∀ τ τ' : ℍ, ((τ' : ℂ) = ((a : ℂ) * τ + b) / d) → G τ = F τ') :
    Function.Periodic (G ∘ UpperHalfPlane.ofComplex) N ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G ∧
      UpperHalfPlane.IsBoundedAtImInfty G ∧
      ((qExpansion N G : PowerSeries ℂ) : LaurentSeries ℂ)
        = ModularCurve.cosetSubst ζ a b ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ)
```

`Theorems/Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.lean`:

```
theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExp {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    qExpansionDiffAlong F.val ω = diffQExp F ω
```

## The pin proofs

**611** — `P2M/Sol/S_ModularCurve_meromorphicOrderAt_….lean`, 611 lines / 63 declarations, in
`namespace ModularCurve` then `namespace JMultiplicity` (one section, 16–594). The engine is:
`jf`/`jf_smul`/`jf_`/`jf_I_ne_zero`, `E` (the `E₄³/Δ` abbreviation), `mdifferentiable_jf`,
`D_smul`/`S_smul_I`/`TinvS_smul_`/`denom_TinvS_`, `natCard_stabilizer_I`/`_smul`/`_eq_two`,
`orbit_trichotomy`, the level-14 witnesses `g14`/`e14` (+`_apply`, `_ne_zero`) and
`finrank_fourteen`, then the order comparison: `deriv_jf_eq`, `deriv_jf_eventuallyEq`,
`analyticOrderAt_deriv_jf`, `jf_eq_of_E`, `order_deriv_add_one`, `case_E`/`case_generic`,
`order_and_card`, `main`, `solution`.

**144** — `P2M/Sol/S_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.lean`, 144 lines /
4 declarations, in `namespace ModularCurve` then `namespace CosetTranslateAux`: `cosetPt` (+
`coe_cosetPt`, `cosetPt_im`) and `hasSum_laurent`; then the headline `solution`. The ported
premises are `ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow` (`ModularPolynomialCoset.lean`)
and `ModularCurve.laurent_qParam_coeff_unique` (`Analytic/QParamUnique.lean`).

**62** — `P2M/Sol/S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.lean`, 62 lines /
6 declarations: a `section Engine` (13–29) then the headline. The ported premises are
`ModularCurve.theta_coeff` (`Period/QExpansionDerivative.lean`) and
`ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong` (`Period/QExpansionDiff.lean`).

## Vocabulary (all ported — import, never re-derive)

- U9: `UpperHalfPlane`/`ℍ` coercions and `meromorphicOrderAt` (mathlib);
  `ModularForm.E₄`, `ModularForm.discriminant` (mathlib/ported); `ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq`
  in the host module.
- U10: `ModularCurve.cosetSubst` (`Defs/PhiGen.lean`), `UpperHalfPlane.qExpansion`,
  `Function.Periodic.qParam`, `MDifferentiable` (`open scoped Manifold`), `ℂˣ`.
- U11: `Ω[F⁄L]` and the differential vocabulary (`AlgebraicCurve/Differential/…`), `diffQExp`
  (`Period/QExpansionDiff.lean`), `qExpansionDiffAlong` (`Defs/QExpansionDiff.lean`).

## Traps

1. **U9**'s statement is over `ℍ` with an explicit `ofComplex`; the pin's `E` and `jf` are the
   `E₄³/Δ` abbreviations, and the pin proves the two cases (`case_E` the elliptic points,
   `case_generic`) separately. The host module already holds the 254-row engine this row's single
   premise is — read it before writing (`grep -n "exists_smul_eq_of_E4_cube_div_discriminant_eq"`).
2. **U9**'s `E₄`/`discriminant` appear both as `ℍ → ℂ` and coerced at `z : ℂ`; that is the
   statement's shape, not a slip. `Nat.card (MulAction.stabilizer SL(2, ℤ) τ)` is the `Nat.card`
   of a subgroup of a finite group — keep the `/ 2 : ℕ` and the `: ℤ` cast.
3. **U10**'s statement is a four-clause conjunction *ending* with the `qExpansion` identity; the
   first three clauses (`Periodic`, `MDifferentiable`, `IsBoundedAtImInfty`) are the pin's, not
   decoration. `hG` is stated over `ℍ × ℍ` with an equality of the complex coercion — keep both
   binders and the `τ'` name.
4. **U11** is `qExpansionDiffAlong F.val ω = diffQExp F ω` for an `IntermediateField` `F` and an
   `Ω[F⁄L]`: the `F.val` coercion is part of the statement. Do not specialise `L` or assume
   `F = ⊤`.
5. Do not touch the hosts' existing declarations, their `spec-pin:` blocks' existing lines, or
   their headers' existing prose; **append** to each (a new section, two new `spec-pin:` lines for
   its row). No `p2m_*`, no `attribute [-simp]`/`[-instance]` prelude, no `set_option`, no
   `sorry`.
6. `Period/QExpansionDiff.lean` and `ModularPolynomialCoset.lean` are recent modules (leaves wave);
   their headers carry a `spec-pin:` list — extend it, do not rewrite it.
7. The pin sets no `maxHeartbeats` on 144 and 62; 611's is not carried by its `S_` either. If a
   declaration will not fit at 200k, diagnose the inference.

## Gates

1. Edit loop, per file as you go: `cd lean && timeout 120 lake env lean -DautoImplicit=false
   -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/TateSlots/Invariants.lean` (and the other two)
   → silent, zero warnings.
2. Build each host after its insertion, serialized:
   `flock tmp/lean-build.lock timeout 90 lake build FLTForHuman.ModularCurve.TateSlots.Invariants`
   (then `…ModularCurve.ModularPolynomialCoset`, `…ModularCurve.Period.QExpansionDiff`).
3. `python3 spec/check_port.py --force <host>` after each: **91 → 92**, **16 → 17**, **3 → 4** ok,
   each with 0 mismatch / 0 missing / 0 own.
4. `#print axioms` on all three headlines → `[propext, Classical.choice, Quot.sound]`.
5. Two new `spec-pin:` lines per host (the row's `Thm_` wrapper and its `S_` copy).
6. `cd tools/deps && python3 dedup.py --targets <host-stem> --within --tier shape` per host (dry run, report only).
7. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression, no other
   file touched, no git, no tree build; every command under 2 minutes.
8. Report: per host, the declarations added (public/private), lines, checker line, axioms, build
   result, and every deviation from this brief.
