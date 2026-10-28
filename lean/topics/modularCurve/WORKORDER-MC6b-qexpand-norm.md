# WORKORDER MC-6b — the q-expansion of the β-operator's norm

**SET**: [SET-MC6.md](SET-MC6.md) §0–§5. **Story**: M9. **Silk**: 384. **Net**: ≈216.
**Home**: **new** `lean/FLTForHuman/ModularCurve/XH/QExpandNorm.lean`.

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_qExpand_norm_heckeBetaHBar.lean`:

```
theorem ModularCurve.qExpand_norm_heckeBetaHBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ ℓ)
    (u : ModularCurve.xHFunctionFieldBar M H) :
    ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
        ((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
          Algebra.norm (ModularCurve.xHFunctionFieldBar M H)
            (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ u) :
            ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) =
      (∏ b ∈ Finset.range ℓ,
          ModularCurve.qTwist (ζ ^ b)
            ((ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) u :
              ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ))) *
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ …
```

(Transcribe the rest of the RHS from the wrapper file — the product's second factor is the
`qExpand` of `u`; read `Theorems/Thm_ModularCurve_qExpand_norm_heckeBetaHBar.lean` for the verbatim
tail.)

Pin proof: `P2M/Sol/S_ModularCurve_qExpand_norm_heckeBetaHBar.lean` (384 lines): the degree of the
α-operator (`finrankAlong_heckeAlphaHBar`), the Atkin–Lehner intertwining
(`exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar`), the norm's q-expansion over the `ℓ`
conjugates, and the twist product.

## Vocabulary

- `ModularCurve.heckeBetaHBar`/`heckeAlphaHBar`, `HeckeDiamondInputsHAll`, `diamondAutHBar` —
  `XH/HeckeOperator.lean`, `XH/Operators.lean` (D3 + MC-4d).
- `ModularCurve.qTwist` — `ModularCurve/Defs/Twist.lean` (the port spells the pin's `twistFun` as
  `qTwistFun`/`qTwist` — check which, and do not restate it).
- `ModularCurve.qExpand` — `ModularCurve/Defs/*` (q-expansion of a function-field element).
- `AlgebraicCurve.algebraAlong`, `Algebra.norm` — `AlgebraicCurve/Defs/Correspondence.lean` and
  mathlib's `Algebra.norm`.
- The two premises (import): `ModularCurve/X1/AtkinLehnerExchange.lean`,
  `ModularCurve/XH/HeckeDegree.lean`; the pin's `Defs/PhiGen` is `ModularCurve/Defs/PhiGen.lean`.

## Traps

1. The `letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar …)` is **inside the statement** (it types
   the `Algebra.norm`); transcribe it as written.
2. `ζ : (AlgebraicClosure ℚ)ˣ` with `IsPrimitiveRoot ζ ℓ` — the twist is in `qTwist`, not in a local
   `twist`/`qTwistFun` restatement.
3. The `ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)` term is the
   diamond unit; keep the exact spelling.
4. Do not reproduce the pin's `attribute [-simp]` prelude (it is long and global in the port).
5. `hin : HeckeDiamondInputsHAll M H` is a *hypothesis*; do not discharge it.

## Gates

As WORKORDER-MC6a's §Gates: `check_port` → the headline `ok`; **two** `spec-pin:` lines; one module
build (background channel on a busy tree, FR-0060); axioms; silent; 0 dedup clusters; no
`set_option`, no suppression, no other file, no git, no tree build; every command under 2 minutes.
