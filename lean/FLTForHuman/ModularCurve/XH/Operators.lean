/-
The `X_H(M)` diamond-operator vocabulary and the input bundle `HeckeDiamondInputsHAll`,
after FLT's `Definitions/Def_ModularCurve_XHOperators.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHOperators.lean>).

The pin's `GenOp` block (`genOpH`, `genOpH_T`/`_U`/`_dia`, `tateGenOpH`,
`tateGenOpH_apply_coe`) and its `diamondHBar`/`diamondHBar_apply`/`diamondHBar_of_not`
are off this cone (0 references in the four `S_` files) and deferred to the
successor Jacobian topics. This module lands the diamond predicate
`IsDiamondAutHBar`, the choice function `diamondAutHBar` with its two lemmas, and
the bundle `HeckeDiamondInputsHAll` with its two accessors.

`IsDiamondAutHBar` is the base-changed (`ℚ̄`) sibling of the ported X₁ predicate
`ModularCurve.IsDiamondAut` (`ModularCurve/X1/Diamond.lean`): the same slash-ratio
condition, but read through `coeffEmb`/`xHFunctionFieldBar` rather than over `ℚ`.
Its inputs — `intSeriesC`, `div_mem_qExpFunctionFieldC` (`JqIntegralRatios.lean`),
`coeffEmb_mem_laurentBaseChange` (`Defs/Laurent.lean`), `IsIntegralQExp`
(`ModularForms/WeightOne/Gamma0Integral.lean`) and `xHFunctionFieldBar` — are all
ported.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHOperators.lean
-/
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

/-- The diamond automorphism of `X_H(M)` attached to `d`: it is the `ℚ̄`-algebra
automorphism multiplying the `q`-expansion of a ratio by the `γ`-slash with
`γ 0 0 ≡ d (mod M)`. -/
def IsDiamondAutHBar (d : (ZMod M)ˣ)
    (σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
        ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H) :
            LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

/-- The diamond automorphism at `d`, or the identity when none exists. -/
def diamondAutHBar (d : (ZMod M)ˣ) :
    xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H :=
  haveI := Classical.dec (∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
    IsDiamondAutHBar M H d σ)
  if h : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ
  then h.choose else AlgEquiv.refl

variable {M H}

theorem isDiamondAutHBar_diamondAutHBar {d : (ZMod M)ˣ}
    (h : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) :
    IsDiamondAutHBar M H d (diamondAutHBar M H d) := by
  rw [diamondAutHBar, dite_eq_left h]
  exact h.choose_spec

theorem diamondAutHBar_of_not {d : (ZMod M)ˣ}
    (h : ¬ ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) :
    diamondAutHBar M H d = AlgEquiv.refl := by
  rw [diamondAutHBar, dite_eq_right h]

variable (M H)

/-- The bundle of inputs for the `X_H(M)` Hecke operators (every prime `ℓ`) and
the diamond automorphisms (every `d ∈ (ZMod M)ˣ`). -/
def HeckeDiamondInputsHAll : Prop :=
  (∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ) ∧
    ∀ d : (ZMod M)ˣ, ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ

variable {M H}

theorem HeckeDiamondInputsHAll.heckeInputsHAlong (h : HeckeDiamondInputsHAll M H) (ℓ : ℕ)
    (hℓ : ℓ.Prime) : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ :=
  h.1 ℓ hℓ

theorem HeckeDiamondInputsHAll.isDiamondAutHBar (h : HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ) :
    IsDiamondAutHBar M H d (diamondAutHBar M H d) :=
  isDiamondAutHBar_diamondAutHBar (h.2 d)

end Diamond

end ModularCurve

end
