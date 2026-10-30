/-
The diamond-operator pullback predicate over `Γ_H`, the definition layer of the
`ModularCurve` diamond-mod-`ℓ` work (`IsDiamondPullbackModL`, the pin's
`mod ℓ` weakening of the diamond compatibilities): the property that a
`K`-automorphism `ρ` of the `q`-expansion function field of `Γ_H(M)` sends a
ratio of integral `q`-expansions of `γ`-twins back to the corresponding ratio.

Transcribed verbatim from FLT's `Definitions/Def_ModularCurve_XHDiamondModL.lean`
(pinned `aa2d8b3`, 50 lines), whole: the two declarations the pin has, at the
pin's names. `IsDiamondPullbackModL` is the predicate; its projection lemma
`IsDiamondPullbackModL.coe_apply_eq` is the `Prop`-elimination of the pin's
`∀`-body, carrying the pin's `variable` block (`K`, `M`, `H`, `ρ` implicit).

The pin's imports map to the port as: `Def_ModularCurve_XH` →
`ModularCurve/X1/Defs.lean` (`qExpFunctionFieldC`, `intSeriesC`, and
`ModularCurve/X1/Integral.lean` underneath for `IsIntegralQExp`) and
`ModularForms/Defs/GammaH.lean` (`CohCarrier.GammaH`). That is the whole
vocabulary of the statement; no node module is imported.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHDiamondModL.lean

spec-pin: Definitions/Def_ModularCurve_XHDiamondModL.lean
-/
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularForms.Defs.GammaH

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve

/-- The pin's `Def_ModularCurve_XHDiamondModL.IsDiamondPullbackModL`: a
`K`-automorphism `ρ` of the `q`-expansion function field of `Γ_H(M)` pulls a
ratio `q(f₁)/q(g₁)` of integral `q`-expansions of `γ`-twins of `f` and `g`
to the ratio `q(f)/q(g)`. -/
def IsDiamondPullbackModL (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        qExpFunctionFieldC K (CohCarrier.GammaH M H))) : Prop :=
  ∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
    (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg pf₁ pg₁ : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg →
    IsIntegralQExp f₁ pf₁ → IsIntegralQExp g₁ pg₁ →
    (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    intSeriesC K pg ≠ 0 →
    ∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
      (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁ →
      ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
        intSeriesC K pf / intSeriesC K pg

variable {K : Type*} [Field K] {M : ℕ} {H : Subgroup (ZMod M)ˣ}
  {ρ : CongruenceSubgroup.Gamma0 M →*
    (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H))}

/-- The pin's projection lemma: a pointwise read-off of
`IsDiamondPullbackModL` at the pin's own argument order. -/
theorem IsDiamondPullbackModL.coe_apply_eq (hρ : IsDiamondPullbackModL K M H ρ)
    (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
    {f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k}
    {pf pg pf₁ pg₁ : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf₁ : IsIntegralQExp f₁ pf₁) (hg₁ : IsIntegralQExp g₁ pg₁)
    (hfs : (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hgs : (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hpg : intSeriesC K pg ≠ 0)
    {x : qExpFunctionFieldC K (CohCarrier.GammaH M H)}
    (hx : (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁) :
    ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
      intSeriesC K pf / intSeriesC K pg :=
  hρ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx

end ModularCurve

end
