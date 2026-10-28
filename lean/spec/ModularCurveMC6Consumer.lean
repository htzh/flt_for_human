/-
  Consumer specification for **SET MC-6** (M9): Fricke, and the q-expansion norm of the β-operator.

  Written-down *uses* of the set's two headlines, composed across modules.  Not part of any
  library; run by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveMC6Consumer.lean 2>&1 | grep -c error

  ZONES
  -----
    [fricke] ZONE A — the slash-Fricke sum unpacked: the existential's two conclusions (the
             integrality of every summand's q-expansion and the identity) read separately, and the
             sum consumed by `Finset.sum`'s `smul`-linearity.
    [norm]   ZONE B — the q-expansion norm of the β-operator at `ℓ = 2`, with the diamond inputs
             hypothesis taken from D3's bundle and the twist product consumed at `b = 0`.
-/

import FLTForHuman.ModularCurve.XH.FrickeSlash
import FLTForHuman.ModularCurve.XH.QExpandNorm

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups ModularForm

namespace MC6Consumer

/-! ## Zone A — `[fricke]` the slash-Fricke sum -/

theorem fricke_slash_eq_sum_smul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) :=
  ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion M H f hf ι W hW

/-- The same row, with its two conclusions split: the summands' integral q-expansions as an
existential of their own, and the identity — the shape the leaves' coefficient rows consume. -/
theorem fricke_slash_eq_sum_smul_split (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
      (∃ p : Fin n → PowerSeries ℤ, ∀ i, ModularCurve.IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by
  obtain ⟨n, c, g, p, hp, hsum⟩ :=
    ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion M H f hf ι W hW
  exact ⟨n, c, g, ⟨p, hp⟩, hsum⟩

/-! ## Zone B — `[norm]` the β-operator's norm at `ℓ = 2` -/

theorem qExpand_norm_heckeBetaHBar_two (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hℓM : ¬ (2 : ℕ) ∣ M) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ 2)
    (u : ModularCurve.xHFunctionFieldBar M H) :
    ModularCurve.qExpand (AlgebraicClosure ℚ) 2
        ((letI := AlgebraicCurve.algebraAlong
            (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H 2)
          Algebra.norm (ModularCurve.xHFunctionFieldBar M H)
            (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H 2 u) :
            ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) =
      (∏ b ∈ Finset.range 2,
          ModularCurve.qTwist (ζ ^ b)
            ((ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr
                  hℓM)) u : ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ))) *
        ModularCurve.qExpand (AlgebraicClosure ℚ) 2
          (ModularCurve.qExpand (AlgebraicClosure ℚ) 2
            (u : LaurentSeries (AlgebraicClosure ℚ))) :=
  ModularCurve.qExpand_norm_heckeBetaHBar M H hℓM hin ζ hζ u

end MC6Consumer
