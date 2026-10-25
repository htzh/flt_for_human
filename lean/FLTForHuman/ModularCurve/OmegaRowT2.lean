/-
The `omegaRow_T2` identity: the `q`-expansion row of the `T_2`-omega differential, and the
`θ`/`coeffMap` commutation it consumes.

`θ = q d/dq` is the normalised derivation on `LaurentSeries`, `Δ` the discriminant and
`E₄`, `E₆` the level-one Eisenstein series. The identity is

    `coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) * Δ = -(E₄ ^ 2 * E₆)`

in `q`-expansions. It is proved on the `ANb` dictionary — `𝒩`, the `q`-expansion `ψ`, the
complex realisation `toC`, `𝔞`/`𝔟`/`𝔡` for `E₄`/`E₆`/`Δ`, and the identities
`J · Δ = E₄³`, `E₄³ - E₆² = 1728 Δ` — which lives in
`ModularCurve/Analytic/ANb.lean`. This module adds the `θ` layer on top: after `θ` is
applied to those two identities, eliminating `θ Δ` with the Rankin–Cohen relation
`4 A θB - 6 θA B = -3456 Δ` between the differential leaves of the pair leaves
`ψ 𝔡 * θ 𝐉 + ψ 𝔞 ^ 2 * ψ 𝔟 = 0`, and that is the omega row
(`thetaJ_mul_D`), transported to the statement above along `thetaL_coeffEmb_jq`.

Two pinned statements are homed here, in that order: the `θ`/`coeffMap` commutation
`thetaL_coeffMap_eq_coeffMap_single_mul_derivative` (the `θ` fact the omega row
consumes), and `omegaRow_T2` itself, at its `Theorems/` wrapper's statement.

After FLT's `P2M/Sol/S_omegaRow_T2.lean` and
`P2M/Sol/S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean`, pinned at
`aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_omegaRow_T2.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean>.

Assumes `ModularCurve/Analytic/ANb.lean` (the dictionary), `ModularCurve/Period/ThetaMul.lean`
(`θ`'s Leibniz rule) and `ModularCurve/Defs/OmegaOf.lean` (`θ` on `LaurentSeries`). The
`omegaRow_T2` wrapper's `Def_ModularCurve_EigenformIdeal.lean` import is not homed; its
declarations (`IsEigenformIdeal`, `EigenformSupportAt`, `EichlerShimuraDataAt`) appear
neither in the statement nor in the proof.

spec-pin: Theorems/Thm_omegaRow_T2.lean
spec-pin: P2M/Sol/S_omegaRow_T2.lean
spec-pin: Theorems/Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean
spec-pin: P2M/Sol/S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean
-/

import FLTForHuman.ModularCurve.Analytic.ANb
import FLTForHuman.ModularForms.QCoeffLevelOne
import FLTForHuman.ModularCurve.Defs.OmegaOf
import FLTForHuman.ModularCurve.Period.ThetaMul
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularForms.JqAnalyticModel
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section
open UpperHalfPlane ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm Manifold


/-! ### `θ` commutes with `coeffMap` -/

namespace ModularCurve

section

variable {R K : Type*} [CommRing R] [Field K]

private theorem coeffMap_single_one (φ : R →+* K) :
    coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single (1 : ℤ) (1 : K) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

private theorem derivative_coeffMap (φ : R →+* K) (w : LaurentSeries R) :
    LaurentSeries.derivative K (coeffMap φ w) = coeffMap φ (LaurentSeries.derivative R w) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeffMap_coeff,
    coeffMap_coeff, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, map_zsmul]

end

/-- `θ` commutes with `coeffMap` up to the `single 1 1` factor: the pin's public
statement, with its private helper's body (the two said the same thing in one line). -/
theorem thetaL_coeffMap_eq_coeffMap_single_mul_derivative {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    thetaL K (coeffMap φ w) =
      coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by
  rw [thetaL_apply, derivative_coeffMap, map_mul, coeffMap_single_one]

end ModularCurve

namespace ANb

local notation "𝒩" => niceSubalgebra
local notation "𝐉" => ModularCurve.coeffEmb ℂ ModularCurve.jq
local notation "θ" => ModularCurve.thetaL ℂ

theorem theta_mul' (x y : LaurentSeries ℂ) : θ (x * y) = x * θ y + y * θ x := by
  rw [ModularCurve.thetaL_apply, ModularCurve.thetaL_apply, ModularCurve.thetaL_apply]
  exact ModularCurve.theta_mul x y

theorem theta_one : θ (1 : LaurentSeries ℂ) = 0 := by
  have e := theta_mul' 1 1
  rw [mul_one, one_mul] at e
  have e' : θ 1 + θ 1 = θ 1 + 0 := by rw [add_zero]; exact e.symm
  exact add_left_cancel e'

theorem theta_natCast (n : ℕ) : θ (n : LaurentSeries ℂ) = 0 := by
  rw [← nsmul_one, map_nsmul, theta_one, nsmul_zero]

theorem theta_1728 : θ (1728 : LaurentSeries ℂ) = 0 := by
  rw [show (1728 : LaurentSeries ℂ) = ((1728 : ℕ) : LaurentSeries ℂ) from (Nat.cast_ofNat).symm]
  exact theta_natCast 1728

theorem ofPowerSeries_mk_mul (p : PowerSeries ℂ) :
    HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun n => (n : ℂ) * PowerSeries.coeff n p) =
      θ (HahnSeries.ofPowerSeries ℤ ℂ p) := by
  ext k
  rw [ModularCurve.thetaL_apply, ModularCurve.theta_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk,
      zsmul_eq_mul, Int.cast_natCast]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, smul_zero]

theorem Gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun γ => ?_
  rw [CongruenceSubgroup.Gamma0_mem]
  exact Subsingleton.elim _ _

theorem rankinCohen_E4_E6 :
    4 * ψ 𝔞 * θ (ψ 𝔟) - 6 * θ (ψ 𝔞) * ψ 𝔟 = -3456 * ψ 𝔡 := by
  have : (CongruenceSubgroup.Gamma0 1).FiniteIndex := by rw [Gamma0_one_eq_top]; infer_instance
  obtain ⟨g4, hg4⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne 1 ModularForm.E₄
  obtain ⟨g6, hg6⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne 1 ModularForm.E₆
  obtain ⟨RC, -, hRCq⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq
    (Γ := CongruenceSubgroup.Gamma0 1) (one_mem_strictPeriods_gamma0 1) g4 g6
  rw [hg4, hg6] at hRCq

  have hΓ : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) =
      Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 1) := by
    rw [Gamma0_one_eq_top, ← MonoidHom.range_eq_map]
  let Z : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) RC hΓ
  have hZcoe : (Z : ℍ → ℂ) = (RC : ℍ → ℂ) := rfl
  have hZq : qExpansion 1 (Z : ℍ → ℂ) =
      PowerSeries.C (4 : ℂ) * qExpansion 1 ⇑ModularForm.E₄ *
          PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 ⇑ModularForm.E₆).coeff n)
        - PowerSeries.C (6 : ℂ) *
          PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 ⇑ModularForm.E₄).coeff n) *
            qExpansion 1 ⇑ModularForm.E₆ := by
    rw [hZcoe]; exact_mod_cast hRCq
  have hmk0 : ∀ p : PowerSeries ℂ, PowerSeries.coeff 0 (PowerSeries.mk fun n : ℕ => (n : ℂ) * PowerSeries.coeff n p) = 0 := by
    intro p; rw [PowerSeries.coeff_mk]; simp
  have hmk1 : ∀ p : PowerSeries ℂ, PowerSeries.coeff 1 (PowerSeries.mk fun n : ℕ => (n : ℂ) * PowerSeries.coeff n p) =
      PowerSeries.coeff 1 p := by
    intro p; rw [PowerSeries.coeff_mk]; simp
  have h0 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 0 = 0 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_zero_mul', hmk0, PowerSeries.coeff_zero_C]
    ring
  have h1 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 1 = -3456 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_one_mul, coeff_zero_mul', hmk0, hmk1,
      PowerSeries.coeff_zero_C, qA0, qA1, qB0, qB1]
    have hC4 : PowerSeries.coeff 1 (PowerSeries.C (4 : ℂ)) = 0 := by
      rw [PowerSeries.coeff_C, ite_eq_right one_ne_zero]
    have hC6 : PowerSeries.coeff 1 (PowerSeries.C (6 : ℂ)) = 0 := by
      rw [PowerSeries.coeff_C, ite_eq_right one_ne_zero]
    rw [hC4, hC6]
    norm_num
  have hW := ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0
  have hZΔ : qExpansion 1 (Z : ℍ → ℂ) = PowerSeries.C (-3456) * qExpansion 1 ModularForm.discriminant := by
    ext n
    rw [PowerSeries.coeff_C_mul]
    have := hW n
    have h1' := h1
    simp only [ModularFormClass.qCoeff] at this h1'
    rw [this, h1']

  have hL := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hZΔ
  rw [hZq] at hL
  simp only [map_sub, map_mul, HahnSeries.ofPowerSeries_C, ofPowerSeries_mk_mul] at hL
  rw [← ψ𝔞, ← ψ𝔟, ← ψ𝔡] at hL
  have e4 : (HahnSeries.C (4 : ℂ) : LaurentSeries ℂ) = 4 := map_ofNat _ 4
  have e6 : (HahnSeries.C (6 : ℂ) : LaurentSeries ℂ) = 6 := map_ofNat _ 6
  have e3456 : (HahnSeries.C (-3456 : ℂ) : LaurentSeries ℂ) = -3456 := by
    rw [map_neg, map_ofNat]
  rw [e4, e6, e3456] at hL
  linear_combination hL

theorem thetaL_coeffEmb_jq :
    θ (𝐉) = coeffMap (algebraMap ℚ ℂ) (ModularCurve.thetaL ℚ jq) := by
  rw [coeffEmb, ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative]
  rfl

theorem thetaJ_mul_D : θ (𝐉) * ψ 𝔡 = -(ψ 𝔞 ^ 2 * ψ 𝔟) := by
  have H3 : 𝐉 * ψ 𝔡 = ψ 𝔞 * ψ 𝔞 * ψ 𝔞 := by rw [J_mul_D]; ring
  have H2' : ψ 𝔞 * ψ 𝔞 * ψ 𝔞 - ψ 𝔟 * ψ 𝔟 = 1728 * ψ 𝔡 := by
    rw [← A_cube_sub_B_sq]; ring
  have H1 := rankinCohen_E4_E6

  have H5 : ψ 𝔡 * θ (𝐉) + 𝐉 * θ (ψ 𝔡) = 3 * (ψ 𝔞) ^ 2 * θ (ψ 𝔞) := by
    have e := congrArg (ModularCurve.thetaL ℂ) H3
    simp only [theta_mul'] at e
    linear_combination e
  have H6 : 3 * (ψ 𝔞) ^ 2 * θ (ψ 𝔞) - 2 * ψ 𝔟 * θ (ψ 𝔟) = 1728 * θ (ψ 𝔡) := by
    have e := congrArg (ModularCurve.thetaL ℂ) H2'
    simp only [map_sub, theta_mul', theta_1728] at e
    linear_combination e
  have hD := ψ𝔡_ne_zero
  have h1728 : (1728 : LaurentSeries ℂ) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 1728]
    exact HahnSeries.C_ne_zero (by norm_num)
  have h2 : (2 : LaurentSeries ℂ) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 2]
    exact HahnSeries.C_ne_zero (by norm_num)

  have key : (2 * 1728 * ψ 𝔡) * (ψ 𝔡 * θ (𝐉) + ψ 𝔞 ^ 2 * ψ 𝔟) = 0 := by
    linear_combination (2 * 1728 * ψ 𝔡) * H5 - (2 * 1728 * θ (ψ 𝔡)) * H3
      + (2 * (ψ 𝔞 * ψ 𝔞 * ψ 𝔞)) * H6 - (6 * ψ 𝔞 ^ 2 * θ (ψ 𝔞)) * H2' + (ψ 𝔞 ^ 2 * ψ 𝔟) * H1
  have : ψ 𝔡 * θ (𝐉) + ψ 𝔞 ^ 2 * ψ 𝔟 = 0 :=
    (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero h2 h1728) hD)
  linear_combination this

end ANb

open ANb in
theorem omegaRow_T2 :
    coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 *
          ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  rw [← ANb.thetaL_coeffEmb_jq]
  exact ANb.thetaJ_mul_D

