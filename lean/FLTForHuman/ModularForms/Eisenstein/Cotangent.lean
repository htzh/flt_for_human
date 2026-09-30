/-
  The cotangent / Weierstrass-`ζ` prelude shared by the weight-one Eisenstein
  modules.

  These declarations are the common part of the four pinned solution files
  `P2M/Sol/S_EisensteinSeries_*.lean` (pin `aa2d8b3`) that build the
  `eisensteinG1` API: the lattice vector `om`, the Weierstrass `ζ` summand
  `zterm`, the lattice-point predicate `NotLat`, the cotangent estimates used
  for boundedness at the cusp, and the two series carriers `ser` / `pval`.
  They are homed here exactly once so the later modules can import them.

  The pin repeats some of them in different implementation namespaces
  (`WZA`/`WZB`/`WZC`/`WZD`); this file is their union at the pin's names and
  statements. The headline `hasSum_ser` is deliberately *not* ported: its pin
  proof appeals to `EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2`, a
  phase-T target that is not in the port.
-/
import FLTForHuman.ModularForms.Eisenstein.WeierstrassZeta
import FLTForHuman.ModularForms.EisensteinSeries
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

set_option autoImplicit false

open scoped Topology Real MatrixGroups Matrix
open UpperHalfPlane hiding I
open EisensteinSeries Filter Complex

noncomputable section

namespace EisensteinSeries

variable (τ : ℍ)

/-- The lattice point `v 0 * τ + v 1` attached to an integer vector. -/
def om (v : Fin 2 → ℤ) : ℂ := (v 0 : ℂ) * τ + v 1

/-- The `v`-summand of the Weierstrass `ζ` expansion at `z`. -/
def zterm (z : ℂ) (v : Fin 2 → ℤ) : ℂ :=
  if v = 0 then 0 else (1 / (z - om τ v) + 1 / om τ v + z / om τ v ^ 2)

lemma weierstrassZeta_eq (z : ℂ) : weierstrassZeta τ z = 1 / z + ∑' v, zterm τ z v := rfl

lemma om_smul (γ : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    om (γ • τ) v = om τ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) / denom γ τ := by
  have h := eisSummand_SL2_apply (-1) v γ τ
  simp only [eisSummand, neg_neg, zpow_one, zpow_neg] at h
  simpa [om, div_eq_inv_mul] using h

lemma cot_neg (x : ℂ) : Complex.cot (-x) = -Complex.cot x := by
  simp [Complex.cot_eq_cos_div_sin, Complex.sin_neg, Complex.cos_neg, div_neg]

lemma norm_cexp_two_pi_I (w : ℂ) : ‖cexp (2 * π * I * w)‖ = Real.exp (-2 * π * w.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, mul_comm]

lemma pi_cot_add_eq (w : ℂ) (hq : cexp (2 * π * I * w) ≠ 1) :
    π * Complex.cot (π * w) + π * I =
      2 * π * cexp (2 * π * I * w) / (I * (1 - cexp (2 * π * I * w))) := by
  rw [Complex.cot_pi_eq_exp_ratio]
  set q := cexp (2 * π * I * w) with hq_def
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have h2 : I * (1 - q) ≠ 0 := mul_ne_zero I_ne_zero h1
  rw [eq_div_iff h2, add_mul, mul_assoc, div_mul_cancel₀ _ h2]
  ring_nf
  rw [I_sq]
  ring

lemma norm_pi_cot_add_le {w : ℂ} {Y : ℝ} (hY : 0 < Y) (hw : Y ≤ w.im) :
    ‖π * Complex.cot (π * w) + π * I‖ ≤
      2 * π * Real.exp (-2 * π * w.im) / (1 - Real.exp (-2 * π * Y)) := by
  have hq : ‖cexp (2 * π * I * w)‖ = Real.exp (-2 * π * w.im) := norm_cexp_two_pi_I w
  have hqY : Real.exp (-2 * π * w.im) ≤ Real.exp (-2 * π * Y) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hY1 : Real.exp (-2 * π * Y) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hq1 : ‖cexp (2 * π * I * w)‖ < 1 := by rw [hq]; linarith
  have hne : cexp (2 * π * I * w) ≠ 1 := by
    intro h; rw [h, norm_one] at hq1; exact lt_irrefl _ hq1
  rw [pi_cot_add_eq w hne, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, hq]
  have hden : 1 - Real.exp (-2 * π * Y) ≤ ‖1 - cexp (2 * π * I * w)‖ := by
    calc 1 - Real.exp (-2 * π * Y) ≤ 1 - ‖cexp (2 * π * I * w)‖ := by rw [hq]; linarith
      _ = ‖(1 : ℂ)‖ - ‖cexp (2 * π * I * w)‖ := by rw [norm_one]
      _ ≤ ‖1 - cexp (2 * π * I * w)‖ := norm_sub_norm_le _ _
  have hpos : 0 < 1 - Real.exp (-2 * π * Y) := by linarith
  exact div_le_div_of_nonneg_left (by positivity) hpos hden

lemma norm_pi_cot_sub_le {w : ℂ} {Y : ℝ} (hY : 0 < Y) (hw : w.im ≤ -Y) :
    ‖π * Complex.cot (π * w) - π * I‖ ≤
      2 * π * Real.exp (2 * π * w.im) / (1 - Real.exp (-2 * π * Y)) := by
  have hw' : Y ≤ (-w).im := by simp; linarith
  have := norm_pi_cot_add_le hY hw'
  rw [show π * (-w) = -(π * w) by ring, cot_neg] at this
  rw [show π * Complex.cot (π * w) - π * I = -(π * -Complex.cot (π * w) + π * I) by ring, norm_neg]
  simpa using this

/-- `z` is not a lattice point of `ℤ τ + ℤ`. -/
def NotLat (τ : ℍ) (z : ℂ) : Prop := ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1

variable {τ}

lemma NotLat.add_intCast {z : ℂ} (hz : NotLat τ z) (n : ℤ) : NotLat τ (z + n) := by
  intro v hv
  apply hz (v - ![0, n])
  simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, Int.cast_sub]
  linear_combination hv

lemma NotLat.add_intCast_mul {z : ℂ} (hz : NotLat τ z) (n : ℤ) : NotLat τ (z + n * τ) := by
  intro v hv
  apply hz (v - ![n, 0])
  -- (`Int.cast_zero` was in the pin's `simp only` set but is unused under v4.34.0.)
  simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, Int.cast_sub]
  linear_combination hv

variable (τ)

lemma om_injective : Function.Injective (om τ) := by
  intro u v huv
  have h : om τ (u - v) = 0 := by
    simp only [om, Pi.sub_apply, Int.cast_sub] at huv ⊢
    linear_combination huv
  by_contra hne
  have hne' : u - v ≠ 0 := sub_ne_zero.mpr hne
  have := UpperHalfPlane.linear_ne_zero (cd := fun i => ((u - v) i : ℝ)) τ
    (by
      intro h0
      apply hne'
      funext i
      have := congr_fun h0 i
      simp only [Pi.zero_apply] at this ⊢
      exact_mod_cast this)
  apply this
  simpa [om] using h

/-- The `m`-th summand of the Weierstrass `ζ` cotangent series. -/
def ser (z : ℂ) (m : ℕ) : ℂ :=
  π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) + π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ))

/-- The value of the Weierstrass `ζ` cotangent series. -/
def pval (z : ℂ) : ℂ := weierstrassZeta τ z - z * G2 τ - π * Complex.cot (π * z)

end EisensteinSeries

end
