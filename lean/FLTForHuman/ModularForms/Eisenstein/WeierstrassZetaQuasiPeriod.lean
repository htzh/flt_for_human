/-
  The quasi-periods of the Weierstrass `ζ`-function: translation by the two
  lattice generators changes `ζ` by combinations of `G₂`, and the `SL(2, ℤ)`
  transformation law.

  Transcribed from
  `P2M/Sol/S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean`
  (pinned `aa2d8b3`, 284 lines), whose public target is the wrapper
  `Theorems/Thm_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean`.

  This module also lands `hasSum_ser`, the cotangent-expansion statement the H1
  home (`FLTForHuman/ModularForms/Eisenstein/Cotangent.lean`) deliberately omitted:
  its pin proof appeals to `hasSum_weierstrassZeta_sub_mul_G2`, i.e. to module
  `WeierstrassZetaSum.lean`. The rest of the shared prelude (`om`, `zterm`,
  `weierstrassZeta_eq`, `om_smul`, `cot_neg`, `norm_cexp_two_pi_I`,
  `pi_cot_add_eq`, `norm_pi_cot_add_le`, `norm_pi_cot_sub_le`, `NotLat` and its
  two translations, `ser`, `pval`) is imported from H1 rather than repeated.
-/
import FLTForHuman.ModularForms.Eisenstein.WeierstrassZetaSum
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false

open scoped Topology Real MatrixGroups Matrix
open UpperHalfPlane hiding I
open EisensteinSeries Filter Complex

noncomputable section

namespace EisensteinSeries

variable (τ : ℍ)

def vecMulEquiv (γ : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  invFun v := v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  left_inv v := by
    simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by
    simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

lemma vecMul_eq_zero_iff (γ : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congr_arg (vecMulEquiv γ).symm h
    rw [show (vecMulEquiv γ).symm (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = v from
      (vecMulEquiv γ).symm_apply_apply v] at this
    rw [this]
    simp [vecMulEquiv]
  · rintro rfl; simp

lemma zterm_smul (γ : SL(2, ℤ)) (z : ℂ) (v : Fin 2 → ℤ) :
    zterm (γ • τ) (z / denom γ τ) v =
      denom γ τ * zterm τ z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  by_cases hv : v = 0
  · subst hv
    simp [zterm]
  · have hv' : v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0 := by
      rwa [Ne, vecMul_eq_zero_iff]
    rw [zterm, ite_eq_right hv, zterm, ite_eq_right hv', om_smul]
    set D : ℂ := denom (γ : GL (Fin 2) ℝ) τ with hDdef
    set w : ℂ := om τ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ))
    rw [show z / D - w / D = (z - w) / D by ring, one_div_div, one_div_div,
      show z / D / (w / D) ^ 2 = D * (z / w ^ 2) by
        field_simp]
    rw [div_eq_mul_one_div D (z - w), div_eq_mul_one_div D w]
    ring

theorem weierstrassZeta_smul (γ : SL(2, ℤ)) (z : ℂ) :
    weierstrassZeta (γ • τ) (z / denom γ τ) = denom γ τ * weierstrassZeta τ z := by
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  rw [weierstrassZeta_eq, weierstrassZeta_eq, one_div_div]
  simp_rw [zterm_smul]
  rw [tsum_mul_left]
  rw [show ∑' v, zterm τ z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = ∑' v, zterm τ z v from
    (vecMulEquiv γ).tsum_eq (zterm τ z)]
  rw [div_eq_mul_one_div]
  ring

lemma cot_pi_add_one (w : ℂ) : Complex.cot (π * (w + 1)) = Complex.cot (π * w) := by
  rw [Complex.cot_pi_eq_exp_ratio, Complex.cot_pi_eq_exp_ratio]
  have : cexp (2 * π * I * (w + 1)) = cexp (2 * π * I * w) := by
    rw [mul_add, Complex.exp_add, mul_one, Complex.exp_two_pi_mul_I, mul_one]
  rw [this]

lemma cot_pi_add_intCast (w : ℂ) (n : ℤ) : Complex.cot (π * (w + n)) = Complex.cot (π * w) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [← ih]; push_cast; rw [← add_assoc, cot_pi_add_one]
  | pred n ih =>
      rw [← ih]; push_cast
      rw [show w + -(n : ℂ) = (w + (-(n : ℂ) - 1)) + 1 by ring, cot_pi_add_one]

lemma tendsto_pi_cot_add (z : ℂ) :
    Tendsto (fun M : ℕ => π * Complex.cot (π * (z + (M : ℂ) * τ))) atTop (𝓝 (-(π * I))) := by
  have hτ : 0 < τ.im := τ.2
  set ρ : ℝ := Real.exp (-2 * π * τ.im) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by rw [hρ, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [sub_neg_eq_add]
  have hgeom : Tendsto (fun M : ℕ => 2 * π * Real.exp (-2 * π * z.im) / (1 - ρ) * ρ ^ M)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
      (2 * π * Real.exp (-2 * π * z.im) / (1 - ρ))
  refine squeeze_zero' (Eventually.of_forall fun M => norm_nonneg _) ?_ hgeom
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, -z.im / τ.im + 1 ≤ N₀ := exists_nat_ge _
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun M hM => ?_⟩
  have hMN : (N₀ : ℝ) ≤ M := by exact_mod_cast hM
  have hIm : τ.im ≤ (z + (M : ℂ) * τ).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, zero_mul, add_zero]
    have h1 : -z.im / τ.im + 1 ≤ M := le_trans hN₀ hMN
    have h2 := (div_le_iff₀ hτ).mp (by linarith : -z.im / τ.im ≤ M - 1)
    nlinarith
  refine (norm_pi_cot_add_le hτ hIm).trans (le_of_eq ?_)
  have : Real.exp (-2 * π * (z + (M : ℂ) * τ).im) = Real.exp (-2 * π * z.im) * ρ ^ M := by
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, zero_mul, add_zero]
    rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  rw [this]; ring

lemma tendsto_pi_cot_sub (z : ℂ) :
    Tendsto (fun M : ℕ => π * Complex.cot (π * (z - (M : ℂ) * τ))) atTop (𝓝 (π * I)) := by
  have h := (tendsto_pi_cot_add τ (-z)).neg
  rw [neg_neg] at h
  refine h.congr fun M => ?_
  rw [show π * (-z + (M : ℂ) * τ) = -(π * (z - (M : ℂ) * τ)) by ring, cot_neg]
  ring

lemma hasSum_ser {z : ℂ} (hz : NotLat τ z) : HasSum (ser τ z) (pval τ z) :=
  EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 τ z hz

theorem weierstrassZeta_add_one {z : ℂ} (hz : NotLat τ z) :
    weierstrassZeta τ (z + 1) = weierstrassZeta τ z + G2 τ := by
  have h1 := hasSum_ser τ hz
  have h2 := hasSum_ser τ (by simpa using hz.add_intCast 1)
  have hser : ser τ (z + 1) = ser τ z := by
    funext m
    simp only [ser]
    rw [show z + 1 + ((m : ℂ) + 1) * τ = (z + ((m : ℂ) + 1) * τ) + 1 by ring, cot_pi_add_one,
      show z + 1 - ((m : ℂ) + 1) * τ = (z - ((m : ℂ) + 1) * τ) + 1 by ring, cot_pi_add_one]
  rw [hser] at h2
  have := h1.unique h2
  simp only [pval, cot_pi_add_one] at this
  linear_combination -this

lemma telescope (A B : ℕ → ℂ) (M : ℕ) :
    ∑ m ∈ Finset.range M, (A (m + 2) + B m) - ∑ m ∈ Finset.range M, (A (m + 1) + B (m + 1)) =
      (A (M + 1) - A 1) + (B 0 - B M) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linear_combination ih

theorem weierstrassZeta_add_tau {z : ℂ} (hz : NotLat τ z) :
    weierstrassZeta τ (z + τ) = weierstrassZeta τ z + ((τ : ℂ) * G2 τ - 2 * π * I) := by
  set A : ℕ → ℂ := fun k => π * Complex.cot (π * (z + (k : ℂ) * τ)) with hA
  set B : ℕ → ℂ := fun k => π * Complex.cot (π * (z - (k : ℂ) * τ)) with hB
  have h1 := hasSum_ser τ hz
  have h2 := hasSum_ser τ (by simpa using hz.add_intCast_mul 1)
  have hser1 : ser τ z = fun m => A (m + 1) + B (m + 1) := by
    funext m; simp only [ser, hA, hB]; push_cast; ring_nf
  have hser2 : ser τ (z + τ) = fun m => A (m + 2) + B m := by
    funext m; simp only [ser, hA, hB]; push_cast; ring_nf
  rw [hser1] at h1
  rw [hser2] at h2
  have t1 := h1.tendsto_sum_nat
  have t2 := h2.tendsto_sum_nat
  have t3 : Tendsto (fun M : ℕ => (A (M + 1) - A 1) + (B 0 - B M)) atTop
      (𝓝 ((-(π * I) - A 1) + (B 0 - π * I))) := by
    have tA : Tendsto (fun M : ℕ => A (M + 1)) atTop (𝓝 (-(π * I))) := by
      have := (tendsto_pi_cot_add τ z).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun M => ?_
      simp [hA, Function.comp]
    have tB : Tendsto (fun M : ℕ => B M) atTop (𝓝 (π * I)) := tendsto_pi_cot_sub τ z
    exact (tA.sub_const _).add (tB.const_sub _)
  have t4 : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, (A (m + 2) + B m) -
      ∑ m ∈ Finset.range M, (A (m + 1) + B (m + 1))) atTop
      (𝓝 (pval τ (z + τ) - pval τ z)) := t2.sub t1
  have heq := tendsto_nhds_unique (t4.congr (telescope A B)) t3
  have hA1 : A 1 = π * Complex.cot (π * (z + τ)) := by simp [hA]
  have hB0 : B 0 = π * Complex.cot (π * z) := by simp [hB]
  simp only [pval, hA1, hB0] at heq
  linear_combination heq

end EisensteinSeries

end

theorem EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul (τ : UpperHalfPlane) :
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + 1) =
          EisensteinSeries.weierstrassZeta τ z + EisensteinSeries.G2 τ) ∧
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + τ) =
          EisensteinSeries.weierstrassZeta τ z +
            ((τ : ℂ) * EisensteinSeries.G2 τ - 2 * π * Complex.I)) ∧
    (∀ (γ : SL(2, ℤ)) (z : ℂ),
        EisensteinSeries.weierstrassZeta (γ • τ) (z / UpperHalfPlane.denom γ τ) =
          UpperHalfPlane.denom γ τ * EisensteinSeries.weierstrassZeta τ z) :=
  ⟨fun _ hz => EisensteinSeries.weierstrassZeta_add_one τ hz,
    fun _ hz => EisensteinSeries.weierstrassZeta_add_tau τ hz,
    fun γ z => EisensteinSeries.weierstrassZeta_smul τ γ z⟩
