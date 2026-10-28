/-
  The Siegel unit's `SL(2, ℤ)`-multiplier and its differentiability.

  Two headlines, one shared engine. The first,
  `ModularCurve.siegelFun_specialLinearGroup_smul`, says that for `α ∈ SL(2, ℤ)` there is a
  twelfth root of unity `μ` with
  `siegelFun N r s (α • τ) = μ * siegelFun N (r α₀₀ + s α₁₀) (r α₀₁ + s α₁₁) τ` for all
  `r s τ`; `μ` is *constructed* as the product of the `S`/`T` multipliers along the
  decomposition of `α`, and `μ ^ 12 = 1` is the eta-quotient weight count. The second,
  `ModularCurve.SiegelUnit.differentiableOn_siegelFun`, is the pair
  `DifferentiableOn ℂ (siegelFun N r s) {0 < im} ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (siegelFun N r s)`.

  The engine, shared by both and written **once** here, is the q-product decomposition
  `siegelFun_eq : siegelFun N r s τ = pref N r s τ * sprod N r s τ`, the Jacobi-triple-product
  identity `theta_eq : jacobiTheta₂ (w N r s τ) τ = P τ * sprod N r s τ` (from the premise
  `jacobiTheta_two_eq_tprod`), the eta rewrite `eta_eq` for `P`, and the `S`/`T` laws. The pin
  carries this prelude twice, verbatim, in its two `S_` files (`SiegelSL2` in the first,
  `E97cSHol` in the second); here it is `private`, so the module's public surface is exactly the
  two headlines.

  Transcribed from the pin's
  `P2M/Sol/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean` (pinned `aa2d8b3`, 390 lines)
  and `P2M/Sol/S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean` (224 lines). The
  statements are the two `Theorems/` wrappers' verbatim; the proofs are the `S_` files' `solution`
  bodies with the wrapper `solution` theorems folded into the headlines. The pin's inner
  namespaces (`SiegelSL2`, `E97cSHol`), its `p2m_export`/`p2m_open` prelude and its `attribute
  [-simp]` prelude are not transcribed; the pin's `import Mathlib` is replaced by the modules its
  proof names, and its one premise (`ModularForms/JacobiThetaTripleProduct.lean`,
  `jacobiTheta_two_eq_tprod`) is imported rather than re-proved.

  A third headline, `ModularCurve.SiegelUnit.siegelFun_add_level`, adds the level-shift laws:
  `siegelFun N r (s + N) z = exp (π i (r - N) / N) * siegelFun N r s z` for `z : ℂ` and
  `siegelFun N (r + N) s τ = -exp (-(π i s / N)) * siegelFun N r s τ` for `τ : ℍ`. Its pin
  source is a third `S_` file (`SiegelPerE96`, 155 lines) whose `qa_add_level` family is the
  `qa`/`pref`/`sprod` level-shift engine; those six identities are public here under their
  pin names, and `qq_ne_zero` is added to the private engine as their only new ingredient.

  FLT provenance, pinned `aa2d8b3`:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_SiegelUnit_siegelFun_add_level.lean>
  spec-pin: Theorems/Thm_ModularCurve_siegelFun_specialLinearGroup_smul.lean
  spec-pin: P2M/Sol/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean
  spec-pin: P2M/Sol/S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_SiegelUnit_siegelFun_add_level.lean
  spec-pin: P2M/Sol/S_ModularCurve_SiegelUnit_siegelFun_add_level.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.Defs.SiegelFunction
import FLTForHuman.ModularForms.JacobiThetaTripleProduct
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped Manifold
open scoped Real MatrixGroups

namespace ModularCurve

/-! ### The shared q-product engine (private)

The pin carries this block twice, once per `S_` file, under the two inner namespaces
`SiegelSL2` (390) and `E97cSHol` (224). It is written once here, `private`, in the single
namespace `SiegelUnitEngine`; every declaration keeps its pin name, and the only change is that
the two pin namespace wrappers are unified. -/

namespace SiegelUnitEngine

private def qq (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

private def qa (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := cexp (2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ))

private def pref (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * τ)

private def sprod (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  (1 - qa N r s τ) * ∏' n : ℕ, ((1 - qq τ ^ (n + 1) * qa N r s τ) *
    (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹))

private theorem siegelFun_eq (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * sprod N r s τ := by
  unfold ModularCurve.siegelFun pref sprod qq qa; simp only [mul_assoc]

private theorem siegelFun_level_zero (r s : ℤ) (τ : ℂ) : ModularCurve.siegelFun 0 r s τ = 0 := by
  simp [ModularCurve.siegelFun]

private theorem qq_add_one (τ : ℂ) : qq (τ + 1) = qq τ := by
  unfold qq
  rw [show 2 * π * I * (τ + 1) = 2 * π * I * τ + 2 * π * I by ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

private theorem qa_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s (τ + 1) = qa N r (r + s) τ := by
  unfold qa
  push_cast
  ring_nf

private theorem pref_add_one (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) :
    pref N r s (τ + 1) = cexp (π * I / 6) * pref N r (r + s) τ := by
  unfold pref
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [neg_mul, neg_mul, mul_neg, neg_inj, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem sprod_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) : sprod N r s (τ + 1) = sprod N r (r + s) τ := by
  unfold sprod
  rw [qq_add_one, qa_add_one]

private theorem siegelFun_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s (τ + 1) = cexp (π * I / 6) * ModularCurve.siegelFun N r (r + s) τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelFun_level_zero]
  rw [siegelFun_eq, siegelFun_eq, pref_add_one N hN, sprod_add_one, mul_assoc]

private theorem norm_qq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qq τ‖ < 1 := by
  unfold qq
  rw [Complex.norm_exp]
  have : (2 * π * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

private theorem qa_ne_zero (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s τ ≠ 0 := Complex.exp_ne_zero _

private def P (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - qq τ ^ (n + 1))

private theorem multipliable_P {τ : ℂ} (hτ : 0 < τ.im) : Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow (norm_qq_lt_one hτ)

private theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k : ℕ) :
    Multipliable fun n : ℕ => 1 - q ^ (n + k) * c := by
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + k) * c)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_add]
    have := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right (‖q‖ ^ k * ‖c‖)
    refine this.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

private theorem multipliable_b {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ n * qa N r s τ := by
  simpa using multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 0

private theorem multipliable_b_succ {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * qa N r s τ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 1

private theorem multipliable_c {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ)⁻¹ 1

private def w (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + (1 - τ) / 2

private theorem jtp_term (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) (n : ℕ) :
    (1 - cexp (2 * π * I * (n + 1) * τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ)) =
      (1 - qq τ ^ (n + 1)) * ((1 - qq τ ^ n * qa N r s τ) *
        (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e1 : cexp (2 * π * I * (n + 1) * τ) = qq τ ^ (n + 1) := by
    rw [show 2 * π * I * (n + 1) * τ = ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) by push_cast; ring,
      Complex.exp_nat_mul, qq]
  have e2 : cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ) = -(qq τ ^ n * qa N r s τ) := by
    have : π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ =
        (n : ℂ) * (2 * π * I * τ) + 2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + π * I := by
      unfold w; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, qq, qa]
    ring
  have e3 : cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ) =
      -(qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := by
    have : π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ =
        ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) + -(2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ)) +
          -(π * I) := by
      unfold w; push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_neg, Complex.exp_pi_mul_I, qq, qa]
    ring
  rw [e1, e2, e3]; ring

private theorem theta_eq (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (w N r s τ) τ = P τ * sprod N r s τ := by
  rw [jacobiTheta_two_eq_tprod _ _ hτ, tprod_congr (jtp_term N hN r s τ)]
  have hP := multipliable_P hτ
  have hb := multipliable_b hτ N r s
  have hb1 := multipliable_b_succ hτ N r s
  have hc := multipliable_c hτ N r s
  have hbc : Multipliable fun n : ℕ => (1 - qq τ ^ n * qa N r s τ) *
      (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := (hb.hasProd.mul hc.hasProd).multipliable
  have h3 : ∏' n : ℕ, (1 - qq τ ^ n * qa N r s τ) =
      (1 - qq τ ^ 0 * qa N r s τ) * ∏' n : ℕ, (1 - qq τ ^ (n + 1) * qa N r s τ) :=
    tprod_eq_zero_mul' hb1
  rw [hP.tprod_mul hbc, hb.tprod_mul hc, h3, pow_zero, one_mul, mul_assoc, ← hb1.tprod_mul hc]
  simp only [P, sprod]

private theorem qParam_24 (τ : ℂ) : Function.Periodic.qParam 24 τ = cexp (π * I * τ / 12) := by
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

private theorem one_sub_eta_q (n : ℕ) (τ : ℂ) : 1 - ModularForm.eta_q n τ = 1 - qq τ ^ (n + 1) := by
  simp only [ModularForm.eta_q, Function.Periodic.qParam, qq]
  congr 3
  push_cast
  ring

private theorem eta_eq (τ : ℂ) : ModularForm.eta τ = cexp (π * I * τ / 12) * P τ := by
  unfold ModularForm.eta P
  rw [qParam_24, tprod_congr (fun n => one_sub_eta_q n τ)]

private theorem P_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : P τ ≠ 0 := by
  have h := ModularForm.eta_tprod_ne_zero (z := τ) hτ
  rwa [tprod_congr (fun n => one_sub_eta_q n τ)] at h

/-! ### The `S`-law of the q-product, and the `SL(2, ℤ)`-multiplier -/

private theorem sqrt_bridge {τ : ℂ} (hτ : 0 < τ.im) :
    (Complex.sqrt I)⁻¹ * Complex.sqrt τ = (-I * τ) ^ (1 / 2 : ℂ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hI : (-I : ℂ) ≠ 0 := by simp
  have hlog : Complex.log (-I * τ) = Complex.log (-I) + Complex.log τ := by
    rw [Complex.log_mul_eq_add_log_iff hI hτ0, Complex.arg_neg_I]
    have h1 : 0 ≤ Complex.arg τ := Complex.arg_nonneg_iff.mpr hτ.le
    have h2 : Complex.arg τ < π := Complex.arg_lt_pi_iff.mpr (Or.inr hτ.ne')
    have hπ := Real.pi_pos
    constructor <;> linarith
  have hcpow : (-I * τ) ^ (1 / 2 : ℂ) = Complex.sqrt (-I) * Complex.sqrt τ := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hI hτ0), hlog, add_mul, Complex.exp_add,
      Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero hI, Complex.cpow_def_of_ne_zero hτ0]
    norm_num
  have hc : ((√(2⁻¹) : ℝ) : ℂ) * ((√(2⁻¹) : ℝ) : ℂ) = 2⁻¹ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast
    ring
  have hprod : Complex.sqrt I * Complex.sqrt (-I) = 1 := by
    rw [Complex.sqrt_I, Complex.sqrt_neg_I]
    calc (((√(2⁻¹) : ℝ) : ℂ) * (1 + I)) * (((√(2⁻¹) : ℝ) : ℂ) * (1 - I))
          = (((√(2⁻¹) : ℝ) : ℂ) * ((√(2⁻¹) : ℝ) : ℂ)) * (1 - I ^ 2) := by ring
      _ = 1 := by rw [hc, Complex.I_sq]; norm_num
  rw [hcpow, inv_eq_of_mul_eq_one_right hprod]

private theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * τ) ^ (1 / 2 : ℂ) * ModularForm.eta τ := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [h, ← mul_assoc, sqrt_bridge τ.2]

private theorem P_S (τ : ℍ) :
    P (-1 / (τ : ℂ)) = (-I * τ) ^ (1 / 2 : ℂ) * cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) *
      cexp (π * I * τ / 12) * P τ := by
  have h := eta_S τ
  rw [eta_eq, eta_eq] at h
  have he : cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * cexp (π * I * (-1 / (τ : ℂ)) / 12) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc P (-1 / (τ : ℂ))
        = cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * (cexp (π * I * (-1 / (τ : ℂ)) / 12) * P (-1 / (τ : ℂ))) := by
          rw [← mul_assoc, he, one_mul]
    _ = _ := by rw [h]; ring

private theorem cpow_half_ne_zero (τ : ℍ) : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero (by simp) τ.ne_zero)

private theorem theta_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    jacobiTheta₂ (w N r s (-1 / (τ : ℂ))) (-1 / (τ : ℂ)) =
      (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * jacobiTheta₂ (w N s (-r) τ) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hA := cpow_half_ne_zero τ
  have hz : (w N s (-r) τ + τ) / τ = w N r s (-1 / (τ : ℂ)) := by
    unfold w; push_cast; field_simp; ring
  symm
  calc (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * jacobiTheta₂ (w N s (-r) τ) τ
        = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            jacobiTheta₂ (w N s (-r) τ + τ) τ := by
          rw [jacobiTheta₂_add_left']; ring
    _ = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            (1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
              jacobiTheta₂ ((w N s (-r) τ + τ) / τ) (-1 / τ)) := by
          rw [← jacobiTheta₂_functional_equation]
    _ = jacobiTheta₂ ((w N s (-r) τ + τ) / τ) (-1 / τ) := by
          have he : cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
              cexp (-π * I * (w N s (-r) τ + τ) ^ 2 / τ) = 1 := by
            rw [← Complex.exp_add]
            convert Complex.exp_zero using 2
            ring
          calc _ = ((-I * τ) ^ (1 / 2 : ℂ) * (1 / (-I * τ) ^ (1 / 2 : ℂ))) *
                (cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
                  cexp (-π * I * (w N s (-r) τ + τ) ^ 2 / τ)) *
                jacobiTheta₂ ((w N s (-r) τ + τ) / τ) (-1 / τ) := by ring
            _ = _ := by rw [he, mul_one_div_cancel hA, one_mul, one_mul]
    _ = _ := by rw [hz]

private theorem sprod_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    sprod N r s (-1 / (τ : ℂ)) =
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) * sprod N s (-r) τ := by
  have hτ' : 0 < (-1 / (τ : ℂ)).im := by
    have : -1 / (τ : ℂ) = (-(τ : ℂ))⁻¹ := by rw [inv_neg, neg_div, one_div]
    rw [this]; exact τ.im_inv_neg_coe_pos
  have h1 := theta_eq N hN r s hτ'
  have h2 := theta_eq N hN s (-r) τ.2
  have h3 := theta_S N hN r s τ
  rw [h1, h2, P_S] at h3

  have hne : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) *
      cexp (π * I * τ / 12) * P τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (cpow_half_ne_zero τ) (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)) (P_ne_zero τ.2)
  refine mul_left_cancel₀ hne ?_
  rw [h3]
  have he : cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * cexp (π * I * τ / 12) *
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) =
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) * cexp (-π * I * (τ + 2 * w N s (-r) τ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * (P τ * sprod N s (-r) τ)
        = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * (cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            cexp (-π * I * (τ + 2 * w N s (-r) τ))) * P τ * sprod N s (-r) τ := by ring
    _ = _ := by rw [← he]; ring

private theorem pref_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    pref N r s (-1 / (τ : ℂ)) *
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) = -I * pref N s (-r) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hI : -I = cexp (-(π / 2 * I)) := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  unfold pref
  rw [hI]
  simp only [neg_mul, mul_neg, neg_inj, ← Complex.exp_add]
  congr 1
  unfold w
  push_cast
  field_simp
  ring

private theorem siegelFun_S (N : ℕ) (r s : ℤ) (τ : ℍ) :
    ModularCurve.siegelFun N r s (-1 / (τ : ℂ)) = -I * ModularCurve.siegelFun N s (-r) τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelFun_level_zero]
  rw [siegelFun_eq, siegelFun_eq, sprod_S N hN, ← mul_assoc, pref_S N hN, mul_assoc]

private def Law (N : ℕ) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
    ModularCurve.siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
      μ * ModularCurve.siegelFun N
        (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
        (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ)

private theorem law_one (N : ℕ) : Law N 1 :=
  ⟨1, one_pow _, fun r s τ => by simp⟩

private theorem law_T (N : ℕ) : Law N ModularGroup.T := by
  refine ⟨cexp (π * I / 6), ?_, fun r s τ => ?_⟩
  · rw [← Complex.exp_nat_mul]
    convert Complex.exp_two_pi_mul_I using 2
    push_cast; ring
  · rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
    simp only [ModularGroup.coe_T, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    push_cast
    rw [add_comm (1 : ℂ), siegelFun_add_one]
    congr 2 <;> ring

private theorem law_S (N : ℕ) : Law N ModularGroup.S := by
  refine ⟨-I, by rw [neg_pow, show (12 : ℕ) = 2 * 6 by rfl, pow_mul, pow_mul, Complex.I_sq]; norm_num,
    fun r s τ => ?_⟩
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  simp only [ModularGroup.coe_S, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  rw [show (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) by rw [inv_neg, neg_div, one_div], siegelFun_S]
  congr 2 <;> ring

private theorem law_mul {N : ℕ} {α β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hα : Law N α) (hβ : Law N β) :
    Law N (α * β) := by
  obtain ⟨μ, hμ, hα⟩ := hα
  obtain ⟨ν, hν, hβ⟩ := hβ
  refine ⟨μ * ν, by rw [mul_pow, hμ, hν, one_mul], fun r s τ => ?_⟩
  rw [mul_smul, hα, hβ, mul_assoc]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  congr 3 <;> ring

private theorem law_inv {N : ℕ} {α : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hα : Law N α) : Law N α⁻¹ := by
  obtain ⟨μ, hμ, hα⟩ := hα
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ
  refine ⟨μ⁻¹, by rw [inv_pow, hμ, inv_one], fun r s τ => ?_⟩
  have hdet : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := α.det_coe
    rwa [Matrix.det_fin_two] at this
  set r' : ℤ := r * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
    s * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hr'
  set s' : ℤ := r * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
    s * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hs'
  have h := hα r' s' (α⁻¹ • τ)
  rw [smul_inv_smul] at h
  have h1 : r' * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s' * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by
    simp only [hr', hs', Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    linear_combination r * hdet
  have h2 : r' * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s' * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = s := by
    simp only [hr', hs', Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    linear_combination s * hdet
  rw [h1, h2] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]

private theorem law_all (N : ℕ) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Law N α := by
  have hmem : α ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  refine Subgroup.closure_induction (fun x hx => ?_) (law_one N) (fun x y _ _ hx hy => law_mul hx hy)
    (fun x _ hx => law_inv hx) hmem
  rcases hx with rfl | rfl
  · exact law_S N
  · exact law_T N

/-! ### The addition laws in the level: `s ↦ s + N` and `r ↦ r + N`

The pin's `S_ModularCurve_SiegelUnit_siegelFun_add_level.lean` (`SiegelPerE96`) states these
six identities beside the engine; `qa`/`pref`/`sprod` are the engine's factors, so the six keep
their pin names, their pin statements and their pin proofs here, and the headline
`SiegelUnit.siegelFun_add_level` is the pair of level-shifts. -/

private theorem qq_ne_zero (τ : ℂ) : qq τ ≠ 0 := Complex.exp_ne_zero _

theorem qa_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    qa N r (s + N) z = qa N r s z := by
  unfold qa
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [show 2 * (π : ℂ) * I * ((r : ℂ) * z + ((s : ℂ) + (N : ℂ))) / (N : ℂ)
      = 2 * π * I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ) + 2 * π * I by field_simp; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem pref_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    pref N r (s + N) z = cexp (π * I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * pref N r s z := by
  unfold pref
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [show ∀ x y u : ℂ, cexp u * (-cexp x * cexp y) = -cexp (u + x) * cexp y from
    fun x y u => by rw [Complex.exp_add]; ring]
  congr 3
  push_cast
  field_simp
  ring

theorem sprod_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    sprod N r (s + N) z = sprod N r s z := by
  unfold sprod
  simp only [qa_add_level N hN]

theorem qa_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    qa N (r + N) s z = qq z * qa N r s z := by
  unfold qa qq
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

theorem pref_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    pref N (r + N) s z = pref N r s z * (qa N r s z * cexp (-(π * I * (s : ℂ) / (N : ℂ)))) := by
  unfold pref qa
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [show ∀ x y u v : ℂ, -cexp x * cexp y * (cexp u * cexp v) = -cexp (x + y + u + v) from
      fun x y u v => by rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring,
    show ∀ x y : ℂ, -cexp x * cexp y = -cexp (x + y) from fun x y => by rw [Complex.exp_add]; ring]
  congr 2
  push_cast
  field_simp
  ring

theorem sprod_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    sprod N (r + N) s τ = -(qa N r s τ)⁻¹ * sprod N r s τ := by
  have hq := norm_qq_lt_one hτ
  set q := qq τ with hqdef
  set w := qa N r s τ with hwdef
  have hq0 : q ≠ 0 := qq_ne_zero τ
  have hw0 : w ≠ 0 := qa_ne_zero N r s τ
  unfold sprod
  simp only [qa_add_level_left N hN, ← hqdef, ← hwdef]

  have ht : ∀ n : ℕ, (1 - q ^ (n + 1) * (q * w)) * (1 - q ^ (n + 1) * (q * w)⁻¹)
      = (1 - q ^ (n + 1 + 1) * w) * (1 - q ^ n * w⁻¹) := by
    intro n
    rw [mul_inv, pow_succ q (n + 1), pow_succ q n]
    field_simp
  rw [tprod_congr ht]

  have hA2 : Multipliable fun n : ℕ => 1 - q ^ (n + 1 + 1) * w := by
    simpa [add_assoc] using multipliable_one_sub_pow_mul hq w 2
  have hA1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * w := multipliable_one_sub_pow_mul hq w 1
  have hB1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * w⁻¹ := multipliable_one_sub_pow_mul hq w⁻¹ 1
  have hB0 : Multipliable fun n : ℕ => 1 - q ^ n * w⁻¹ := by
    simpa using multipliable_one_sub_pow_mul hq w⁻¹ 0

  rw [hA2.tprod_mul hB0, hA1.tprod_mul hB1,
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ (n + 1) * w) hA2,
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ n * w⁻¹) hB1]
  simp only [zero_add, pow_one, pow_zero, one_mul]
  field_simp
  ring

/-! ### Differentiability of the q-product -/

private theorem differentiable_w (N : ℕ) (r s : ℤ) : Differentiable ℂ (w N r s) := by
  unfold w; fun_prop

private theorem differentiable_pref (N : ℕ) (r s : ℤ) : Differentiable ℂ (pref N r s) := by
  unfold pref; fun_prop

private theorem differentiableAt_theta_w (N : ℕ) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun z => jacobiTheta₂ (w N r s z) z) τ := by
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (w N r s τ, τ) :=
    (hasFDerivAt_jacobiTheta₂ (w N r s τ) hτ).differentiableAt
  have h2 : DifferentiableAt ℂ (fun z => (w N r s z, z)) τ :=
    ((differentiable_w N r s) τ).prodMk differentiableAt_id
  have h3 : DifferentiableAt ℂ ((fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) ∘ (fun z => (w N r s z, z))) τ :=
    DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f := fun z => (w N r s z, z)) τ h1 h2
  exact h3

private theorem differentiableAt_P {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ P τ := by
  have h := ModularForm.differentiableAt_eta_tprod (z := τ) hτ
  have hfun : (fun x => ∏' n, (1 - ModularForm.eta_q n x)) = P := by
    funext x
    exact tprod_congr (fun n => one_sub_eta_q n x)
  rwa [hfun] at h

private theorem siegelFun_eq_theta (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * (jacobiTheta₂ (w N r s τ) τ / P τ) := by
  rw [siegelFun_eq, theta_eq N hN r s hτ, mul_div_cancel_left₀ _ (P_ne_zero hτ)]

private theorem differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) {z : ℂ | 0 < z.im} := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [siegelFun_level_zero]
    exact differentiableOn_const 0
  · have h : DifferentiableOn ℂ (fun z => pref N r s z * (jacobiTheta₂ (w N r s z) z / P z)) {z : ℂ | 0 < z.im} :=
      fun z hz => (((differentiable_pref N r s) z).mul
        ((differentiableAt_theta_w N r s hz).div (differentiableAt_P hz) (P_ne_zero hz))).differentiableWithinAt
    exact h.congr fun z hz => siegelFun_eq_theta N hN r s hz

private theorem mdifferentiable_siegelFun (N : ℕ) (r s : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => ModularCurve.siegelFun N r s (τ : ℂ)) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have hd : DifferentiableAt ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) (τ : ℂ) :=
    (differentiableOn_siegelFun N r s).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp only [Function.comp_apply, id_eq] at hz
  simp only [Function.comp_apply, hz]

end SiegelUnitEngine

/-! ### The two headlines -/

theorem siegelFun_specialLinearGroup_smul (N : ℕ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * siegelFun N (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ) :=
  SiegelUnitEngine.law_all N α

namespace SiegelUnit

theorem differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ)) :=
  ⟨SiegelUnitEngine.differentiableOn_siegelFun N r s,
    SiegelUnitEngine.mdifferentiable_siegelFun N r s⟩

/-! ### The addition law in the level -/

theorem siegelFun_add_level (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine ⟨fun z => ?_, fun τ => ?_⟩ <;> simp [SiegelUnitEngine.siegelFun_level_zero]
  refine ⟨fun z => ?_, fun τ => ?_⟩
  · rw [SiegelUnitEngine.siegelFun_eq, SiegelUnitEngine.siegelFun_eq,
      SiegelUnitEngine.pref_add_level N hN, SiegelUnitEngine.sprod_add_level N hN, mul_assoc]
  · rw [SiegelUnitEngine.siegelFun_eq, SiegelUnitEngine.siegelFun_eq,
      SiegelUnitEngine.pref_add_level_left N hN, SiegelUnitEngine.sprod_add_level_left N hN r s τ.2]
    have hw : SiegelUnitEngine.qa N r s (τ : ℂ) ≠ 0 := SiegelUnitEngine.qa_ne_zero N r s τ
    field_simp

end SiegelUnit

end ModularCurve
