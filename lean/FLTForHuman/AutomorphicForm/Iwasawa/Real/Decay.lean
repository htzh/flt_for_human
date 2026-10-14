/-
  The real Iwasawa decay engine.

  The generic one-parameter-group smoothness machinery (`AutoSmooth`), the tower
  composition estimate (`ScalarMajorant.Composition`), the real-place symbol/decay
  development (`RealDecay`) and the uniform-in-`g`/`u` extension (`B2bRUnif`).
  The pin's local `FourierDecay` block is not re-transcribed: it is the landed
  `FLTForHuman.MeasureTheory.FourierDecay`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean
-/
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import FLTForHuman.AutomorphicForm.Iwasawa.Real.Core

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Real VectorFourier
open scoped ContDiff FourierTransform Nat

namespace AutomorphicForm.RealIwasawa.AutoSmooth


variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

-- pin: IsOneParamGroup (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:525)
structure IsOneParamGroup (R : ℝ → A) : Prop where
  map_zero : R 0 = 1
  map_add : ∀ s t : ℝ, R (s + t) = R s * R t
  continuous : Continuous R

-- pin: prim (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:530)
def prim (R : ℝ → A) (t : ℝ) : A := ∫ u in (0 : ℝ)..t, R u

namespace IsOneParamGroup

variable {R : ℝ → A}

-- pin: hasDerivAt_prim (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:536)
theorem hasDerivAt_prim (hR : IsOneParamGroup R) (t : ℝ) : HasDerivAt (prim R) (R t) t :=
  (hR.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

-- pin: deriv_prim (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:539)
theorem deriv_prim (hR : IsOneParamGroup R) : deriv (prim R) = R :=
  funext fun t => (hR.hasDerivAt_prim t).deriv

-- pin: differentiable_prim (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:542)
theorem differentiable_prim (hR : IsOneParamGroup R) : Differentiable ℝ (prim R) :=
  fun t => (hR.hasDerivAt_prim t).differentiableAt

-- pin: mul_prim (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:545)
theorem mul_prim (hR : IsOneParamGroup R) (t ε : ℝ) :
    R t * prim R ε = prim R (t + ε) - prim R t := by
  have h1 : R t * prim R ε = ∫ u in (0 : ℝ)..ε, R t * R u := by
    have h := (ContinuousLinearMap.mul ℝ A (R t)).intervalIntegral_comp_comm
      (hR.continuous.intervalIntegrable (μ := volume) 0 ε)
    simpa [prim] using h.symm
  have h2 : (∫ u in (0 : ℝ)..ε, R t * R u) = ∫ u in (0 : ℝ)..ε, R (t + u) := by
    congr 1
    funext u
    rw [hR.map_add]
  have h3 : (∫ u in (0 : ℝ)..ε, R (t + u)) = ∫ v in t..t + ε, R v := by
    rw [intervalIntegral.integral_comp_add_left R t, add_zero]
  have h4 : prim R (t + ε) - prim R t = ∫ v in t..t + ε, R v := by
    unfold prim
    exact intervalIntegral.integral_interval_sub_left (hR.continuous.intervalIntegrable _ _)
      (hR.continuous.intervalIntegrable _ _)
  rw [h1, h2, h3, h4]

-- pin: exists_isUnit_prim (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:563)
theorem exists_isUnit_prim (hR : IsOneParamGroup R) : ∃ ε : ℝ, 0 < ε ∧ IsUnit (prim R ε) := by
  have hc : ContinuousAt R 0 := hR.continuous.continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hball⟩ := hc (1 / 2) (by norm_num)
  have hε0 : (0 : ℝ) < δ / 2 := by positivity
  refine ⟨δ / 2, hε0, ?_⟩
  set ε : ℝ := δ / 2 with hεdef

  have hbound : ‖∫ u in (0 : ℝ)..ε, (R u - 1)‖ ≤ 1 / 2 * |ε - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hε0.le] at hu
    have hud : dist u 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]
      linarith [hu.2]
    have h := hball hud
    rw [hR.map_zero, dist_eq_norm] at h
    exact h.le
  have hsplit : (∫ u in (0 : ℝ)..ε, (R u - 1)) = prim R ε - ε • (1 : A) := by
    rw [intervalIntegral.integral_sub (hR.continuous.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    rfl

  have hx : ‖(1 : A) - ε⁻¹ • prim R ε‖ < 1 := by
    have hrw : (1 : A) - ε⁻¹ • prim R ε = -(ε⁻¹ • (prim R ε - ε • (1 : A))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hε0.ne', one_smul, neg_sub]
    rw [hrw, norm_neg, norm_smul, ← hsplit, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
    calc ε⁻¹ * ‖∫ u in (0 : ℝ)..ε, (R u - 1)‖ ≤ ε⁻¹ * (1 / 2 * |ε - 0|) := by gcongr
      _ = 1 / 2 := by rw [sub_zero, abs_of_pos hε0]; field_simp
      _ < 1 := by norm_num
  have hu : IsUnit (ε⁻¹ • prim R ε) := by
    have h := (Units.oneSub ((1 : A) - ε⁻¹ • prim R ε) hx).isUnit
    rwa [Units.val_oneSub, sub_sub_cancel] at h
  have hεA : IsUnit (algebraMap ℝ A ε) := (isUnit_iff_ne_zero.2 hε0.ne').map (algebraMap ℝ A)
  have hrw : prim R ε = algebraMap ℝ A ε * (ε⁻¹ • prim R ε) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hε0.ne', one_smul]
  rw [hrw]
  exact hεA.mul hu

-- pin: eq_sub_mul_inv (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:602)
theorem eq_sub_mul_inv (hR : IsOneParamGroup R) {ε : ℝ} (u : Aˣ) (hu : (u : A) = prim R ε) (t : ℝ) :
    R t = (prim R (t + ε) - prim R t) * (u⁻¹ : Aˣ) := by
  rw [← hR.mul_prim t ε, ← hu, Units.mul_inv_cancel_right]

-- pin: contDiff_nat (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:606)
theorem contDiff_nat (hR : IsOneParamGroup R) : ∀ n : ℕ, ContDiff ℝ n R := by
  obtain ⟨ε, _hε, hunit⟩ := hR.exists_isUnit_prim
  obtain ⟨u, hu⟩ := hunit
  have hformula : R = fun t => (prim R (t + ε) - prim R t) * ((u⁻¹ : Aˣ) : A) :=
    funext (hR.eq_sub_mul_inv u hu)
  intro n
  induction n with
  | zero => rw [Nat.cast_zero]; exact contDiff_zero.2 hR.continuous
  | succ n ih =>
    have hP : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (prim R) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨hR.differentiable_prim, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
      rw [hR.deriv_prim]
      exact ih
    rw [Nat.cast_succ, hformula]
    exact ((hP.comp (contDiff_id.add contDiff_const)).sub hP).mul contDiff_const

-- pin: contDiff (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:623)
theorem contDiff (hR : IsOneParamGroup R) : ContDiff ℝ ∞ R :=
  contDiff_infty.2 hR.contDiff_nat

-- pin: differentiable (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:626)
theorem differentiable (hR : IsOneParamGroup R) : Differentiable ℝ R :=
  (hR.contDiff_nat 1).differentiable (by simp)

-- pin: deriv_eq_mul (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:629)
theorem deriv_eq_mul (hR : IsOneParamGroup R) (t : ℝ) : deriv R t = R t * deriv R 0 := by
  have hd := hR.differentiable
  have heq : (fun s => R (t + s)) = fun s => R t * R s := funext fun s => hR.map_add t s
  calc deriv R t = deriv (fun s => R (t + s)) 0 := by rw [deriv_comp_const_add, add_zero]
    _ = deriv (fun s => R t * R s) 0 := by rw [heq]
    _ = R t * deriv R 0 := deriv_const_mul _ (hd 0)

-- pin: deriv_eq_mul' (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:636)
theorem deriv_eq_mul' (hR : IsOneParamGroup R) (t : ℝ) : deriv R t = deriv R 0 * R t := by
  have hd := hR.differentiable
  have heq : (fun s => R (s + t)) = fun s => R s * R t := funext fun s => hR.map_add s t
  calc deriv R t = deriv (fun s => R (s + t)) 0 := by rw [deriv_comp_add_const, zero_add]
    _ = deriv (fun s => R s * R t) 0 := by rw [heq]
    _ = deriv R 0 * R t := deriv_mul_const (hd 0) _

-- pin: commute_deriv_zero (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:643)
theorem commute_deriv_zero (hR : IsOneParamGroup R) (t : ℝ) : Commute (R t) (deriv R 0) := by
  have h := hR.deriv_eq_mul t
  rw [hR.deriv_eq_mul' t] at h
  exact h.symm

-- pin: iteratedDeriv_eq (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:648)
theorem iteratedDeriv_eq (hR : IsOneParamGroup R) (k : ℕ) :
    iteratedDeriv k R = fun t => R t * deriv R 0 ^ k := by
  induction k with
  | zero => funext t; simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_mul_const (hR.differentiable t), hR.deriv_eq_mul t, mul_assoc, ← pow_succ']

-- pin: norm_iteratedDeriv_le (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:657)
theorem norm_iteratedDeriv_le (hR : IsOneParamGroup R) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k R t‖ ≤ ‖R t‖ * ‖deriv R 0‖ ^ k := by
  rw [hR.iteratedDeriv_eq k]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le' _ hk)

-- pin: norm_iteratedDeriv_le_of_bound (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:664)
theorem norm_iteratedDeriv_le_of_bound (hR : IsOneParamGroup R) {S : Set ℝ} {M : ℝ}
    (hM : ∀ t ∈ S, ‖R t‖ ≤ M) (k : ℕ) (t : ℝ) (ht : t ∈ S) :
    ‖iteratedDeriv k R t‖ ≤ M * ‖deriv R 0‖ ^ k :=
  (hR.norm_iteratedDeriv_le k t).trans (by gcongr; exact hM t ht)

end IsOneParamGroup

-- pin: contDiff_of_continuous_addChar (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:672)
theorem contDiff_of_continuous_addChar (χ : ℝ → ℂ) (h0 : χ 0 = 1) (hadd : ∀ s t, χ (s + t) = χ s * χ t)
    (hc : Continuous χ) : ContDiff ℝ ∞ χ :=
  (IsOneParamGroup.mk h0 hadd hc).contDiff

-- pin: deriv_continuous_addChar (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:676)
theorem deriv_continuous_addChar (χ : ℝ → ℂ) (h0 : χ 0 = 1) (hadd : ∀ s t, χ (s + t) = χ s * χ t)
    (hc : Continuous χ) (t : ℝ) : deriv χ t = χ t * deriv χ 0 :=
  (IsOneParamGroup.mk h0 hadd hc).deriv_eq_mul t


-- pin: isOneParamGroup_cexp (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:683)
theorem isOneParamGroup_cexp (c : ℂ) : IsOneParamGroup (fun t : ℝ => Complex.exp (t * c)) := by
  refine ⟨by simp, fun s t => ?_, Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)⟩
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- pin: deriv_cexp_zero (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:690)
theorem deriv_cexp_zero (c : ℂ) : deriv (fun t : ℝ => Complex.exp (t * c)) 0 = c := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w * c))
      (Complex.exp ((((0 : ℝ) : ℂ)) * c) * (1 * c)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' ((0 : ℝ) : ℂ)).mul_const c).cexp
  have h2 := h1.comp_ofReal
  rw [h2.deriv]
  simp



end AutomorphicForm.RealIwasawa.AutoSmooth

namespace AutomorphicForm.RealIwasawa.ScalarMajorant

section Composition

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

-- pin: norm_iteratedFDeriv_comp_log_rad_le (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:827)
theorem norm_iteratedFDeriv_comp_log_rad_le (hg : g.det ≠ 0) {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hΨd : ∀ (j : ℕ) (t : ℝ), ‖iteratedDeriv j Ψ t‖ ≤ κ ^ j * ‖Ψ t‖)
    {n i : ℕ} (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u => Ψ (Real.log (rad g u))) u‖
      ≤ n ! * (max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖) * towerD g n ^ n := by
  have hC : ∀ j, j ≤ i → ‖iteratedFDeriv ℝ j Ψ (Real.log (rad g u))‖
      ≤ max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖ := by
    intro j hj
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine (hΨd j _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (pow_le_pow_left₀ hκ (le_max_right 1 κ) j).trans (pow_le_pow_right₀ (le_max_left 1 κ) (hj.trans hin))
  have hD : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j (fun u => Real.log (rad g u)) u‖ ≤ towerD g n ^ j :=
    fun j hj1 hji => norm_iteratedFDeriv_log_rad_le hg hj1 (hji.trans hin) u
  have h := norm_iteratedFDeriv_comp_le (g := Ψ) (f := fun u => Real.log (rad g u)) (n := i)
    hΨ (contDiff_log_rad hg) (by exact_mod_cast le_top) u hC hD
  rw [Function.comp_def] at h
  refine h.trans ?_
  have hfac : (i ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le hin
  have hpow : towerD g n ^ i ≤ towerD g n ^ n := pow_le_pow_right₀ (one_le_towerD n) hin
  have h0 : 0 ≤ max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖ := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfac h0) hpow (pow_nonneg (towerD_pos n).le _) (by positivity)

end Composition

end AutomorphicForm.RealIwasawa.ScalarMajorant

namespace AutomorphicForm.RealIwasawa.RealDecay

open AutomorphicForm.RealIwasawa.AutoSmooth AutomorphicForm.RealIwasawa.ScalarMajorant

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

-- pin: Ψ (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:933)
def Ψ (u : ℂ) (t : ℝ) : ℂ := Complex.exp (↑t * (-u))

-- pin: isOneParamGroup_Ψ (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:935)
theorem isOneParamGroup_Ψ (u : ℂ) : IsOneParamGroup (Ψ u) := isOneParamGroup_cexp (-u)

-- pin: deriv_Ψ_zero (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:937)
theorem deriv_Ψ_zero (u : ℂ) : deriv (Ψ u) 0 = -u := deriv_cexp_zero (-u)

-- pin: norm_Ψ (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:939)
theorem norm_Ψ (u : ℂ) (t : ℝ) : ‖Ψ u t‖ = Real.exp (-u.re * t) := by
  unfold Ψ
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    zero_mul, sub_zero]
  ring

-- pin: norm_iteratedDeriv_Ψ_le (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:947)
theorem norm_iteratedDeriv_Ψ_le (u : ℂ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (Ψ u) t‖ ≤ ‖u‖ ^ j * ‖Ψ u t‖ := by
  have h := (isOneParamGroup_Ψ u).norm_iteratedDeriv_le j t
  rw [deriv_Ψ_zero, norm_neg] at h
  calc ‖iteratedDeriv j (Ψ u) t‖ ≤ ‖Ψ u t‖ * ‖u‖ ^ j := h
    _ = ‖u‖ ^ j * ‖Ψ u t‖ := mul_comm _ _

-- pin: norm_Ψ_log_rad (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:954)
theorem norm_Ψ_log_rad (hg : g.det ≠ 0) (u : ℂ) (x : ℝ) :
    ‖Ψ u (Real.log (rad g x))‖ = rad g x ^ (-u.re) := by
  rw [norm_Ψ, Real.rpow_def_of_pos (rad_pos hg x), mul_comm (-u.re)]

-- pin: weight_eq (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:958)
theorem weight_eq (hg : g.det ≠ 0) (u : ℂ) (x : ℝ) :
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))
      = Ψ u (Real.log (rad g x)) := by
  rw [← rad_eq_sqrt g x]
  have hr := rad_pos hg x
  unfold Ψ
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), ← Complex.ofReal_log hr.le]

-- pin: weightFun_eq (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:966)
theorem weightFun_eq (hg : g.det ≠ 0) (u : ℂ) :
    (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)))
      = fun x => Ψ u (Real.log (rad g x)) :=
  funext (weight_eq hg u)

-- pin: contDiff_Ψ_log_rad (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:971)
theorem contDiff_Ψ_log_rad (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞ (fun x => Ψ u (Real.log (rad g x))) :=
  (isOneParamGroup_Ψ u).contDiff.comp (contDiff_log_rad hg)

-- pin: contDiff_weight (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:975)
theorem contDiff_weight (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞
      (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) := by
  rw [weightFun_eq hg u]
  exact contDiff_Ψ_log_rad hg u

-- pin: norm_iteratedFDeriv_Ψ_log_rad_le (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:981)
theorem norm_iteratedFDeriv_Ψ_log_rad_le (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x => Ψ u (Real.log (rad g x))) x‖
      ≤ (n ! * max 1 ‖u‖ ^ n * towerD g n ^ n) * rad g x ^ (-u.re) := by
  have h := norm_iteratedFDeriv_comp_log_rad_le (g := g) hg (Ψ := Ψ u) (isOneParamGroup_Ψ u).contDiff
    (κ := ‖u‖) (norm_nonneg u) (norm_iteratedDeriv_Ψ_le u) (le_refl n) x
  rw [norm_Ψ_log_rad hg u x] at h
  calc ‖iteratedFDeriv ℝ n (fun x => Ψ u (Real.log (rad g x))) x‖
      ≤ n ! * (max 1 ‖u‖ ^ n * rad g x ^ (-u.re)) * towerD g n ^ n := h
    _ = (n ! * max 1 ‖u‖ ^ n * towerD g n ^ n) * rad g x ^ (-u.re) := by ring

-- pin: exists_bound_iteratedFDeriv_weight (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:991)
theorem exists_bound_iteratedFDeriv_weight (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n
          (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        ≤ C * rad g x ^ (-u.re) := by
  refine ⟨n ! * max 1 ‖u‖ ^ n * towerD g n ^ n, ?_, fun x => ?_⟩
  · have h1 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have h2 : (0 : ℝ) < max 1 ‖u‖ ^ n := pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) n
    exact mul_pos (mul_pos h1 h2) (pow_pos (towerD_pos n) n)
  · rw [weightFun_eq hg u]
    exact norm_iteratedFDeriv_Ψ_log_rad_le hg u n x

-- pin: rad_rpow_neg_le_one_add_sq (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1003)
theorem rad_rpow_neg_le_one_add_sq (hg : g.det ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    rad g x ^ (-κ) ≤ radFloor g ^ (-κ / 2) * (1 + ‖x‖ ^ 2) ^ (-κ / 2) := by
  have hF := radFloor_pos hg
  have hr := rad_pos hg x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2]
  have h1 : rad g x ^ (-κ) = (rad g x ^ 2) ^ (-κ / 2) := by
    rw [← Real.rpow_natCast (rad g x) 2, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  rw [h1, ← Real.mul_rpow hF.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (radFloor_mul_le_rad_sq hg x) (by linarith)

-- pin: integrable_rpow_neg_rad (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1017)
theorem integrable_rpow_neg_rad (hg : g.det ≠ 0) {κ : ℝ} (hκ : 1 < κ) :
    Integrable (fun x => rad g x ^ (-κ)) (volume : Measure ℝ) := by
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-κ / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (μ := volume) (by rw [Module.finrank_self]; exact_mod_cast hκ)
  refine (hint.const_mul (radFloor g ^ (-κ / 2))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((contDiff_rad hg).continuous.rpow_const fun x => Or.inl (rad_pos hg x).ne').aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (rad_pos hg x).le _)]
    exact rad_rpow_neg_le_one_add_sq hg (by linarith) x

-- pin: exists_bound_iteratedFDeriv_weight_mul (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1026)
theorem exists_bound_iteratedFDeriv_weight_mul (hg : g.det ≠ 0) (u : ℂ)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n
          (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))
            * P x) x‖
        ≤ C * rad g x ^ (-u.re) := by
  intro n
  choose Cf hCf using fun i => exists_bound_iteratedFDeriv_weight hg u i
  choose Ch hCh using hPB
  have hpos : (0:ℝ) < ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Ch (n - i) := by
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    have h1 : (0:ℝ) < (n.choose i : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    exact mul_pos (mul_pos h1 (hCf i).1) (hCh (n - i)).1
  refine ⟨_, hpos, fun x => ?_⟩
  have hrad := rad_pos hg x
  refine (norm_iteratedFDeriv_mul_le (contDiff_weight hg u) hPC x
    (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  calc (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i
            (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        * ‖iteratedFDeriv ℝ (n - i) P x‖
      ≤ (n.choose i : ℝ) * (Cf i * rad g x ^ (-u.re)) * Ch (n - i) := by
        gcongr
        · exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hCf i).1.le (Real.rpow_nonneg hrad.le _))
        · exact (hCf i).2 x
        · exact (hCh (n - i)).2 x
    _ = (n.choose i : ℝ) * Cf i * Ch (n - i) * rad g x ^ (-u.re) := by ring

-- pin: norm_fourierIntegral_cpow_radR_mul_le_polyDecay (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1060)
theorem norm_fourierIntegral_cpow_radR_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  set f : ℝ → ℂ := fun x =>
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x with hfdef

  obtain ⟨CB, hCB⟩ := Classical.axiom_of_choice
    (fun n => exists_bound_iteratedFDeriv_weight_mul hg u hPC hPB n)
  have hintr : Integrable (fun x => rad g x ^ (-u.re)) volume :=
    integrable_rpow_neg_rad hg hu
  have hfC : ContDiff ℝ ∞ f := (contDiff_weight hg u).mul hPC
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (CB j)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (hCB j).2 x

  have key := MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive L
    (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume
  have hMN0 : (0:ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)

  have hfint : Integrable f volume := by
    refine (hintr.const_mul (CB 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 := (hCB 0).2 x
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume
  have hM00 : (0:ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  refine ⟨(M0 * 2 ^ N + MN * (2 / c) ^ N) + 1, by positivity, fun ξ => ?_⟩
  have hξ0 : (0:ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0:ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0:ℝ) < (1 + ‖ξ‖) ^ (-(N:ℝ)) := Real.rpow_pos_of_pos h1ξ _
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  ·
    have hbd : (2:ℝ) ^ (-(N:ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith)
        (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0 : ℝ) = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := by
      rw [mul_assoc, show ((2:ℝ)^N : ℝ) = (2:ℝ)^(N:ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ))
        ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hbd
        (mul_nonneg hM00 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0 * 2 ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hMN0
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0 := hstep1
      _ = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := hstep2
      _ ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := hstep3
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  ·
    have hkey := key ξ
    have hcξ : (0:ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1:ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N:ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N:ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast,
          ← inv_pow, inv_div]
      rw [hp1]
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)
      exact Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep4 : (MN * (2 / c) ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hM00 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := hdiv
      _ ≤ MN * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ))) :=
          mul_le_mul_of_nonneg_left hcmp hMN0
      _ = MN * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by ring
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

-- pin: radR_eq_rad (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1157)
theorem radR_eq_rad (g : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) = rad g x :=
  (rad_eq_sqrt g x).symm

-- pin: radR_control (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1161)
theorem radR_control (x : ℝ) :
    Real.sqrt (((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
        + ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2)
      = Real.sqrt ((1 + x * 3) ^ 2 + (2 + x * 4) ^ 2) := by
  simp

-- pin: hypotheses_inhabited (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1167)
theorem hypotheses_inhabited :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 ∧ 1 < (2 : ℂ).re ∧ ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℂ)) ∧
    (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n (fun _ : ℝ => (1 : ℂ)) x‖ ≤ C) ∧
    (0 : ℝ) < 1 ∧
    (∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ 1 * ‖ξ‖ ≤ ‖ContinuousLinearMap.mul ℝ ℝ v ξ‖) := by
  refine ⟨by simp, by norm_num, contDiff_const, fun n => ⟨1, one_pos, fun x => ?_⟩, one_pos, fun ξ => ⟨1, by simp, by simp⟩⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [iteratedFDeriv_const_of_ne hn]
    simp



end AutomorphicForm.RealIwasawa.RealDecay

namespace AutomorphicForm.RealIwasawa.B2bRUnif

open AutomorphicForm.RealIwasawa.ScalarMajorant AutomorphicForm.RealIwasawa.RealDecay MeasureTheory
open scoped ContDiff FourierTransform Nat

-- pin: continuous_botNormSq (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1205)
theorem continuous_botNormSq : Continuous fun g : Matrix (Fin 2) (Fin 2) ℝ => botNormSq g := by
  unfold botNormSq
  fun_prop

-- pin: continuous_foot_num (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1209)
theorem continuous_foot_num : Continuous fun g : Matrix (Fin 2) (Fin 2) ℝ => -(g 0 0 * g 1 0 + g 0 1 * g 1 1) := by
  fun_prop

-- pin: continuous_det2 (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1212)
theorem continuous_det2 : Continuous fun g : Matrix (Fin 2) (Fin 2) ℝ => g.det := by
  have : (fun g : Matrix (Fin 2) (Fin 2) ℝ => g.det) = fun g => g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
    funext fun g => Matrix.det_fin_two g
  rw [this]; fun_prop

-- pin: exists_uniform_matrix_constants (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1217)
theorem exists_uniform_matrix_constants (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℝ)) (h𝒢 : IsCompact 𝒢)
    (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) :
    ∃ T ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ g ∈ 𝒢, towerRatio g ≤ T ∧ ρ ≤ radFloor g := by

  obtain ⟨A₁, hA₁⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => botNormSq g) continuous_botNormSq.continuousOn
  obtain ⟨CA, hCA⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => (botNormSq g)⁻¹)
    ((continuous_botNormSq.continuousOn).inv₀ fun g hg => (botNormSq_pos (hdet g hg)).ne')
  obtain ⟨CD, hCD⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => (g.det)⁻¹)
    (continuous_det2.continuousOn.inv₀ fun g hg => hdet g hg)
  obtain ⟨CF, hCF⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => foot g)
    ((continuous_foot_num.continuousOn).div continuous_botNormSq.continuousOn fun g hg => (botNormSq_pos (hdet g hg)).ne')

  set A := max 1 A₁ with hA
  set cA := max 1 CA with hcA
  set cD := max 1 CD with hcD
  set cF := max 1 CF with hcF
  have hA1 : 1 ≤ A := le_max_left _ _
  have hcA1 : 1 ≤ cA := le_max_left _ _
  have hcD1 : 1 ≤ cD := le_max_left _ _
  have hcF1 : 1 ≤ cF := le_max_left _ _
  refine ⟨A * cD, min 1 (min ((cD ^ 2 * A * (1 + 2 * cF ^ 2))⁻¹) ((2 * cA)⁻¹)), by positivity, min_le_left _ _,
    fun g hg => ⟨?_, ?_⟩⟩
  ·
    have h1 : botNormSq g ≤ A := by
      have := hA₁ g hg; rw [Real.norm_of_nonneg (botNormSq_pos (hdet g hg)).le] at this
      exact this.trans (le_max_right _ _)
    have h2 : |g.det|⁻¹ ≤ cD := by
      have := hCD g hg; rw [norm_inv, Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _)
    unfold towerRatio
    rw [div_eq_mul_inv]
    exact mul_le_mul h1 h2 (inv_nonneg.mpr (abs_nonneg _)) (zero_le_one.trans hA1)
  ·
    have hApos := botNormSq_pos (hdet g hg)
    have h1 : botNormSq g ≤ A := by
      have := hA₁ g hg; rw [Real.norm_of_nonneg hApos.le] at this
      exact this.trans (le_max_right _ _)
    have h2 : (botNormSq g)⁻¹ ≤ cA := by
      have := hCA g hg; rw [norm_inv, Real.norm_of_nonneg hApos.le] at this
      exact this.trans (le_max_right _ _)
    have h3 : |g.det|⁻¹ ≤ cD := by
      have := hCD g hg; rw [norm_inv, Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _)
    have h4 : |foot g| ≤ cF := by
      have := hCF g hg; rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _)
    have hdet0 : 0 < |g.det| := abs_pos.mpr (hdet g hg)

    have hb1 : (cD ^ 2 * A * (1 + 2 * cF ^ 2))⁻¹ ≤ g.det ^ 2 / botNormSq g / (1 + 2 * foot g ^ 2) := by

      have e1 : g.det ^ 2 / botNormSq g / (1 + 2 * foot g ^ 2) = g.det ^ 2 * ((botNormSq g)⁻¹ * (1 + 2 * foot g ^ 2)⁻¹) := by
        rw [div_div, div_eq_mul_inv, mul_inv]
      have e2 : (cD ^ 2 * A * (1 + 2 * cF ^ 2))⁻¹ = (cD ^ 2)⁻¹ * (A⁻¹ * (1 + 2 * cF ^ 2)⁻¹) := by
        rw [mul_inv, mul_inv, mul_assoc]
      rw [e1, e2]
      have hd2 : (cD ^ 2)⁻¹ ≤ g.det ^ 2 := by
        rw [← sq_abs g.det, ← inv_pow]
        exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ (by positivity) hdet0).mpr (by rwa [← one_div, ← inv_eq_one_div] )) 2
      have hAinv : A⁻¹ ≤ (botNormSq g)⁻¹ := (inv_le_inv₀ (by positivity) hApos).mpr h1
      have hFinv : (1 + 2 * cF ^ 2)⁻¹ ≤ (1 + 2 * foot g ^ 2)⁻¹ := by
        refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
        have : foot g ^ 2 ≤ cF ^ 2 := by rw [← sq_abs (foot g)]; exact pow_le_pow_left₀ (abs_nonneg _) h4 2
        linarith
      exact mul_le_mul hd2 (mul_le_mul hAinv hFinv (by positivity) (by positivity)) (by positivity) (sq_nonneg _)

    have hb2 : (2 * cA)⁻¹ ≤ botNormSq g / 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      calc 2 / botNormSq g = 2 * (botNormSq g)⁻¹ := div_eq_mul_inv _ _
        _ ≤ 2 * cA := by gcongr
    unfold radFloor
    refine (min_le_right _ _).trans (le_min (le_trans (min_le_left _ _) hb1) (le_trans (min_le_right _ _) hb2))

end AutomorphicForm.RealIwasawa.B2bRUnif

namespace AutomorphicForm.RealIwasawa.B2bRUnif

open AutomorphicForm.RealIwasawa.ScalarMajorant AutomorphicForm.RealIwasawa.RealDecay MeasureTheory
open scoped ContDiff FourierTransform Nat

-- pin: norm_iteratedFDeriv_weight_le_uniform (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1302)
theorem norm_iteratedFDeriv_weight_le_uniform {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {T R : ℝ}
    (hT : towerRatio g ≤ T) {u : ℂ} (hu : ‖u‖ ≤ R) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n
        (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
      ≤ (n ! * max 1 R ^ n * (n ! * max 1 T) ^ n) * rad g x ^ (-u.re) := by
  rw [weightFun_eq hg u]
  refine (norm_iteratedFDeriv_Ψ_log_rad_le hg u n x).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (rad_pos hg x).le _)
  have h1 : max 1 ‖u‖ ^ n ≤ max 1 R ^ n := pow_le_pow_left₀ (by positivity) (max_le_max le_rfl hu) n
  have h2 : towerD g n ^ n ≤ (n ! * max 1 T) ^ n := by
    refine pow_le_pow_left₀ (towerD_pos n).le ?_ n
    unfold towerD
    exact mul_le_mul_of_nonneg_left (max_le_max le_rfl hT) (by positivity)
  have h0 : (0 : ℝ) ≤ n ! := by positivity
  calc (n ! : ℝ) * max 1 ‖u‖ ^ n * towerD g n ^ n ≤ n ! * max 1 R ^ n * (n ! * max 1 T) ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) h2 (pow_nonneg (towerD_pos n).le n) (by positivity)

-- pin: Dconst (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1319)
def Dconst (T R : ℝ) (Ch : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (i ! * max 1 R ^ i * (i ! * max 1 T) ^ i) * Ch (n - i)

-- pin: Dconst_nonneg (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1322)
theorem Dconst_nonneg (T R : ℝ) {Ch : ℕ → ℝ} (hCh : ∀ n, 0 ≤ Ch n) (n : ℕ) : 0 ≤ Dconst T R Ch n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hCh _)

-- pin: norm_iteratedFDeriv_weight_mul_le_uniform (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1325)
theorem norm_iteratedFDeriv_weight_mul_le_uniform {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {T R : ℝ}
    (hT : towerRatio g ≤ T) {u : ℂ} (hu : ‖u‖ ≤ R)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P) {Ch : ℕ → ℝ} (hCh : ∀ n x, ‖iteratedFDeriv ℝ n P x‖ ≤ Ch n)
    (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n
        (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) x‖
      ≤ Dconst T R Ch n * rad g x ^ (-u.re) := by
  have hrad := rad_pos hg x
  have hCh0 : ∀ m, 0 ≤ Ch m := fun m => (norm_nonneg _).trans (hCh m 0)
  refine (norm_iteratedFDeriv_mul_le (contDiff_weight hg u) hPC x (mod_cast le_top)).trans ?_
  unfold Dconst
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  calc (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i
            (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        * ‖iteratedFDeriv ℝ (n - i) P x‖
      ≤ (n.choose i : ℝ) * ((i ! * max 1 R ^ i * (i ! * max 1 T) ^ i) * rad g x ^ (-u.re)) * Ch (n - i) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_weight_le_uniform hg hT hu i x) (Nat.cast_nonneg _))
          (hCh (n - i) x) (norm_nonneg _) ?_
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (Real.rpow_nonneg hrad.le _))
    _ = (n.choose i : ℝ) * (i ! * max 1 R ^ i * (i ! * max 1 T) ^ i) * Ch (n - i) * rad g x ^ (-u.re) := by ring

-- pin: integral_rad_rpow_neg_le_uniform (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1348)
theorem integral_rad_rpow_neg_le_uniform {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρ : ρ ≤ radFloor g) {κ κ₀ κ₁ : ℝ} (hκ₀ : 1 < κ₀) (hκ : κ₀ ≤ κ) (hκ1 : κ ≤ κ₁) :
    ∫ x, rad g x ^ (-κ) ∂volume ≤ ρ ^ (-κ₁ / 2) * ∫ x : ℝ, (1 + ‖x‖ ^ 2) ^ (-κ₀ / 2) ∂volume := by
  have hint0 : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-κ₀ / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (μ := volume) (by rw [Module.finrank_self]; exact_mod_cast hκ₀)
  have hpt : ∀ x : ℝ, rad g x ^ (-κ) ≤ ρ ^ (-κ₁ / 2) * (1 + ‖x‖ ^ 2) ^ (-κ₀ / 2) := by
    intro x
    refine (rad_rpow_neg_le_one_add_sq hg (by linarith) x).trans ?_
    have hF := radFloor_pos hg
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    ·
      calc radFloor g ^ (-κ / 2) ≤ ρ ^ (-κ / 2) := Real.rpow_le_rpow_of_nonpos hρ0 hρ (by linarith)
        _ ≤ ρ ^ (-κ₁ / 2) := Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖x‖]) (by linarith)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (rad_pos hg x).le _)
    (hint0.const_mul _) (Filter.Eventually.of_forall hpt)

end AutomorphicForm.RealIwasawa.B2bRUnif

namespace AutomorphicForm.RealIwasawa.B2bRUnif

open AutomorphicForm.RealIwasawa.ScalarMajorant AutomorphicForm.RealIwasawa.RealDecay MeasureTheory
open scoped ContDiff FourierTransform Nat

-- pin: main (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1379)
theorem main
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℝ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU1 : ∀ u ∈ U, 1 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℝ → ℝ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ x : ℝ, ‖iteratedFDeriv ℝ n (P g) x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P g x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by

  rcases U.eq_empty_or_nonempty with hUe | hUne
  · exact ⟨1, one_pos, fun g _ u hu => by simp [hUe] at hu⟩

  obtain ⟨T, ρ, hρ0, hρ1, hG⟩ := exists_uniform_matrix_constants 𝒢 h𝒢 hdet
  obtain ⟨R, hR⟩ := hU.exists_bound_of_continuousOn (f := fun u : ℂ => u) continuousOn_id
  obtain ⟨u₀, hu₀U, hu₀⟩ := hU.exists_isMinOn hUne Complex.continuous_re.continuousOn
  set κ₀ : ℝ := u₀.re with hκ₀
  have hκ₀1 : 1 < κ₀ := hU1 u₀ hu₀U
  set κ₁ : ℝ := max κ₀ R with hκ₁
  choose Ch hCh using hPB

  set I₀ : ℝ := ∫ x : ℝ, (1 + ‖x‖ ^ 2) ^ (-κ₀ / 2) ∂volume with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun x => by positivity
  set J : ℝ := ρ ^ (-κ₁ / 2) * I₀ with hJ
  have hJ0 : 0 ≤ J := mul_nonneg (Real.rpow_nonneg hρ0.le _) hI₀0
  set D : ℕ → ℝ := fun n => Dconst T R Ch n with hD
  have hD0 : ∀ n, 0 ≤ D n := fun n => Dconst_nonneg T R (fun m => (hCh m).1.le) n
  set M0' : ℝ := D 0 * J with hM0'
  set MN' : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), D j * J with hMN'
  have hM0'0 : 0 ≤ M0' := mul_nonneg (hD0 0) hJ0
  have hMN'0 : 0 ≤ MN' := mul_nonneg (pow_nonneg (by norm_num) N) (Finset.sum_nonneg fun j _ => mul_nonneg (hD0 j) hJ0)
  refine ⟨(M0' * 2 ^ N + MN' * (2 / c) ^ N) + 1, by positivity, fun g hg u hu ξ => ?_⟩

  have hgd := hdet g hg
  have hTg := (hG g hg).1
  have hρg := (hG g hg).2
  have huR : ‖u‖ ≤ R := by simpa using hR u hu
  have hure : κ₀ ≤ u.re := by have := hu₀ hu; simpa [hκ₀] using this
  have hure1 : u.re ≤ κ₁ := ((Complex.re_le_norm u).trans huR).trans (le_max_right _ _)
  have hu1 : 1 < u.re := hU1 u hu
  set f : ℝ → ℂ := fun x =>
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P g x with hfdef
  have hCB : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D n * rad g x ^ (-u.re) := fun n x =>
    norm_iteratedFDeriv_weight_mul_le_uniform hgd hTg huR (hPC g hg) (fun m y => (hCh m).2 g hg y) n x
  have hintr : Integrable (fun x => rad g x ^ (-u.re)) volume := integrable_rpow_neg_rad hgd hu1
  have hintJ : ∫ x, rad g x ^ (-u.re) ∂volume ≤ J :=
    integral_rad_rpow_neg_le_uniform hgd hρ0 hρ1 hρg hκ₀1 hure hure1
  have hfC : ContDiff ℝ ∞ f := (contDiff_weight hgd u).mul (hPC g hg)
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (D j)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hCB j x
  have hIj : ∀ j, ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume ≤ D j * J := by
    intro j
    calc ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume ≤ ∫ v, D j * rad g v ^ (-u.re) ∂volume :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) (hintr.const_mul _)
            (Filter.Eventually.of_forall (hCB j))
      _ = D j * ∫ v, rad g v ^ (-u.re) ∂volume := integral_const_mul _ _
      _ ≤ D j * J := mul_le_mul_of_nonneg_left hintJ (hD0 j)

  have key := MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive L
    (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume with hMN
  have hMNle : MN ≤ MN' := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hIj j) (pow_nonneg (by norm_num) N)
  have hMN0 : (0:ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)
  have hfint : Integrable f volume := by
    refine (hintr.const_mul (D 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 := hCB 0 x
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume with hM0
  have hM00 : (0:ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  have hM0le : M0 ≤ M0' := by
    have := hIj 0
    simp only [norm_iteratedFDeriv_zero] at this
    exact this
  have hξ0 : (0:ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0:ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0:ℝ) < (1 + ‖ξ‖) ^ (-(N:ℝ)) := Real.rpow_pos_of_pos h1ξ _
  have hc2 : (0:ℝ) ≤ (2 / c) ^ N := pow_nonneg (div_nonneg (by norm_num) hc.le) N
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  · have hbd : (2:ℝ) ^ (-(N:ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith) (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0' : ℝ) = M0' * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := by
      rw [mul_assoc, show ((2:ℝ)^N : ℝ) = (2:ℝ)^(N:ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0' * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) ≤ M0' * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hbd (mul_nonneg hM0'0 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0' * 2 ^ N : ℝ) ≤ M0' * 2 ^ N + MN' * (2 / c) ^ N + 1 := by
      have := mul_nonneg hMN'0 hc2; linarith
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0' := hstep1.trans hM0le
      _ = M0' * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := hstep2
      _ ≤ M0' * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := hstep3
      _ ≤ (M0' * 2 ^ N + MN' * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  · have hkey := key ξ
    have hcξ : (0:ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1:ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N:ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N:ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast, ← inv_pow, inv_div]
      rw [hp1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))) hc2
    have hstep4 : (MN' * (2 / c) ^ N : ℝ) ≤ M0' * 2 ^ N + MN' * (2 / c) ^ N + 1 := by
      have := mul_nonneg hM0'0 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N); linarith
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := hdiv
      _ ≤ MN' * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ))) :=
          mul_le_mul hMNle hcmp (Real.rpow_nonneg hcξ.le _) hMN'0
      _ = MN' * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by ring
      _ ≤ (M0' * 2 ^ N + MN' * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

end AutomorphicForm.RealIwasawa.B2bRUnif

namespace AutomorphicForm.RealIwasawa.Engine

-- pin: solution (S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:1198)
theorem norm_fourierIntegral_cpow_rad_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  RealDecay.norm_fourierIntegral_cpow_radR_mul_le_polyDecay hg hu hPC hPB L hc hL N

-- pin: solution (S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:1518)
theorem exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℝ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU1 : ∀ u ∈ U, 1 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℝ → ℝ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ x : ℝ, ‖iteratedFDeriv ℝ n (P g) x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P g x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  B2bRUnif.main 𝒢 h𝒢 hdet U hU hU1 P hPC hPB L hc hL N

end AutomorphicForm.RealIwasawa.Engine

end
