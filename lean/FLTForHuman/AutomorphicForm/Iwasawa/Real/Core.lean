/-
  The real Iwasawa rotation engine: the `kR` proof-local vocabulary and its smoothness.

  The real-place companion of `Iwasawa/Complex/Basic.lean`: the rotation `rot`, the
  Weyl-unipotent translate `weylUnip`, the radial length `rad`, the angle `angle`, the
  Borel factor `borel`, the Weyl element `weylR` and the `kR` tower.  The pin has no
  `Def_AutomorphicForm_RealIwasawa` (topic §4c), so the whole real vocabulary is
  proof-local and is transcribed once, public at the pin's names, here.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean
-/
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import FLTForHuman.MeasureTheory.FourierDecay

set_option autoImplicit false

noncomputable section

open scoped ContDiff Nat

namespace AutomorphicForm.RealIwasawa

-- pin: rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:17)
def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

-- pin: rot_apply_00 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:20)
@[scoped simp] theorem rot_apply_00 (θ : ℝ) : rot θ 0 0 = Real.cos θ := rfl
-- pin: rot_apply_01 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:21)
@[scoped simp] theorem rot_apply_01 (θ : ℝ) : rot θ 0 1 = -Real.sin θ := rfl
-- pin: rot_apply_10 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:22)
@[scoped simp] theorem rot_apply_10 (θ : ℝ) : rot θ 1 0 = Real.sin θ := rfl
-- pin: rot_apply_11 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:23)
@[scoped simp] theorem rot_apply_11 (θ : ℝ) : rot θ 1 1 = Real.cos θ := rfl

-- pin: rot_zero (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:25)
theorem rot_zero : rot 0 = 1 := by
  rw [rot, Matrix.one_fin_two, Real.cos_zero, Real.sin_zero, neg_zero]

-- pin: rot_add (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:28)
theorem rot_add (s t : ℝ) : rot (s + t) = rot s * rot t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

-- pin: det_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:33)
theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, Matrix.det_fin_two_of]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination h

-- pin: rot_mul_rot_neg (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:38)
theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  rw [← rot_add, add_neg_cancel, rot_zero]

-- pin: rot_neg_mul_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:41)
theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  rw [← rot_add, neg_add_cancel, rot_zero]

-- pin: row_sq_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:44)
theorem row_sq_rot (θ x y : ℝ) :
    (x * rot θ 0 0 + y * rot θ 1 0) ^ 2 + (x * rot θ 0 1 + y * rot θ 1 1) ^ 2 = x ^ 2 + y ^ 2 := by
  simp only [rot_apply_00, rot_apply_01, rot_apply_10, rot_apply_11]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination (x ^ 2 + y ^ 2) * h

-- pin: norm_det_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:50)
theorem norm_det_rot (θ : ℝ) : ‖(rot θ).det‖ = 1 := by
  rw [det_rot, norm_one]

-- pin: norm_row_sq_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:53)
theorem norm_row_sq_rot (θ x y : ℝ) :
    ‖x * rot θ 0 0 + y * rot θ 1 0‖ ^ 2 + ‖x * rot θ 0 1 + y * rot θ 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [Real.norm_eq_abs, sq_abs]
  exact row_sq_rot θ x y

-- pin: continuous_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:58)
theorem continuous_rot : Continuous rot := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · show Continuous fun θ => Real.cos θ
    exact Real.continuous_cos
  · show Continuous fun θ => -Real.sin θ
    exact Real.continuous_sin.neg
  · show Continuous fun θ => Real.sin θ
    exact Real.continuous_sin
  · show Continuous fun θ => Real.cos θ
    exact Real.continuous_cos

-- pin: contDiff_rot_apply (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:70)
theorem contDiff_rot_apply (i j : Fin 2) : ContDiff ℝ ∞ (fun θ => rot θ i j) := by
  fin_cases i <;> fin_cases j
  · show ContDiff ℝ ∞ fun θ => Real.cos θ
    exact Real.contDiff_cos
  · show ContDiff ℝ ∞ fun θ => -Real.sin θ
    exact Real.contDiff_sin.neg
  · show ContDiff ℝ ∞ fun θ => Real.sin θ
    exact Real.contDiff_sin
  · show ContDiff ℝ ∞ fun θ => Real.cos θ
    exact Real.contDiff_cos

-- pin: rotGL (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:81)
def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  ⟨rot θ, rot (-θ), rot_mul_rot_neg θ, rot_neg_mul_rot θ⟩

-- pin: coe_rotGL (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:84)
@[scoped simp] theorem coe_rotGL (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rot θ := rfl

-- pin: rotGL_zero (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:86)
theorem rotGL_zero : rotGL 0 = 1 := Units.ext rot_zero

-- pin: rotGL_add (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:88)
theorem rotGL_add (s t : ℝ) : rotGL (s + t) = rotGL s * rotGL t := Units.ext (rot_add s t)

-- pin: continuous_rotGL (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:90)
theorem continuous_rotGL : Continuous rotGL := by
  refine Units.continuous_iff.2 ⟨continuous_rot, ?_⟩
  show Continuous fun θ => rot (-θ)
  exact continuous_rot.comp continuous_neg

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

-- pin: weylUnip (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:97)
def weylUnip (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0] * !![1, u; 0, 1] * g

-- pin: weylUnip_eq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:99)
theorem weylUnip_eq (u : ℝ) :
    weylUnip g u = !![g 1 0, g 1 1; g 0 0 + u * g 1 0, g 0 1 + u * g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylUnip, Matrix.mul_apply, Fin.sum_univ_two]

-- pin: botNormSq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:104)
def botNormSq : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

-- pin: foot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:106)
def foot : ℝ := -(g 0 0 * g 1 0 + g 0 1 * g 1 1) / botNormSq g

-- pin: center (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:108)
def center : ℂ := ⟨foot g, -(g.det / botNormSq g)⟩

-- pin: dir (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:110)
def dir : ℂ := ⟨g 1 1, g 1 0⟩

-- pin: botRow (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:112)
def botRow (u : ℝ) : ℂ := ⟨g 0 1 + u * g 1 1, g 0 0 + u * g 1 0⟩

-- pin: rad (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:114)
def rad (u : ℝ) : ℝ := ‖botRow g u‖

variable {g}

-- pin: botNormSq_pos (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:118)
theorem botNormSq_pos (hg : g.det ≠ 0) : 0 < botNormSq g := by
  unfold botNormSq
  rcases (add_nonneg (sq_nonneg (g 1 0)) (sq_nonneg (g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero]

-- pin: norm_dir_sq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:128)
theorem norm_dir_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖dir g‖ ^ 2 = botNormSq g := by
  rw [Complex.sq_norm, dir, Complex.normSq_mk, botNormSq]
  ring

-- pin: norm_dir_pos (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:132)
theorem norm_dir_pos (hg : g.det ≠ 0) : 0 < ‖dir g‖ := by
  have h := norm_dir_sq g
  have hA := botNormSq_pos hg
  nlinarith [norm_nonneg (dir g)]

-- pin: dir_ne_zero (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:137)
theorem dir_ne_zero (hg : g.det ≠ 0) : dir g ≠ 0 :=
  norm_pos_iff.1 (norm_dir_pos hg)

-- pin: botRow_eq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:140)
theorem botRow_eq (hg : g.det ≠ 0) (u : ℝ) : botRow g u = dir g * ((u : ℂ) - center g) := by
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  apply Complex.ext
  · simp only [botRow, dir, center, foot, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, Matrix.det_fin_two]
    unfold botNormSq at hA ⊢
    field_simp
    ring
  · simp only [botRow, dir, center, foot, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, Matrix.det_fin_two]
    unfold botNormSq at hA ⊢
    field_simp
    ring

-- pin: im_sub_center (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:154)
theorem im_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    ((u : ℂ) - center g).im = g.det / botNormSq g := by
  simp [center]

-- pin: re_sub_center (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:158)
theorem re_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : ((u : ℂ) - center g).re = u - foot g := by
  simp [center]

-- pin: sub_center_mem_slitPlane (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:161)
theorem sub_center_mem_slitPlane (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by
    rw [im_sub_center]
    exact div_ne_zero hg (botNormSq_pos hg).ne'))

-- pin: sub_center_ne_zero (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:166)
theorem sub_center_ne_zero (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ≠ 0 :=
  Complex.slitPlane_ne_zero (sub_center_mem_slitPlane hg u)

-- pin: abs_det_div_le_norm_sub_center (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:169)
theorem abs_det_div_le_norm_sub_center (hg : g.det ≠ 0) (u : ℝ) :
    |g.det| / botNormSq g ≤ ‖(u : ℂ) - center g‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) - center g)
  rwa [im_sub_center, abs_div, abs_of_pos (botNormSq_pos hg)] at h

-- pin: rad_eq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:174)
theorem rad_eq (hg : g.det ≠ 0) (u : ℝ) : rad g u = ‖dir g‖ * ‖(u : ℂ) - center g‖ := by
  rw [rad, botRow_eq hg, norm_mul]

-- pin: rad_pos (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:177)
theorem rad_pos (hg : g.det ≠ 0) (u : ℝ) : 0 < rad g u := by
  rw [rad_eq hg]
  exact mul_pos (norm_dir_pos hg) (norm_pos_iff.2 (sub_center_ne_zero hg u))

-- pin: rad_sq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:181)
theorem rad_sq (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u ^ 2 = (g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2 := by
  rw [rad, Complex.sq_norm, botRow, Complex.normSq_mk]
  ring

-- pin: rad_eq_sqrt (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:186)
theorem rad_eq_sqrt (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u = Real.sqrt ((g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2) := by
  rw [← rad_sq, Real.sqrt_sq (show 0 ≤ rad g u from norm_nonneg _)]

-- pin: rad_sq_eq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:190)
theorem rad_sq_eq (hg : g.det ≠ 0) (u : ℝ) :
    rad g u ^ 2 = botNormSq g * (u - foot g) ^ 2 + g.det ^ 2 / botNormSq g := by
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  rw [rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm, ← Complex.re_add_im ((u : ℂ) - center g),
    re_sub_center, im_sub_center]
  rw [Complex.normSq_add_mul_I]
  field_simp

-- pin: abs_det_div_sqrt_le_rad (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:198)
theorem abs_det_div_sqrt_le_rad (hg : g.det ≠ 0) (u : ℝ) :
    |g.det| / Real.sqrt (botNormSq g) ≤ rad g u := by
  have hA := botNormSq_pos hg
  have hdir : ‖dir g‖ = Real.sqrt (botNormSq g) := by
    rw [← norm_dir_sq, Real.sqrt_sq (norm_nonneg _)]
  have hs : 0 < Real.sqrt (botNormSq g) := Real.sqrt_pos.2 hA
  have h1 : |g.det| ≤ ‖(u : ℂ) - center g‖ * botNormSq g :=
    (div_le_iff₀ hA).1 (abs_det_div_le_norm_sub_center hg u)
  rw [rad_eq hg, hdir, div_le_iff₀ hs]
  calc |g.det| ≤ ‖(u : ℂ) - center g‖ * botNormSq g := h1
    _ = Real.sqrt (botNormSq g) * ‖(u : ℂ) - center g‖ * Real.sqrt (botNormSq g) := by
        rw [mul_comm (Real.sqrt (botNormSq g)) _, mul_assoc, Real.mul_self_sqrt hA.le]

variable (g)

-- pin: logLine (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:213)
def logLine (u : ℝ) : ℂ := Complex.log ((u : ℂ) - center g)

-- pin: angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:215)
def angle (u : ℝ) : ℝ := Complex.arg (dir g) + (logLine g u).im

variable {g}

-- pin: angle_eq_arg_add_arg (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:219)
theorem angle_eq_arg_add_arg (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    angle g u = Complex.arg (dir g) + Complex.arg ((u : ℂ) - center g) := by
  rw [angle, logLine, Complex.log_im]

-- pin: log_rad_eq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:223)
theorem log_rad_eq (hg : g.det ≠ 0) (u : ℝ) : Real.log (rad g u) = Real.log ‖dir g‖ + (logLine g u).re := by
  rw [rad_eq hg, Real.log_mul (norm_dir_pos hg).ne' (norm_pos_iff.2 (sub_center_ne_zero hg u)).ne', logLine,
    Complex.log_re]

-- pin: exp_angle_mul_I (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:227)
theorem exp_angle_mul_I (hg : g.det ≠ 0) (u : ℝ) :
    Complex.exp (angle g u * Complex.I) = botRow g u / rad g u := by
  have h1 : Complex.exp (Complex.arg (dir g) * Complex.I) = dir g / ‖dir g‖ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.2 (norm_dir_pos hg).ne')]
    exact (mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I (dir g))
  have h2 : Complex.exp (Complex.arg ((u : ℂ) - center g) * Complex.I)
      = ((u : ℂ) - center g) / ‖(u : ℂ) - center g‖ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.2 (norm_pos_iff.2 (sub_center_ne_zero hg u)).ne')]
    exact (mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I _)
  rw [angle_eq_arg_add_arg, Complex.ofReal_add, add_mul, Complex.exp_add, h1, h2, div_mul_div_comm,
    ← botRow_eq hg, rad_eq hg, Complex.ofReal_mul]

-- pin: cos_angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:239)
theorem cos_angle (hg : g.det ≠ 0) (u : ℝ) : Real.cos (angle g u) = (g 0 1 + u * g 1 1) / rad g u := by
  have h := congrArg Complex.re (exp_angle_mul_I hg u)
  rw [Complex.exp_ofReal_mul_I_re, Complex.div_ofReal_re] at h
  rw [h, botRow]

-- pin: sin_angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:244)
theorem sin_angle (hg : g.det ≠ 0) (u : ℝ) : Real.sin (angle g u) = (g 0 0 + u * g 1 0) / rad g u := by
  have h := congrArg Complex.im (exp_angle_mul_I hg u)
  rw [Complex.exp_ofReal_mul_I_im, Complex.div_ofReal_im] at h
  rw [h, botRow]

variable (g)

-- pin: borel (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:251)
def borel (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-g.det / rad g u, (g 1 0 * (g 0 0 + u * g 1 0) + g 1 1 * (g 0 1 + u * g 1 1)) / rad g u; 0, rad g u]

variable {g}

-- pin: borel_apply_10 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:256)
@[scoped simp] theorem borel_apply_10 (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : borel g u 1 0 = 0 := rfl
-- pin: borel_apply_11 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:257)
@[scoped simp] theorem borel_apply_11 (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : borel g u 1 1 = rad g u := rfl
-- pin: borel_apply_00 (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:258)
@[scoped simp] theorem borel_apply_00 (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : borel g u 0 0 = -g.det / rad g u := rfl

-- pin: det_borel (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:260)
theorem det_borel (hg : g.det ≠ 0) (u : ℝ) : (borel g u).det = -g.det := by
  rw [borel, Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ (rad_pos hg u).ne']

-- pin: weylUnip_eq_borel_mul_rot (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:263)
theorem weylUnip_eq_borel_mul_rot (hg : g.det ≠ 0) (u : ℝ) : weylUnip g u = borel g u * rot (angle g u) := by
  have hr : rad g u ≠ 0 := (rad_pos hg u).ne'
  have hr2 := rad_sq g u
  have hD := Matrix.det_fin_two g

  set P : ℝ := g 0 0 + u * g 1 0 with hP
  set Q : ℝ := g 0 1 + u * g 1 1 with hQ
  have hc : Real.cos (angle g u) = Q / rad g u := cos_angle hg u
  have hs : Real.sin (angle g u) = P / rad g u := sin_angle hg u
  have e00 : -g.det / rad g u * (Q / rad g u)
      + (g 1 0 * P + g 1 1 * Q) / rad g u * (P / rad g u) = g 1 0 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_eq_iff (mul_ne_zero hr hr), ← sq, hr2, hD,
      hP, hQ]
    ring
  have e01 : -g.det / rad g u * (-(P / rad g u))
      + (g 1 0 * P + g 1 1 * Q) / rad g u * (Q / rad g u) = g 1 1 := by
    rw [mul_neg, div_mul_div_comm, div_mul_div_comm, ← sub_eq_neg_add, div_sub_div_same,
      div_eq_iff (mul_ne_zero hr hr), ← sq, hr2, hD, hP, hQ]
    ring
  have e10 : (0 : ℝ) * (Q / rad g u) + rad g u * (P / rad g u) = P := by
    rw [zero_mul, zero_add, mul_div_cancel₀ _ hr]
  have e11 : (0 : ℝ) * (-(P / rad g u)) + rad g u * (Q / rad g u) = Q := by
    rw [zero_mul, zero_add, mul_div_cancel₀ _ hr]
  rw [weylUnip_eq, borel, rot, Matrix.mul_fin_two, hc, hs, ← hP, ← hQ, e00, e01, e10, e11]

-- pin: borelGL (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:288)
def borelGL (hg : g.det ≠ 0) (u : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borel g u) (by rw [det_borel hg]; exact neg_ne_zero.2 hg)

-- pin: coe_borelGL (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:291)
@[scoped simp] theorem coe_borelGL (hg : g.det ≠ 0) (u : ℝ) :
    ((borelGL hg u : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = borel g u := rfl

-- pin: weylR (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:294)
def weylR : GL (Fin 2) ℝ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

-- pin: unipR (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:299)
def unipR (u : ℝ) : GL (Fin 2) ℝ :=
  ⟨!![1, u; 0, 1], !![1, -u; 0, 1],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

-- pin: weylR_mul_unipR_mul_eq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:304)
theorem weylR_mul_unipR_mul_eq (g : GL (Fin 2) ℝ) (u : ℝ) :
    weylR * unipR u * g
      = borelGL (g := (g : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.GeneralLinearGroup.det_ne_zero g) u
        * rotGL (angle (g : Matrix (Fin 2) (Fin 2) ℝ) u) := by
  apply Units.ext
  simp only [Units.val_mul, coe_borelGL, coe_rotGL]
  exact weylUnip_eq_borel_mul_rot (Matrix.GeneralLinearGroup.det_ne_zero g) u

-- pin: invTower (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:312)
def invTower (g : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  (-1) ^ k * (k ! : ℂ) * ((u : ℂ) - center g) ^ (-1 - (k : ℤ))

-- pin: invTower_zero (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:315)
theorem invTower_zero (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : invTower g 0 u = ((u : ℂ) - center g)⁻¹ := by
  simp [invTower]

-- pin: hasDerivAt_logLine (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:318)
theorem hasDerivAt_logLine (hg : g.det ≠ 0) (u : ℝ) : HasDerivAt (logLine g) (invTower g 0 u) u := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ) - center g) 1 u := (hasDerivAt_id u).ofReal_comp.sub_const _
  have h2 := h.clog_real (sub_center_mem_slitPlane hg u)
  rw [invTower_zero, ← one_div]
  exact h2

-- pin: hasDerivAt_invTower (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:324)
theorem hasDerivAt_invTower (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    HasDerivAt (invTower g k) (invTower g (k + 1) u) u := by
  have hz := sub_center_ne_zero hg u
  have h1 : HasDerivAt (fun z : ℂ => (z - center g) ^ (-1 - (k : ℤ)))
      (((-1 - (k : ℤ) : ℤ) : ℂ) * ((u : ℂ) - center g) ^ (-1 - (k : ℤ) - 1)) (u : ℂ) := by
    have := (hasDerivAt_zpow (-1 - (k : ℤ)) ((u : ℂ) - center g) (Or.inl hz)).comp (u : ℂ)
      ((hasDerivAt_id (u : ℂ)).sub_const (center g))
    simp at this ⊢
    exact this
  have h2 := (h1.comp_ofReal).const_mul ((-1) ^ k * (k ! : ℂ))
  refine h2.congr_deriv ?_
  have he : (-1 - (k : ℤ) - 1) = (-1 - ((k + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [invTower, he, Nat.factorial_succ]
  push_cast
  ring

-- pin: hasDerivAt_im (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:340)
theorem hasDerivAt_im {F : ℝ → ℂ} {F' : ℂ} {u : ℝ} (h : HasDerivAt F F' u) :
    HasDerivAt (fun y => (F y).im) F'.im u := by
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def] using h2

-- pin: hasDerivAt_re (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:345)
theorem hasDerivAt_re {F : ℝ → ℂ} {F' : ℂ} {u : ℝ} (h : HasDerivAt F F' u) :
    HasDerivAt (fun y => (F y).re) F'.re u := by
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def] using h2

-- pin: iteratedDeriv_logLine_succ (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:350)
theorem iteratedDeriv_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (logLine g) = invTower g k := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_logLine hg u).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_invTower hg k u).deriv

-- pin: iteratedDeriv_im_logLine_succ (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:362)
theorem iteratedDeriv_im_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (fun u => (logLine g u).im) = fun u => (invTower g k u).im := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_im (hasDerivAt_logLine hg u)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_im (hasDerivAt_invTower hg k u)).deriv

-- pin: iteratedDeriv_re_logLine_succ (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:374)
theorem iteratedDeriv_re_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (fun u => (logLine g u).re) = fun u => (invTower g k u).re := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_re (hasDerivAt_logLine hg u)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_re (hasDerivAt_invTower hg k u)).deriv

-- pin: iteratedDeriv_angle_succ (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:386)
theorem iteratedDeriv_angle_succ (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (angle g) u = (invTower g k u).im := by
  have h : angle g = fun u => Complex.arg (dir g) + (logLine g u).im := rfl
  rw [h, iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_im_logLine_succ hg k]

-- pin: iteratedDeriv_log_rad_succ (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:391)
theorem iteratedDeriv_log_rad_succ (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (fun u => Real.log (rad g u)) u = (invTower g k u).re := by
  have h : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [h, iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_re_logLine_succ hg k]

-- pin: hasDerivAt_angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:397)
theorem hasDerivAt_angle (hg : g.det ≠ 0) (u : ℝ) : HasDerivAt (angle g) (-g.det / rad g u ^ 2) u := by
  have h := (hasDerivAt_im (hasDerivAt_logLine hg u)).const_add (Complex.arg (dir g))
  refine h.congr_deriv ?_
  rw [invTower_zero, Complex.inv_im, im_sub_center, rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm, neg_div,
    div_div, neg_div]

-- pin: hasDerivAt_log_rad (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:403)
theorem hasDerivAt_log_rad (hg : g.det ≠ 0) (u : ℝ) :
    HasDerivAt (fun u => Real.log (rad g u)) (botNormSq g * (u - foot g) / rad g u ^ 2) u := by
  have h := (hasDerivAt_re (hasDerivAt_logLine hg u)).const_add (Real.log ‖dir g‖)
  have hfun : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [hfun]
  refine h.congr_deriv ?_
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  rw [invTower_zero, Complex.inv_re, re_sub_center, rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm,
    mul_div_mul_left _ _ hA]

-- pin: deriv_angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:414)
theorem deriv_angle (hg : g.det ≠ 0) (u : ℝ) : deriv (angle g) u = -g.det / rad g u ^ 2 :=
  (hasDerivAt_angle hg u).deriv

-- pin: contDiff_logLine (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:417)
theorem contDiff_logLine (hg : g.det ≠ 0) : ContDiff ℝ ∞ (logLine g) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) - center g) u :=
    (Complex.ofRealCLM.contDiff.sub contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ ∞ Complex.log ((u : ℂ) - center g) :=
    (Complex.contDiffAt_log (sub_center_mem_slitPlane hg u)).restrict_scalars ℝ
  exact h2.comp u h1

-- pin: contDiff_angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:426)
theorem contDiff_angle (hg : g.det ≠ 0) : ContDiff ℝ ∞ (angle g) :=
  contDiff_const.add (Complex.imCLM.contDiff.comp (contDiff_logLine hg))

-- pin: contDiff_log_rad (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:429)
theorem contDiff_log_rad (hg : g.det ≠ 0) : ContDiff ℝ ∞ (fun u => Real.log (rad g u)) := by
  have h : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [h]
  exact contDiff_const.add (Complex.reCLM.contDiff.comp (contDiff_logLine hg))

-- pin: contDiff_rad (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:435)
theorem contDiff_rad (hg : g.det ≠ 0) : ContDiff ℝ ∞ (rad g) := by
  have h : rad g = fun u => Real.exp (Real.log (rad g u)) :=
    funext fun u => (Real.exp_log (rad_pos hg u)).symm
  rw [h]
  exact Real.contDiff_exp.comp (contDiff_log_rad hg)

-- pin: contDiff_rot_angle_apply (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:441)
theorem contDiff_rot_angle_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun u => rot (angle g u) i j) :=
  (contDiff_rot_apply i j).comp (contDiff_angle hg)

-- pin: norm_invTower_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:445)
theorem norm_invTower_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    ‖invTower g k u‖ ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  have hz := sub_center_ne_zero hg u
  have hpos : 0 < |g.det| / botNormSq g := div_pos (abs_pos.2 hg) (botNormSq_pos hg)
  have hle := abs_det_div_le_norm_sub_center hg u
  have hk : (-1 - (k : ℤ)) = -(((k + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [invTower, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, hk,
    zpow_neg, zpow_natCast, norm_inv, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc (‖(u : ℂ) - center g‖ ^ (k + 1))⁻¹ ≤ ((|g.det| / botNormSq g) ^ (k + 1))⁻¹ :=
        inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hle _)
    _ = (botNormSq g / |g.det|) ^ (k + 1) := by rw [← inv_pow, inv_div]

-- pin: abs_iteratedDeriv_angle_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:458)
theorem abs_iteratedDeriv_angle_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    |iteratedDeriv (k + 1) (angle g) u| ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  rw [iteratedDeriv_angle_succ hg]
  exact (Complex.abs_im_le_norm _).trans (norm_invTower_le hg k u)

-- pin: abs_iteratedDeriv_log_rad_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:463)
theorem abs_iteratedDeriv_log_rad_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    |iteratedDeriv (k + 1) (fun u => Real.log (rad g u)) u| ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  rw [iteratedDeriv_log_rad_succ hg]
  exact (Complex.abs_re_le_norm _).trans (norm_invTower_le hg k u)

-- pin: center_one (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:468)
theorem center_one : center (1 : Matrix (Fin 2) (Fin 2) ℝ) = -Complex.I := by
  apply Complex.ext <;> simp [center, foot, botNormSq, Matrix.one_apply_ne]

-- pin: rad_one (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:471)
theorem rad_one (u : ℝ) : rad (1 : Matrix (Fin 2) (Fin 2) ℝ) u = ‖(u : ℂ) + Complex.I‖ := by
  rw [rad_eq (g := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp) u, center_one, sub_neg_eq_add]
  have : dir (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    apply Complex.ext <;> simp [dir, Matrix.one_apply_ne]
  rw [this, norm_one, one_mul]

-- pin: weyl_control_cos (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:488)
theorem weyl_control_cos : Real.cos (angle !![(0 : ℝ), 1; 1, 0] 0) = 1 := by
  have hg : Matrix.det !![(0 : ℝ), 1; 1, 0] ≠ 0 := by rw [Matrix.det_fin_two_of]; norm_num
  rw [cos_angle hg, rad_eq_sqrt]
  simp

-- pin: weyl_control_sin (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:493)
theorem weyl_control_sin : Real.sin (angle !![(0 : ℝ), 1; 1, 0] 0) = 0 := by
  have hg : Matrix.det !![(0 : ℝ), 1; 1, 0] ≠ 0 := by rw [Matrix.det_fin_two_of]; norm_num
  rw [sin_angle hg]
  simp

-- pin: weyl_control_borel (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:498)
theorem weyl_control_borel : borel !![(0 : ℝ), 1; 1, 0] 0 = 1 := by
  rw [borel, rad_eq_sqrt, Matrix.det_fin_two_of, Matrix.one_fin_two]
  simp


end AutomorphicForm.RealIwasawa

namespace AutomorphicForm.RealIwasawa.ScalarMajorant

section Constants

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

-- pin: towerRatio (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:525)
def towerRatio : ℝ := botNormSq g / |g.det|

-- pin: towerD (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:527)
def towerD (n : ℕ) : ℝ := n ! * max 1 (towerRatio g)

-- pin: radFloor (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:529)
def radFloor : ℝ := min ((g.det ^ 2 / botNormSq g) / (1 + 2 * foot g ^ 2)) (botNormSq g / 2)

variable {g}

-- pin: towerRatio_nonneg (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:533)
theorem towerRatio_nonneg : 0 ≤ towerRatio g :=
  div_nonneg (by unfold botNormSq; positivity) (abs_nonneg _)

-- pin: one_le_towerD (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:536)
theorem one_le_towerD (n : ℕ) : 1 ≤ towerD g n :=
  one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos n) (le_max_left _ _)

-- pin: towerD_pos (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:539)
theorem towerD_pos (n : ℕ) : 0 < towerD g n := one_pos.trans_le (one_le_towerD n)

-- pin: radFloor_pos (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:541)
theorem radFloor_pos (hg : g.det ≠ 0) : 0 < radFloor g := by
  have hA := botNormSq_pos hg
  unfold radFloor
  exact lt_min (by positivity) (by linarith)

-- pin: floor_aux (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:546)
theorem floor_aux {A D f : ℝ} (hA : 0 < A) (hD : 0 < D) (u : ℝ) :
    min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + u ^ 2) ≤ A * (u - f) ^ 2 + D := by
  have h1 : 1 + u ^ 2 ≤ (1 + 2 * f ^ 2) + 2 * (u - f) ^ 2 := by nlinarith [sq_nonneg (u - 2 * f), sq_nonneg f]
  have hf2 : 0 < 1 + 2 * f ^ 2 := by positivity
  have hmin0 : 0 ≤ min (D / (1 + 2 * f ^ 2)) (A / 2) := le_min (div_nonneg hD.le hf2.le) (by linarith)
  calc min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + u ^ 2)
      ≤ min (D / (1 + 2 * f ^ 2)) (A / 2) * ((1 + 2 * f ^ 2) + 2 * (u - f) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hmin0
    _ = min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + 2 * f ^ 2)
          + min (D / (1 + 2 * f ^ 2)) (A / 2) * (2 * (u - f) ^ 2) := by ring
    _ ≤ D / (1 + 2 * f ^ 2) * (1 + 2 * f ^ 2) + A / 2 * (2 * (u - f) ^ 2) := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
    _ = A * (u - f) ^ 2 + D := by
        field_simp
        ring

-- pin: radFloor_mul_le_rad_sq (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:564)
theorem radFloor_mul_le_rad_sq (hg : g.det ≠ 0) (u : ℝ) : radFloor g * (1 + u ^ 2) ≤ rad g u ^ 2 := by
  rw [rad_sq_eq hg]
  exact floor_aux (botNormSq_pos hg) (by have := botNormSq_pos hg; positivity) u

-- pin: max_one_abs_sq_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:568)
theorem max_one_abs_sq_le (u : ℝ) : max 1 |u| ^ 2 ≤ 1 + u ^ 2 := by
  rcases le_total 1 |u| with h | h
  · rw [max_eq_right h, sq_abs]; linarith
  · rw [max_eq_left h]; nlinarith [sq_nonneg u]

-- pin: sqrt_radFloor_mul_le_rad (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:573)
theorem sqrt_radFloor_mul_le_rad (hg : g.det ≠ 0) (u : ℝ) : Real.sqrt (radFloor g) * max 1 |u| ≤ rad g u := by
  have hc := radFloor_pos hg
  have h2 : (Real.sqrt (radFloor g) * max 1 |u|) ^ 2 ≤ rad g u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le]
    exact (mul_le_mul_of_nonneg_left (max_one_abs_sq_le u) hc.le).trans (radFloor_mul_le_rad_sq hg u)
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (rad_pos hg u).le] at h3

-- pin: rad_rpow_neg_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:581)
theorem rad_rpow_neg_le (hg : g.det ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (u : ℝ) :
    rad g u ^ (-β) ≤ Real.sqrt (radFloor g) ^ (-β) * max 1 |u| ^ (-β) := by
  have hpos : 0 < Real.sqrt (radFloor g) * max 1 |u| :=
    mul_pos (Real.sqrt_pos.2 (radFloor_pos hg)) (lt_max_of_lt_left one_pos)
  rw [← Real.mul_rpow (Real.sqrt_nonneg _) (zero_le_one.trans (le_max_left _ _))]
  exact Real.rpow_le_rpow_of_nonpos hpos (sqrt_radFloor_mul_le_rad hg u) (neg_nonpos.2 hβ)

-- pin: norm_le_rad_rpow (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:588)
theorem norm_le_rad_rpow (hg : g.det ≠ 0) {Ψ : ℝ → ℂ} {M β : ℝ}
    (hM : ∀ t, ‖Ψ t‖ ≤ M * Real.exp (-β * t)) (u : ℝ) :
    ‖Ψ (Real.log (rad g u))‖ ≤ M * rad g u ^ (-β) := by
  calc ‖Ψ (Real.log (rad g u))‖ ≤ M * Real.exp (-β * Real.log (rad g u)) := hM _
    _ = M * rad g u ^ (-β) := by rw [Real.rpow_def_of_pos (rad_pos hg u), mul_comm (-β)]

end Constants
section Towers

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

-- pin: factorial_mul_pow_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:601)
theorem factorial_mul_pow_le {k n : ℕ} (hkn : k + 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (k ! : ℝ) * r ^ (k + 1) ≤ ((n ! : ℝ) * max 1 r) ^ (k + 1) := by
  have hn1 : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (k ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le (by omega)
  have h2 : (n ! : ℝ) ≤ (n ! : ℝ) ^ (k + 1) := le_self_pow₀ hn1 (Nat.succ_ne_zero k)
  have h3 : r ^ (k + 1) ≤ max 1 r ^ (k + 1) := pow_le_pow_left₀ hr (le_max_right _ _) _
  calc (k ! : ℝ) * r ^ (k + 1) ≤ (n ! : ℝ) ^ (k + 1) * max 1 r ^ (k + 1) :=
        mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
    _ = ((n ! : ℝ) * max 1 r) ^ (k + 1) := (mul_pow _ _ _).symm

-- pin: norm_iteratedFDeriv_log_rad_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:611)
theorem norm_iteratedFDeriv_log_rad_le (hg : g.det ≠ 0) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u => Real.log (rad g u)) u‖ ≤ towerD g n ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (abs_iteratedDeriv_log_rad_le hg k u).trans (factorial_mul_pow_le hin towerRatio_nonneg)

-- pin: norm_iteratedFDeriv_angle_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:617)
theorem norm_iteratedFDeriv_angle_le (hg : g.det ≠ 0) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (angle g) u‖ ≤ towerD g n ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (abs_iteratedDeriv_angle_le hg k u).trans (factorial_mul_pow_le hin towerRatio_nonneg)

end Towers

end AutomorphicForm.RealIwasawa.ScalarMajorant

namespace AutomorphicForm.RealIwasawa.RealKTower

open AutomorphicForm.RealIwasawa.ScalarMajorant

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

-- pin: norm_iteratedFDeriv_comp_angle_le_of_abs_le_one (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:643)
theorem norm_iteratedFDeriv_comp_angle_le_of_abs_le_one (hg : g.det ≠ 0) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcb : ∀ (j : ℕ) (θ : ℝ), |iteratedDeriv j c θ| ≤ 1) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => c (angle g u)) u‖ ≤ n ! * towerD g n ^ n := by
  have hC : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j c (angle g u)‖ ≤ 1 := by
    intro j _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hcb j _
  have hD : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j (angle g) u‖ ≤ towerD g n ^ j :=
    fun j hj1 hjn => norm_iteratedFDeriv_angle_le hg hj1 hjn u
  have h := norm_iteratedFDeriv_comp_le (g := c) (f := angle g) (n := n)
    hc (contDiff_angle hg) (by exact_mod_cast le_top) u hC hD
  rw [Function.comp_def, mul_one] at h
  exact h

-- pin: norm_iteratedFDeriv_cos_angle_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:657)
theorem norm_iteratedFDeriv_cos_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => Real.cos (angle g u)) u‖ ≤ n ! * towerD g n ^ n :=
  norm_iteratedFDeriv_comp_angle_le_of_abs_le_one hg Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one n u

-- pin: norm_iteratedFDeriv_sin_angle_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:661)
theorem norm_iteratedFDeriv_sin_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => Real.sin (angle g u)) u‖ ≤ n ! * towerD g n ^ n :=
  norm_iteratedFDeriv_comp_angle_le_of_abs_le_one hg Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one n u

-- pin: norm_iteratedFDeriv_neg_sin_angle_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:665)
theorem norm_iteratedFDeriv_neg_sin_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => -Real.sin (angle g u)) u‖ ≤ n ! * towerD g n ^ n := by
  have hneg : (fun u => -Real.sin (angle g u)) = -(fun u => Real.sin (angle g u)) := rfl
  rw [hneg, iteratedFDeriv_neg_apply, norm_neg]
  exact norm_iteratedFDeriv_sin_angle_le hg n u

-- pin: norm_iteratedFDeriv_rot_angle_apply_le (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:671)
theorem norm_iteratedFDeriv_rot_angle_apply_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ∀ i j : Fin 2, ‖iteratedFDeriv ℝ n (fun x => rot (angle g x) i j) u‖ ≤ n ! * towerD g n ^ n := by
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · exact norm_iteratedFDeriv_cos_angle_le hg n u
  · exact norm_iteratedFDeriv_neg_sin_angle_le hg n u
  · exact norm_iteratedFDeriv_sin_angle_le hg n u
  · exact norm_iteratedFDeriv_cos_angle_le hg n u

-- pin: kR_literal_eq_rot_angle (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:679)
theorem kR_literal_eq_rot_angle (hg : g.det ≠ 0) : ∀ i j : Fin 2,
    (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
      = fun x => rot (angle g x) i j := by
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 1 + x * g 1 1)
      = rot (angle g x) 0 0
    rw [rot_apply_00, cos_angle hg, rad_eq_sqrt, div_eq_inv_mul]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (-(g 0 0 + x * g 1 0))
      = rot (angle g x) 0 1
    rw [rot_apply_01, sin_angle hg, rad_eq_sqrt, div_eq_inv_mul, mul_neg]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 0 + x * g 1 0)
      = rot (angle g x) 1 0
    rw [rot_apply_10, sin_angle hg, rad_eq_sqrt, div_eq_inv_mul]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 1 + x * g 1 1)
      = rot (angle g x) 1 1
    rw [rot_apply_11, cos_angle hg, rad_eq_sqrt, div_eq_inv_mul]

-- pin: contDiff_and_exists_bound (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:702)
theorem contDiff_and_exists_bound (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C := by
  refine ⟨fun i j => ?_, fun n => ⟨n ! * towerD g n ^ n,
    mul_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos (towerD_pos n) n), fun i j u => ?_⟩⟩
  · rw [kR_literal_eq_rot_angle hg i j]
    exact contDiff_rot_angle_apply hg i j
  · rw [kR_literal_eq_rot_angle hg i j]
    exact norm_iteratedFDeriv_rot_angle_apply_le hg n u i j

end AutomorphicForm.RealIwasawa.RealKTower

namespace AutomorphicForm.RealIwasawa.Engine

-- pin: solution (S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:729)
theorem contDiff_and_exists_bound_iteratedFDeriv_kR_apply
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C :=
  RealKTower.contDiff_and_exists_bound hg

end AutomorphicForm.RealIwasawa.Engine

end
