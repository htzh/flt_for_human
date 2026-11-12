/-
  The near-zero growth bound for a solution of the unforced Whittaker equation.

  At a spectral parameter `ν` the Whittaker equation `y ^ 2 f'' + (1 / 4 - ν ^ 2 + 2 π k y - 4 π ^ 2 y ^ 2) f = 0`
  has indicial roots `1 / 2 ± ν` at `y = 0`, so a solution grows at most like `y ^ (1 / 2 - |Re ν|)`; the
  same Liouville-transform energy estimate as for the forced equation, kept sharp (no `ε`-loss in the
  exponent), gives that bound and the existence of a bound with some exponent below `1 / 2` on `(0, 1]`.

  This is the unforced half of the local Whittaker analysis of the weight-one lifting.

  Transcribed from the pin's proof file
  `P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode.lean`
  (pinned `aa2d8b3`, 443 lines / 39 declarations) with its statement from the wrapper
  `Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode.lean`,
  and the second headline from the sibling pin file and wrapper
  `S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean` /
  `Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean`, whose private
  prelude is byte-identical and is not transcribed twice.

  The prelude of the Liouville transform — the exponential substitution, the transformed components, the
  energy and its comparison function — is shared with the forced equation's development and is imported.

  spec-pin: Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean
-/
import FLTForHuman.LanglandsTunnell.WhittakerODEGrowth

set_option autoImplicit false

open scoped Real

noncomputable section

namespace LanglandsTunnell

section derivs

variable (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
include hf hf'

variable (ν : ℂ) (k : ℝ)
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
include hfeq

private lemma vp_hasDerivAt (l : ℂ) (t : ℝ) :
    HasDerivAt (vp l f) (l * vp l f t + sfun ν l k t * Gf f t) t := by
  have hG := Gf_hasDerivAt f hf t
  have hH := Hf_hasDerivAt f hf' t
  have h := (hG.const_mul (1 / 2 + l)).sub hH
  have hode := hfeq (eA t) (eA_pos t)
  refine (h.congr_deriv ?_)
  unfold vp Gf Hf sfun
  push_cast
  linear_combination ((eB t : ℝ) : ℂ) * hode

private lemma vm_hasDerivAt (l : ℂ) (t : ℝ) :
    HasDerivAt (vm l f) (-l * vm l f t + sfun ν l k t * Gf f t) t := by
  have hG := Gf_hasDerivAt f hf t
  have hH := Hf_hasDerivAt f hf' t
  have h := (hG.const_mul (1 / 2 - l)).sub hH
  have hode := hfeq (eA t) (eA_pos t)
  refine (h.congr_deriv ?_)
  unfold vm Gf Hf sfun
  push_cast
  linear_combination ((eB t : ℝ) : ℂ) * hode

end derivs

section energy

variable (ν l : ℂ) (k : ℝ) (f : ℝ → ℂ)
variable (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)

include hf hf' hfeq in
private lemma Efun_hasDerivAt_le (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (t : ℝ) :
    ∃ E' : ℝ, HasDerivAt (Efun l f) E' t ∧ E' ≤ rate l k m₀ t * Efun l f t := by
  have hvp := vp_hasDerivAt f hf hf' ν k hfeq l t
  have hvm := vm_hasDerivAt f hf hf' ν k hfeq l t
  have hEp := nsq_hasDerivAt hvp
  have hEm := nsq_hasDerivAt hvm
  refine ⟨_, hEp.add hEm, ?_⟩

  set w := sfun ν l k t * Gf f t with hw
  have hdp := cross_decomp (vp l f t) l w
  have hdm := cross_decomp (vm l f t) (-l) w
  have hcp := cross_le (vp l f t) w
  have hcm := cross_le (vm l f t) w
  have hwn : ‖w‖ = ‖sfun ν l k t‖ * ‖Gf f t‖ := by rw [hw, norm_mul]
  have hS := norm_sfun_le ν l k m₀ hm₀ t
  have hS0 : 0 ≤ ‖sfun ν l k t‖ := norm_nonneg _
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hl0 : 0 < ‖l‖ := norm_pos_iff.mpr hl

  have hg : 2 * ‖Gf f t‖ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := by
    have h1 : ‖vp l f t - vm l f t‖ ≤ ‖vp l f t‖ + ‖vm l f t‖ := norm_sub_le _ _
    rw [vp_sub_vm, norm_mul, norm_mul] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h1

    have h3 := mul_le_mul_of_nonneg_left h1 hLi
    calc 2 * ‖Gf f t‖ = ‖l‖⁻¹ * (2 * ‖l‖ * ‖Gf f t‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := h3
  have hmain := rate_bound ‖vp l f t‖ ‖vm l f t‖ ‖Gf f t‖ ‖sfun ν l k t‖ (mfun k m₀ t) l.re ‖l‖⁻¹
    ((vp l f t).re * w.re + (vp l f t).im * w.im) ((vm l f t).re * w.re + (vm l f t).im * w.im)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hS0 hS hLi hg (by rw [← hwn]; exact hcp) (by rw [← hwn]; exact hcm)

  have hnp : (vp l f t).re * (vp l f t).re + (vp l f t).im * (vp l f t).im = ‖vp l f t‖ * ‖vp l f t‖ := by
    have := nsq_eq (vp l f) t; unfold nsq at this; rw [this]; ring
  have hnm : (vm l f t).re * (vm l f t).re + (vm l f t).im * (vm l f t).im = ‖vm l f t‖ * ‖vm l f t‖ := by
    have := nsq_eq (vm l f) t; unfold nsq at this; rw [this]; ring
  have hEt : Efun l f t = ‖vp l f t‖ * ‖vp l f t‖ + ‖vm l f t‖ * ‖vm l f t‖ := by
    unfold Efun; rw [nsq_eq, nsq_eq]; ring
  rw [hEt]
  unfold rate
  simp only [Complex.neg_re] at hdm
  rw [hdp, hdm, hnp, hnm]
  linarith [hmain]

include hf hf' hfeq in
private lemma Efun_le (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) {t : ℝ} (ht : 0 ≤ t) :
    Efun l f t ≤ Efun l f 0 * Real.exp (Phi l k m₀ t) := by

  set Z : ℝ → ℝ := fun x => Efun l f x * Real.exp (-(Phi l k m₀ x)) with hZdef
  have hZ : ∀ x : ℝ, ∃ Z' : ℝ, HasDerivAt Z Z' x ∧ Z' ≤ 0 := by
    intro x
    obtain ⟨E', hE', hle⟩ := Efun_hasDerivAt_le ν l k f hf hf' hfeq hl m₀ hm₀ x
    have hP : HasDerivAt (fun y => Real.exp (-(Phi l k m₀ y))) (Real.exp (-(Phi l k m₀ x)) * (-(rate l k m₀ x))) x :=
      ((Phi_hasDerivAt l k m₀ x).neg).exp
    refine ⟨_, hE'.mul hP, ?_⟩
    have hexp : 0 < Real.exp (-(Phi l k m₀ x)) := Real.exp_pos _
    have hE0 := Efun_nonneg l f x
    have : E' * Real.exp (-(Phi l k m₀ x)) + Efun l f x * (Real.exp (-(Phi l k m₀ x)) * -rate l k m₀ x)
        = Real.exp (-(Phi l k m₀ x)) * (E' - rate l k m₀ x * Efun l f x) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hexp.le (by linarith)
  have hcont : ContinuousOn Z (Set.Ici 0) := fun x _ => ((hZ x).choose_spec.1.continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ Z (interior (Set.Ici (0 : ℝ))) :=
    fun x _ => ((hZ x).choose_spec.1.differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)), deriv Z x ≤ 0 := by
    intro x _
    obtain ⟨Z', hZ', hle⟩ := hZ x
    rw [hZ'.deriv]; exact hle
  have hanti : AntitoneOn Z (Set.Ici 0) := antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff hderiv
  have h0 : Z t ≤ Z 0 := hanti Set.self_mem_Ici ht ht
  have hZ0 : Z 0 = Efun l f 0 := by simp [hZdef, Phi_zero]
  rw [hZ0] at h0

  have hZt : Z t = Efun l f t * Real.exp (-(Phi l k m₀ t)) := rfl
  rw [hZt] at h0
  have hpos : 0 < Real.exp (Phi l k m₀ t) := Real.exp_pos _
  have := mul_le_mul_of_nonneg_right h0 hpos.le
  rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this

include hf hf' hfeq in
private theorem engine (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ ((1 - (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀)) / 2) := by
  set ρ : ℝ := 2 * |l.re| + 2 * ‖l‖⁻¹ * m₀ with hρdef
  set K : ℝ := 2 * ‖l‖⁻¹ * (2 * π * |k| + 4 * π ^ 2 / 2) with hKdef
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  set Cst : ℝ := ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * Real.exp K) with hCst
  have hCst0 : 0 ≤ Cst := by
    have := Efun_nonneg l f 0; have := Real.exp_pos K; positivity
  refine ⟨Real.sqrt Cst, Real.sqrt_nonneg _, ?_⟩
  intro y hy hy1

  set t : ℝ := -Real.log y with htdef
  have ht : 0 ≤ t := by have := Real.log_nonpos hy.le hy1; linarith
  have hAt : eA t = y := by unfold eA; rw [htdef, neg_neg, Real.exp_log hy]

  have hG : Gf f t = ((eB t : ℝ) : ℂ) * f y := by unfold Gf; rw [hAt]
  have hGn : ‖Gf f t‖ = eB t * ‖f y‖ := by
    rw [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eB_pos t)]
  have hfy_sq : ‖f y‖ ^ 2 = y * ‖Gf f t‖ ^ 2 := by
    rw [hGn, mul_pow, ← hAt, ← mul_assoc, eA_mul_eB_sq, one_mul]

  have hE := Efun_le ν l k f hf hf' hfeq hl m₀ hm₀ ht
  have hgl : 2 * ‖Gf f t‖ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := by
    have h1 : ‖vp l f t - vm l f t‖ ≤ ‖vp l f t‖ + ‖vm l f t‖ := norm_sub_le _ _
    rw [vp_sub_vm, norm_mul, norm_mul] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hLi
    have hl0 : 0 < ‖l‖ := norm_pos_iff.mpr hl
    calc 2 * ‖Gf f t‖ = ‖l‖⁻¹ * (2 * ‖l‖ * ‖Gf f t‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := h3
  have hEt : Efun l f t = ‖vp l f t‖ ^ 2 + ‖vm l f t‖ ^ 2 := by unfold Efun; rw [nsq_eq, nsq_eq]
  have hGsq : ‖Gf f t‖ ^ 2 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * Efun l f t := by
    rw [hEt]
    have hp := norm_nonneg (vp l f t); have hq := norm_nonneg (vm l f t); have hg0 := norm_nonneg (Gf f t)
    have hsum : (‖vp l f t‖ + ‖vm l f t‖) ^ 2 ≤ 2 * (‖vp l f t‖ ^ 2 + ‖vm l f t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖vp l f t‖ - ‖vm l f t‖)]
    have h4 : (2 * ‖Gf f t‖) ^ 2 ≤ (‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgl 2
    have hLi2 : 0 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ := mul_nonneg hLi hLi
    nlinarith [mul_le_mul_of_nonneg_left hsum hLi2]

  have hPhi := Phi_le l k m₀ ht
  have hexp : Real.exp (Phi l k m₀ t) ≤ Real.exp K * y ^ (-ρ) := by
    rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : K + Real.log y * -ρ = ρ * t + K := by rw [htdef]; ring
    rw [this]; exact hPhi
  have hE0 := Efun_nonneg l f 0

  have hsq : ‖f y‖ ^ 2 ≤ Cst * (y * y ^ (-ρ)) := by
    rw [hfy_sq, hCst]
    have hLi2 : 0 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ / 2 := by positivity
    calc y * ‖Gf f t‖ ^ 2 ≤ y * (‖l‖⁻¹ * ‖l‖⁻¹ / 2 * Efun l f t) := by gcongr
      _ ≤ y * (‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * Real.exp (Phi l k m₀ t))) := by gcongr
      _ ≤ y * (‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * (Real.exp K * y ^ (-ρ)))) := by gcongr
      _ = ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * Real.exp K) * (y * y ^ (-ρ)) := by ring
  have hyρ : y * y ^ (-ρ) = (y ^ ((1 - ρ) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    have h1 : y * y ^ (-ρ) = y ^ (1 + -ρ) := by rw [Real.rpow_add hy, Real.rpow_one]
    rw [h1]
    congr 1; push_cast; ring
  rw [hyρ] at hsq
  have hrhs : 0 ≤ Real.sqrt Cst * y ^ ((1 - ρ) / 2) := by positivity
  have hsq' : ‖f y‖ ^ 2 ≤ (Real.sqrt Cst * y ^ ((1 - ρ) / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCst0]; exact hsq
  have := abs_le_of_sq_le_sq hsq' hrhs
  rwa [abs_of_nonneg (norm_nonneg _)] at this

end energy

theorem norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
    (ν : ℂ) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    (ν ≠ 0 → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 / 2 - |ν.re|)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 / 2 - |ν.re| - ε)) := by

  have hsharp : ν ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 / 2 - |ν.re|) := by
    intro hν
    have hm : ‖ν ^ 2 - ν ^ 2‖ ≤ 0 := by simp
    obtain ⟨C, hC0, hC⟩ := engine ν ν k f hf hf' hfeq hν 0 hm
    refine ⟨C, hC0, fun y hy hy1 => ?_⟩
    have h := hC y hy hy1
    have hexp : (1 - (2 * |ν.re| + 2 * ‖ν‖⁻¹ * 0)) / 2 = 1 / 2 - |ν.re| := by ring
    rwa [hexp] at h
  refine ⟨fun hν => ?_, fun ε hε => ?_⟩
  · obtain ⟨C, -, hC⟩ := hsharp hν
    exact ⟨C, hC⟩
  · by_cases hν : ν = 0
    ·
      subst hν
      have hε4 : (0 : ℝ) < ε / 4 := by positivity
      have hl : (((ε / 4 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hε4.ne'
      have hnorm : ‖(((ε / 4 : ℝ) : ℂ))‖ = ε / 4 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε4]
      have hm : ‖(0 : ℂ) ^ 2 - (((ε / 4 : ℝ) : ℂ)) ^ 2‖ ≤ (ε / 4) ^ 2 := by
        rw [show (0 : ℂ) ^ 2 - (((ε / 4 : ℝ) : ℂ)) ^ 2 = -((((ε / 4 : ℝ) : ℂ)) ^ 2) by ring, norm_neg, norm_pow,
          hnorm]
      obtain ⟨C, hC0, hC⟩ := engine 0 (((ε / 4 : ℝ) : ℂ)) k f hf hf' hfeq hl ((ε / 4) ^ 2) hm
      refine ⟨C, fun y hy hy1 => (hC y hy hy1).trans ?_⟩
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 ?_) hC0
      rw [hnorm, Complex.ofReal_re, abs_of_pos hε4, Complex.zero_re, abs_zero]
      have h1 : 2 * (ε / 4)⁻¹ * (ε / 4) ^ 2 = ε / 2 := by field_simp; norm_num
      rw [h1]
      linarith
    · obtain ⟨C, hC0, hC⟩ := hsharp hν
      refine ⟨C, fun y hy hy1 => (hC y hy hy1).trans ?_⟩
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) hC0

theorem exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
    (ν : ℂ) (hre : |ν.re| < 1 / 2) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by
  have hδ : 0 < (1 / 2 - |ν.re|) / 2 := by
    have := abs_nonneg ν.re
    linarith
  obtain ⟨C, hC⟩ :=
    (norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode ν k f hf hf' hfeq).2
      ((1 / 2 - |ν.re|) / 2) hδ
  refine ⟨(1 / 2 - |ν.re|) / 2, hδ, max C 0, fun y hy hy1 => ?_⟩
  have h := hC y hy hy1
  have hexp : 1 / 2 - |ν.re| - (1 / 2 - |ν.re|) / 2 = (1 / 2 - |ν.re|) / 2 := by ring
  rw [hexp] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hy.le _))

end LanglandsTunnell
