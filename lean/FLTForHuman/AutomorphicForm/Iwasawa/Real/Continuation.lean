/-
  The real-place Whittaker (Jacquet) integral: continuity, holomorphy and decay.

  The pin develops the integral `j w t = ∫ x, amp k x * (1+x²)^{-w} * exp(-2πi t x)` by
  dominated convergence (`clause_i`), differentiation under the integral (`clause_ii`)
  and rapid decay in `t` from the uniform real decay engine (`clause_iii`, which calls
  `Engine.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact`).

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import FLTForHuman.AutomorphicForm.Iwasawa.Real.Decay

open Set MeasureTheory
open scoped ContDiff FourierTransform Topology

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm.RealIwasawa.Ws1.HARCHR

-- pin: amp (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:23)
private def amp (k : ℤ) (x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k

-- pin: F (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:26)
private def F (k : ℤ) (w : ℂ) (t x : ℝ) : ℂ :=
  amp k x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))

-- pin: one_add_sq_pos (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:29)
private theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

-- pin: sqrt_pos' (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:31)
private theorem sqrt_pos' (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (one_add_sq_pos x)

-- pin: ofReal_sqrt_ne_zero (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:33)
private theorem ofReal_sqrt_ne_zero (x : ℝ) : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (sqrt_pos' x).ne'

-- pin: sub_I_ne_zero (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:36)
private theorem sub_I_ne_zero (x : ℝ) : ((x : ℝ) : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

-- pin: norm_sub_I (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:41)
private theorem norm_sub_I (x : ℝ) : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  have h : ((x : ℝ) : ℂ) - Complex.I = (x : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_add_mul_I]
  congr 1; ring

-- pin: norm_amp (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:46)
private theorem norm_amp (k : ℤ) (x : ℝ) : ‖amp k x‖ = 1 := by
  rw [amp, norm_zpow, norm_div, norm_sub_I, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_self (sqrt_pos' x).ne', one_zpow]

-- pin: norm_base_cpow (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:50)
private theorem norm_base_cpow (w : ℂ) (x : ℝ) : ‖(((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)‖ = (1 + x ^ 2) ^ (-w.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x), Complex.neg_re]

-- pin: norm_expI (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:53)
private theorem norm_expI (r : ℝ) : ‖Complex.exp (-((r : ℂ) * Complex.I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

-- pin: norm_F (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:56)
private theorem norm_F (k : ℤ) (w : ℂ) (t x : ℝ) : ‖F k w t x‖ = (1 + x ^ 2) ^ (-w.re) := by
  rw [F, norm_mul, norm_mul, norm_amp, norm_base_cpow, norm_expI, one_mul, mul_one]

-- pin: norm_F_le (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:59)
private theorem norm_F_le (k : ℤ) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) (t x : ℝ) : ‖F k w t x‖ ≤ (1 + x ^ 2) ^ (-σ) := by
  rw [norm_F]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (neg_le_neg hw)

-- pin: integrable_dom (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:63)
private theorem integrable_dom {σ : ℝ} (hσ : 1 / 2 < σ) : Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-σ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
    (by rw [Module.finrank_self]; push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

-- pin: continuous_amp (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:71)
private theorem continuous_amp (k : ℤ) : Continuous (amp k) := by
  unfold amp
  refine Continuous.zpow₀ ?_ k (fun x => Or.inl (div_ne_zero (sub_I_ne_zero x) (ofReal_sqrt_ne_zero x)))
  exact (Complex.continuous_ofReal.sub continuous_const).div
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))))
    (fun x => ofReal_sqrt_ne_zero x)

-- pin: continuous_F (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:78)
private theorem continuous_F (k : ℤ) : Continuous (fun p : (ℂ × ℝ) × ℝ => F k p.1.1 p.1.2 p.2) := by
  unfold F
  refine (((continuous_amp k).comp continuous_snd).mul ?_).mul ?_
  · refine Continuous.cpow ?_ (continuous_fst.comp continuous_fst).neg ?_
    · exact Complex.continuous_ofReal.comp ((continuous_const.add (continuous_pow 2)).comp continuous_snd)
    · intro p
      exact Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos _)
  · refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const).neg
    exact Complex.continuous_ofReal.comp
      (((continuous_const.mul (continuous_snd.comp continuous_fst)).mul continuous_snd))

-- pin: continuous_F_x (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:89)
private theorem continuous_F_x (k : ℤ) (w : ℂ) (t : ℝ) : Continuous (fun x => F k w t x) := by
  have h : Continuous (fun x : ℝ => (((w, t), x) : (ℂ × ℝ) × ℝ)) := continuous_const.prodMk continuous_id
  have h2 := (continuous_F k).comp h
  exact h2

-- pin: continuousAt_F_p (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:94)
private theorem continuousAt_F_p (k : ℤ) (x : ℝ) (p₀ : ℂ × ℝ) : ContinuousAt (fun p : ℂ × ℝ => F k p.1 p.2 x) p₀ := by
  have h : Continuous (fun p : ℂ × ℝ => ((p, x) : (ℂ × ℝ) × ℝ)) := continuous_id.prodMk continuous_const
  have h2 := ((continuous_F k).comp h).continuousAt (x := p₀)
  exact h2

-- pin: integrable_F (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:99)
private theorem integrable_F (k : ℤ) {w : ℂ} (hw : 1 / 2 < w.re) (t : ℝ) : Integrable (fun x => F k w t x) :=
  (integrable_dom hw).mono' (continuous_F_x k w t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_F_le k le_rfl t x)

-- pin: clause_i (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:103)
private theorem clause_i (k : ℤ) :
    ContinuousOn (fun p : ℂ × ℝ => ∫ x : ℝ, F k p.1 p.2 x) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) := by
  intro p₀ hp₀
  apply ContinuousAt.continuousWithinAt
  have hw₀ : 1 / 2 < p₀.1.re := (Set.mem_prod.mp hp₀).1
  set σ : ℝ := (1 / 2 + p₀.1.re) / 2 with hσdef
  have hσ : 1 / 2 < σ := by rw [hσdef]; linarith
  have hσw : σ < p₀.1.re := by rw [hσdef]; linarith
  have hnhds : ∀ᶠ p : ℂ × ℝ in 𝓝 p₀, σ < p.1.re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).mem_nhds hσw
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun p => (continuous_F_x k p.1 p.2).aestronglyMeasurable)
    (hnhds.mono fun p hp => Filter.Eventually.of_forall fun x => norm_F_le k hp.le _ _)
    (integrable_dom hσ)
    (Filter.Eventually.of_forall fun x => continuousAt_F_p k x p₀)

-- pin: hasDerivAt_F (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:119)
private theorem hasDerivAt_F (k : ℤ) (t x : ℝ) (w : ℂ) :
    HasDerivAt (fun w => F k w t x) (F k w t x * (-((Real.log (1 + x ^ 2) : ℝ) : ℂ))) w := by
  have h0 : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (one_add_sq_pos x).ne'
  have h1 : HasDerivAt (fun w : ℂ => (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w))
      ((((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * Complex.log (((1 + x ^ 2 : ℝ) : ℂ)) * (-1)) w :=
    ((hasDerivAt_id w).neg).const_cpow (Or.inl h0)
  have h2 := (h1.const_mul (amp k x)).mul_const (Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)))
  unfold F
  refine h2.congr_deriv ?_
  rw [Complex.ofReal_log (one_add_sq_pos x).le]
  ring

-- pin: continuous_logterm (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:131)
private theorem continuous_logterm : Continuous (fun x : ℝ => -((Real.log (1 + x ^ 2) : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.comp ((continuous_const.add (continuous_pow 2)).log
    fun x => (one_add_sq_pos x).ne')).neg

-- pin: norm_logterm (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:135)
private theorem norm_logterm (x : ℝ) : ‖-((Real.log (1 + x ^ 2) : ℝ) : ℂ)‖ = Real.log (1 + x ^ 2) := by
  rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg x]))]

-- pin: clause_ii (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:138)
private theorem clause_ii (k : ℤ) (t : ℝ) : DifferentiableOn ℂ (fun w : ℂ => ∫ x : ℝ, F k w t x) {w : ℂ | 1 / 2 < w.re} := by
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  have hw₀' : 1 / 2 < w₀.re := hw₀
  set σ₁ : ℝ := (1 / 2 + w₀.re) / 2 with hσ₁def
  set σ₂ : ℝ := (σ₁ + w₀.re) / 2 with hσ₂def
  have hσ₁ : 1 / 2 < σ₁ := by rw [hσ₁def]; linarith
  have h12 : σ₁ < σ₂ := by rw [hσ₂def, hσ₁def]; linarith
  have hσ₂w : σ₂ < w₀.re := by rw [hσ₂def, hσ₁def]; linarith
  set δ : ℝ := σ₂ - σ₁ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hs : {w : ℂ | σ₂ < w.re} ∈ 𝓝 w₀ := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσ₂w
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w x => F k w t x) (F' := fun w x => F k w t x * (-((Real.log (1 + x ^ 2) : ℝ) : ℂ)))
    (x₀ := w₀) (bound := fun x => δ⁻¹ * (1 + x ^ 2) ^ (-σ₁)) hs
    (Filter.Eventually.of_forall fun w => (continuous_F_x k w t).aestronglyMeasurable)
    (integrable_F k hw₀' t)
    ((continuous_F_x k w₀ t).mul continuous_logterm).aestronglyMeasurable
    ?_ ((integrable_dom hσ₁).const_mul δ⁻¹)
    (Filter.Eventually.of_forall fun x w _ => hasDerivAt_F k t x w)
  · exact key.2.differentiableAt
  · refine Filter.Eventually.of_forall fun x w hw => ?_
    have hw' : σ₂ < w.re := hw
    have hb : (0 : ℝ) ≤ 1 + x ^ 2 := (one_add_sq_pos x).le
    rw [norm_mul, norm_logterm]
    calc ‖F k w t x‖ * Real.log (1 + x ^ 2)
        ≤ (1 + x ^ 2) ^ (-σ₂) * ((1 + x ^ 2) ^ δ / δ) :=
          mul_le_mul (norm_F_le k hw'.le t x) (Real.log_le_rpow_div hb hδ) (Real.log_nonneg (by nlinarith [sq_nonneg x]))
            (Real.rpow_nonneg hb _)
      _ = δ⁻¹ * (1 + x ^ 2) ^ (-σ₁) := by
          rw [mul_div_assoc', ← Real.rpow_add (one_add_sq_pos x), show -σ₂ + δ = -σ₁ by rw [hδdef]; ring]
          ring

-- pin: Tame (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:171)
private def Tame (f : ℝ → ℂ) : Prop := ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ x : ℝ, ‖iteratedFDeriv ℝ n f x‖ ≤ C

-- pin: Tame.const (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:173)
private theorem Tame.const (c : ℂ) : Tame (fun _ => c) := by
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun x => ?_⟩⟩
  cases n with
  | zero => rw [norm_iteratedFDeriv_zero]
  | succ n => rw [iteratedFDeriv_succ_const]; simp

-- pin: Tame.add (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:179)
private theorem Tame.add {f g : ℝ → ℂ} (hf : Tame f) (hg : Tame g) : Tame (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 n
  obtain ⟨D, hD⟩ := hg.2 n
  refine ⟨C + D, fun x => ?_⟩
  have h := iteratedFDeriv_add_apply (i := n) (hf.1.of_le (mod_cast le_top)).contDiffAt
    (hg.1.of_le (mod_cast le_top)).contDiffAt (x := x)
  rw [show (fun x => f x + g x) = f + g from rfl, h]
  exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))

-- pin: Tame.mul (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:189)
private theorem Tame.mul {f g : ℝ → ℂ} (hf : Tame f) (hg : Tame g) : Tame (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  choose C hC using hf.2
  choose D hD using hg.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i * D (n - i), fun x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf.1 hg.1 x (n := n) (mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have hCi : 0 ≤ C i := (norm_nonneg _).trans (hC i x)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i x) (Nat.cast_nonneg _)) (hD (n - i) x) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hCi)

-- pin: Tame.pow (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:200)
private theorem Tame.pow {f : ℝ → ℂ} (hf : Tame f) : ∀ m : ℕ, Tame (fun x => f x ^ m)
  | 0 => by simp only [pow_zero]; exact Tame.const 1
  | m + 1 => by simp only [pow_succ]; exact (Tame.pow hf m).mul hf

-- pin: Tame.ofReal (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:204)
private theorem Tame.ofReal {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x : ℝ, ‖iteratedFDeriv ℝ n c x‖ ≤ C) :
    Tame (fun x => ((c x : ℝ) : ℂ)) := by
  have hcomp : (fun x => ((c x : ℝ) : ℂ)) = Complex.ofRealCLM ∘ c := rfl
  refine ⟨by rw [hcomp]; exact Complex.ofRealCLM.contDiff.comp hc, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hb n
  refine ⟨‖Complex.ofRealCLM‖ * C, fun x => ?_⟩
  rw [hcomp]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.ofRealCLM hc.contDiffAt (mod_cast le_top)).trans ?_
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

-- pin: c00 (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:214)
private def c00 (x : ℝ) : ℝ := (Real.sqrt (1 + x ^ 2))⁻¹ * x
-- pin: c01 (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:215)
private def c01 (x : ℝ) : ℝ := (Real.sqrt (1 + x ^ 2))⁻¹ * (-1)

-- pin: tame_c00_c01 (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:217)
private theorem tame_c00_c01 : Tame (fun x => ((c00 x : ℝ) : ℂ)) ∧ Tame (fun x => ((c01 x : ℝ) : ℂ)) := by
  obtain ⟨hcd, hbd⟩ := AutomorphicForm.RealIwasawa.Engine.contDiff_and_exists_bound_iteratedFDeriv_kR_apply
    (g := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp)
  have e00 : (fun x : ℝ => (Real.sqrt (((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
      + ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2))⁻¹
      * (!![(1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1,
            -((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0);
           (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0,
            (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
      = c00 := by
    funext x; simp [c00]
  have e01 : (fun x : ℝ => (Real.sqrt (((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
      + ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2))⁻¹
      * (!![(1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1,
            -((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0);
           (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0,
            (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 1)
      = c01 := by
    funext x; simp [c01]
  refine ⟨Tame.ofReal ?_ fun n => ?_, Tame.ofReal ?_ fun n => ?_⟩
  · have := hcd 0 0; rwa [e00] at this
  · obtain ⟨C, -, hC⟩ := hbd n
    refine ⟨C, fun x => ?_⟩
    have := hC 0 0 x; rwa [e00] at this
  · have := hcd 0 1; rwa [e01] at this
  · obtain ⟨C, -, hC⟩ := hbd n
    refine ⟨C, fun x => ?_⟩
    have := hC 0 1 x; rwa [e01] at this

-- pin: q (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:246)
private def q (ε : ℂ) (x : ℝ) : ℂ := ((c00 x : ℝ) : ℂ) + ε * ((c01 x : ℝ) : ℂ)

-- pin: tame_q (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:248)
private theorem tame_q (ε : ℂ) : Tame (q ε) :=
  tame_c00_c01.1.add ((Tame.const ε).mul tame_c00_c01.2)

-- pin: q_I (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:251)
private theorem q_I (x : ℝ) : q Complex.I x = (((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  have hs := ofReal_sqrt_ne_zero x
  simp only [q, c00, c01]
  push_cast
  field_simp
  ring

-- pin: q_negI (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:258)
private theorem q_negI (x : ℝ) : q (-Complex.I) x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ))⁻¹ := by
  have hs := ofReal_sqrt_ne_zero x
  have hx := sub_I_ne_zero x
  have h1 : q (-Complex.I) x = (((x : ℝ) : ℂ) + Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
    simp only [q, c00, c01]
    push_cast
    field_simp
  rw [h1, inv_div, div_eq_div_iff hs hx]
  calc (((x : ℝ) : ℂ) + Complex.I) * (((x : ℝ) : ℂ) - Complex.I) = ((x : ℝ) : ℂ) ^ 2 + 1 := by
        ring_nf; rw [Complex.I_sq]; ring
    _ = ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (one_add_sq_pos x).le]; push_cast; ring

-- pin: amp_eq (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:271)
private theorem amp_eq (k : ℤ) : (0 ≤ k ∧ amp k = fun x => q Complex.I x ^ k.natAbs) ∨
    (k < 0 ∧ amp k = fun x => q (-Complex.I) x ^ k.natAbs) := by
  rcases le_or_gt 0 k with hk | hk
  · refine Or.inl ⟨hk, funext fun x => ?_⟩
    rw [amp, q_I]
    conv_lhs => rw [← Int.natAbs_of_nonneg hk]
    rw [zpow_natCast]
  · refine Or.inr ⟨hk, funext fun x => ?_⟩
    rw [amp, q_negI, inv_pow]
    conv_lhs => rw [show k = -((k.natAbs : ℕ) : ℤ) by rw [Int.ofNat_natAbs_of_nonpos hk.le, neg_neg]]
    rw [zpow_neg, zpow_natCast]

-- pin: tame_amp (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:283)
private theorem tame_amp (k : ℤ) : Tame (amp k) := by
  rcases amp_eq k with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact (tame_q _).pow _

-- pin: sqrt_cpow (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:286)
private theorem sqrt_cpow (x : ℝ) (w : ℂ) :
    ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ (-(2 * w)) = (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-w) := by
  have h0 : (0 : ℝ) < 1 + x ^ 2 := one_add_sq_pos x
  have hs : 0 < Real.sqrt (1 + x ^ 2) := sqrt_pos' x
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h0.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log h0.le, Real.log_sqrt h0.le]
  congr 1
  push_cast
  ring

-- pin: clause_iii (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:297)
private theorem clause_iii (k : ℤ) (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ {w : ℂ | 1 / 2 < w.re}) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ t : ℝ, ‖∫ x : ℝ, F k w t x‖ ≤ C * (1 + |t|) ^ (-(N : ℝ)) := by
  have hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ ({1} : Set (Matrix (Fin 2) (Fin 2) ℝ)), ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n ((fun (_ : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) => amp k x) g) x‖ ≤ C := by
    intro n
    obtain ⟨C, hC⟩ := (tame_amp k).2 n
    exact ⟨max C 1, lt_max_of_lt_right one_pos, fun _ _ x => (hC x).trans (le_max_left _ _)⟩
  obtain ⟨C, hC, hb⟩ :=
    AutomorphicForm.RealIwasawa.Engine.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
      ({1} : Set (Matrix (Fin 2) (Fin 2) ℝ)) isCompact_singleton (by simp)
      ((fun w : ℂ => 2 * w) '' K) (hK.image (by fun_prop))
      (by
        rintro _ ⟨w, hw, rfl⟩
        have := hKs hw
        simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at this ⊢
        linarith)
      (fun (_ : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) => amp k x) (fun _ _ => (tame_amp k).1) hPB
      (ContinuousLinearMap.mul ℝ ℝ) one_pos
      (fun ξ => ⟨1, by simp, by simp⟩) N
  refine ⟨C, hC, fun w hw t => ?_⟩
  have h := hb 1 (Set.mem_singleton 1) (2 * w) ⟨w, hw, rfl⟩ t
  have hint : VectorFourier.fourierIntegral 𝐞 volume (ContinuousLinearMap.mul ℝ ℝ).toLinearMap₁₂
      (fun x => ((Real.sqrt (((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
        + ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℂ) ^ (-(2 * w)))
        * (fun (_ : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) => amp k x) 1 x) t
      = ∫ x : ℝ, F k w t x := by
    rw [VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    have hr : Real.sqrt (((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
        + ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) = Real.sqrt (1 + x ^ 2) := by
      simp
    have hL : (ContinuousLinearMap.mul ℝ ℝ).toLinearMap₁₂ x t = x * t := by simp
    rw [hr, hL, sqrt_cpow, F]
    have he : Complex.exp (((2 * Real.pi * -(x * t) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) := by
      congr 1; push_cast; ring
    rw [he]
    ring
  rw [← hint]
  simpa only [Real.norm_eq_abs] using h

end AutomorphicForm.RealIwasawa.Ws1.HARCHR

namespace AutomorphicForm.RealIwasawa.Engine

open AutomorphicForm.RealIwasawa.Ws1.HARCHR in
-- pin: solution (S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:342)
theorem continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (k : ℤ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ContinuousOn (fun p : ℂ × ℝ => j p.1 p.2) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) ∧
    (∀ t : ℝ, DifferentiableOn ℂ (fun w : ℂ => j w t) {w : ℂ | 1 / 2 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | 1 / 2 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, ‖j w t‖ ≤ C * (1 + |t|) ^ (-(N : ℝ))) := by
  intro j
  have hj : j = fun w t => ∫ x : ℝ, F k w t x := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hj]
    exact clause_i k
  · intro t
    rw [hj]
    exact clause_ii k t
  · intro K hK hKs N
    rw [hj]
    exact clause_iii k K hK hKs N

end AutomorphicForm.RealIwasawa.Engine

end
