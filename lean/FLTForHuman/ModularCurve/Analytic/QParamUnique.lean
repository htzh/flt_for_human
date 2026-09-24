/-
  m3 — the two `qParam`-expansion uniqueness lemmas.

  `qParam_coeff_unique` states the bare-`F` uniqueness: two `HasSum` expansions of
  an arbitrary `F : ℍ → ℂ` in `qParam h` with `ℕ`-indexed coefficients agree. The
  pin's proof goes through `HasFPowerSeriesOnBall`/`FormalMultilinearSeries`; all
  its helpers are `private` here, so only the two headline statements are public.
  `laurent_qParam_coeff_unique` is the `ℤ`-indexed Laurent version, derived from it.

  FLT provenance, pinned `aa2d8b3`:
  * `P2M/Sol/S_ModularCurve_qParam_coeff_unique.lean` (158 lines)
  * `P2M/Sol/S_ModularCurve_laurent_qParam_coeff_unique.lean` (71 lines)
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_qParam_coeff_unique.lean
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false

-- The pin's `letI : FiniteDimensional ℝ ℂ` in `hasFPowerSeriesOnBall_update` is
-- load-bearing (it feeds `FormalMultilinearSeries.le_radius_of_summable`), so the
-- style linter's `let` suggestion cannot be taken; disable it as in
-- `AlgebraicCurve/Defs/Correspondence.lean`.
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

variable {h : ℝ} {F : ℍ → ℂ} {c : ℕ → ℂ}

private lemma norm_qParam_lt_one_of_pos (hh : 0 < h) (τ : ℍ) : ‖𝕢 h (τ : ℂ)‖ < 1 := by
  rw [Periodic.norm_qParam, Real.exp_lt_one_iff, neg_mul, coe_im, neg_mul, neg_div, neg_lt_zero]
  exact div_pos (by positivity [τ.im_pos]) hh

private lemma hasSum_cuspFunction_punctured (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m : ℕ => c m * q ^ m) (cuspFunction h F q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := Periodic.cuspFunction_eq_of_nonzero h (F ∘ ofComplex) hq1
  have h3 : cuspFunction h F q = F τ := by
    simpa [τ, cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : 𝕢 h (τ : ℂ) = q := Periodic.qParam_right_inv hh.ne' hq1
  rw [h3, ← h4]
  exact hF τ

private lemma hasFPowerSeriesOnBall_update (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      letI : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [norm_mul, mul_comm] using
        (hasSum_cuspFunction_punctured hh hF (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [zero_add]
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm] using hasSum_cuspFunction_punctured hh hF hy hy'

private def discFun (h : ℝ) (F : ℍ → ℂ) (c : ℕ → ℂ) : ℂ → ℂ := update (cuspFunction h F) 0 (c 0)

private lemma hasSum_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun m : ℕ => c m * q ^ m) (discFun h F c q) := by
  have hy : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.coe_one, Metric.eball_coe]; simpa using hq
  have h := (hasFPowerSeriesOnBall_update hh hF).hasSum hy
  rw [zero_add] at h
  simpa [discFun, mul_comm] using h

private lemma apply_eq_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (τ : ℍ) : F τ = discFun h F c (𝕢 h (τ : ℂ)) :=
  (hF τ).unique (hasSum_discFun hh hF (norm_qParam_lt_one_of_pos hh τ))

private lemma differentiableOn_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    DifferentiableOn ℂ (discFun h F c) (Metric.ball 0 1) := by
  have h1 := (hasFPowerSeriesOnBall_update hh hF).differentiableOn
  rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h1

private lemma continuousAt_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    ContinuousAt (discFun h F c) q :=
  ((differentiableOn_discFun hh hF).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).continuousAt

private lemma discFun_zero : discFun h F c 0 = c 0 := by simp [discFun]

private theorem mdifferentiable (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ => discFun h F c (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzq : ‖𝕢 h z‖ < 1 := by
      have := norm_qParam_lt_one_of_pos hh ⟨z, hz⟩
      simpa using this
    exact (((differentiableOn_discFun hh hF).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hzq))).comp z
      ((Periodic.differentiable_qParam (h := h)) z)).differentiableWithinAt
  refine h1.congr fun z hz => ?_
  simp only [Function.comp_apply, apply_eq_discFun hh hF, ofComplex_apply_of_im_pos hz]

private theorem tendsto_atImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    Tendsto F atImInfty (𝓝 (c 0)) := by
  have h1 : Tendsto (fun τ : ℍ => discFun h F c (𝕢 h (τ : ℂ))) atImInfty (𝓝 (discFun h F c 0)) :=
    (continuousAt_discFun hh hF (q := 0) (by simp)).tendsto.comp (qParam_tendsto_atImInfty hh)
  rw [discFun_zero] at h1
  exact h1.congr fun τ => (apply_eq_discFun hh hF τ).symm

private theorem periodic (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    Periodic (F ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + h).im := by simpa using hw
    simp only [Function.comp_apply, apply_eq_discFun hh hF, ofComplex_apply_of_im_pos hw,
      ofComplex_apply_of_im_pos hw']
    congr 1
    simp only [Periodic.qParam]
    rw [show 2 * ↑Real.pi * Complex.I * (w + ↑h) / ↑h = 2 * ↑Real.pi * Complex.I * w / ↑h + 2 * ↑Real.pi * Complex.I by
      field_simp [(Complex.ofReal_ne_zero.mpr hh.ne')]]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · push Not at hw
    have hw' : (w + h).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hw' hw]

private theorem coeff_unique {d : ℕ → ℂ} (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => d m * 𝕢 h (τ : ℂ) ^ m) (F τ)) : c = d := by
  have hc := hasFPowerSeriesOnBall_update hh hF
  have hd := hasFPowerSeriesOnBall_update hh hF'

  have hlim : ∀ {e : ℕ → ℂ}, HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (e 0)) (.ofScalars ℂ e) 0 1 →
      Tendsto (cuspFunction h F) (𝓝[≠] 0) (𝓝 (e 0)) := by
    intro e he
    have h1 : Tendsto (update (cuspFunction h F) 0 (e 0)) (𝓝[≠] 0) (𝓝 (e 0)) := by
      have := he.hasFPowerSeriesAt.continuousAt.tendsto
      rw [update_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using update_of_ne hz ..
  have h0 : c 0 = d 0 := tendsto_nhds_unique (hlim hc) (hlim hd)
  have hd' : HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ d) 0 1 := h0 ▸ hd
  have heq := hc.hasFPowerSeriesAt.eq_formalMultilinearSeries hd'.hasFPowerSeriesAt
  funext m
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) heq

end Realized

theorem qParam_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c d : ℕ → ℂ)
    (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hd : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => d m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) :
    c = d :=
  Realized.coeff_unique hh hc hd

namespace QexpN

private theorem hasSum_shift (h : ℝ) (F : UpperHalfPlane → ℂ) (C : LaurentSeries ℂ) (M : ℕ)
    (hC : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => C.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hsupp : ∀ m : ℤ, m < -(M : ℤ) → C.coeff m = 0) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => C.coeff ((n : ℤ) - M) * 𝕢 h (τ : ℂ) ^ n)
      (F τ * 𝕢 h (τ : ℂ) ^ (M : ℤ)) := by
  have hq : 𝕢 h (τ : ℂ) ≠ 0 := Periodic.qParam_ne_zero _
  have h1 := (hC τ).mul_right (𝕢 h (τ : ℂ) ^ (M : ℤ))
  have hinj : Function.Injective fun n : ℕ => (n : ℤ) - M := fun a b hab => by simpa using hab
  refine ((hinj.hasSum_iff ?_).mpr h1).congr_fun fun n => ?_
  · intro m hm
    have hm' : m < -(M : ℤ) := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m + M).toNat, by simp; omega⟩
    rw [hsupp m hm', zero_mul, zero_mul]
  · simp only [Function.comp_apply]
    conv_rhs => rw [mul_assoc, ← zpow_add₀ hq, sub_add_cancel]
    rw [zpow_natCast]

private theorem laurent_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ)
    (A B : LaurentSeries ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => B.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    A = B := by
  set M : ℕ := max (-A.order).toNat (-B.order).toNat with hM
  have hsA : ∀ m : ℤ, m < -(M : ℤ) → A.coeff m = 0 := by
    intro m hm
    refine HahnSeries.coeff_eq_zero_of_lt_order ?_
    omega
  have hsB : ∀ m : ℤ, m < -(M : ℤ) → B.coeff m = 0 := by
    intro m hm
    refine HahnSeries.coeff_eq_zero_of_lt_order ?_
    omega
  have hcd := qParam_coeff_unique h hh (fun τ => F τ * 𝕢 h (τ : ℂ) ^ (M : ℤ))
    (fun n : ℕ => A.coeff ((n : ℤ) - M)) (fun n : ℕ => B.coeff ((n : ℤ) - M))
    (hasSum_shift h F A M hA hsA) (hasSum_shift h F B M hB hsB)
  ext m
  rcases lt_or_ge m (-(M : ℤ)) with hm | hm
  · rw [hsA m hm, hsB m hm]
  · have hm2 : m = (((m + M).toNat : ℕ) : ℤ) - M := by omega
    rw [hm2]
    exact congrFun hcd (m + M).toNat

end QexpN

theorem laurent_qParam_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ)
    (A B : LaurentSeries ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => B.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) :
    A = B :=
  QexpN.laurent_unique h hh F A B hA hB

end ModularCurve

end
