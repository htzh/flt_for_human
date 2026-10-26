/-
  Pompeiu's identity for `∂̄` in one complex variable.

  Write `∂̄h = (∂ₓh + I ∂ᵧh) / 2` for a function `h : ℂ → ℂ` of two real variables.  For `h` of
  class `C¹` with compact support: if `G` is holomorphic on an open `V` containing the support
  of `h`, then `∫ z, G z * ∂̄h z = 0` — integration by parts against the two partial derivatives
  and the Cauchy–Riemann equations kill the integral.  The Cauchy kernel `z ↦ (z - a)⁻¹` is the
  fundamental solution of `∂̄`: `∫ z, (z - a)⁻¹ * ∂̄h z = -π * h a`.  The proof splits `h` as
  `h = h * bumpKernel + h * (1 - bumpKernel)` for a smooth cutoff `bumpKernel` equal to `1` on `‖z - a‖ ≤ ε` and to `0` on
  `‖z - a‖ ≥ 2ε`: the far part has support in the punctured disc, where `(z - a)⁻¹` is
  holomorphic, so it contributes `0` by the previous identity, while the near part is handled by
  writing `h = h a + (h - h a)` and integrating the model kernel `∂̄bumpKernel` explicitly, which gives
  `-π * h a` with an error bounded by `O(ε)`; letting `ε → 0` finishes.  Consequently, if `F`
  has only simple poles on the open set `U`, i.e. `F z = c a / (z - a) + analytic` near every
  `a ∈ U`, then `∫ z, F z * ∂̄h z = -π * ∑ᶠ a, c a * h a` for `h` supported in `U`: subtract the
  finite sum of the pinned kernels (finitely many poles meet the support), remove the resulting
  removable singularities from `F`, and apply the holomorphic case.  The prelude is that a
  function with only simple poles is locally integrable on `U`.

  spec-pin: Theorems/Thm_Complex_locallyIntegrableOn_of_simplePoles.lean
  spec-pin: Theorems/Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean
  spec-pin: Theorems/Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.lean
  spec-pin: Theorems/Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.lean
  spec-pin: P2M/Sol/S_Complex_locallyIntegrableOn_of_simplePoles.lean   -- comparable copy
  spec-pin: P2M/Sol/S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean   -- comparable copy
  spec-pin: P2M/Sol/S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.lean   -- comparable copy
  spec-pin: P2M/Sol/S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.lean   -- comparable copy
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic
import FLTForHuman.Analysis.Complex.Dbar

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology Real InnerProductSpace

namespace Complex

/-! ### Local integrability of a function with only simple poles -/

private theorem integrableOn_const_div (c : ℂ) (r : ℝ) :
    IntegrableOn (fun x : ℂ => c / x) (ball 0 r) := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := ‖c‖) (α := 1) ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_div, Real.rpow_neg_one, div_eq_mul_inv]
  · exact (measurable_const.div measurable_id).aestronglyMeasurable

private theorem integrableOn_const_div_sub (c a : ℂ) (r : ℝ) :
    IntegrableOn (fun z : ℂ => c / (z - a)) (ball a r) := by
  have hT := (measurePreserving_add_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (measurableEmbedding_addRight a) (f := fun z : ℂ => c / (z - a)) (s := ball a r)
  rw [← hT]
  have hpre : (fun x : ℂ => x + a) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, add_sub_cancel_right, sub_zero]
  rw [hpre]
  simp only [Function.comp_def, add_sub_cancel_right]
  exact integrableOn_const_div c r

/-- A function with only simple poles on an open set `U` is locally integrable there: near each
`a ∈ U` it is the sum of `c a / (z - a)`, which is integrable on a ball, and of an analytic
function, which is continuous on a neighbourhood. -/
theorem locallyIntegrableOn_of_simplePoles (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U := by
  -- `hU` is the pin's hypothesis; the argument below needs only analyticity near each point.
  have _ := hU
  intro a ha
  obtain ⟨g, hg, hev⟩ := hloc a ha

  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hg.eventually_analyticAt

  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₂, hε₂, hball₂⟩ := hev
  set r : ℝ := min ε₁ ε₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr₁ : r < ε₁ := by
    have := min_le_left ε₁ ε₂; rw [hr]; linarith
  have hr₂ : r < ε₂ := by
    have := min_le_right ε₁ ε₂; rw [hr]; linarith
  refine ⟨ball a r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr0), ?_⟩

  have hgc : ContinuousOn g (closedBall a r) := fun z hz =>
    (hball₁ (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) hr₁)) :
      AnalyticAt ℂ g z).continuousAt.continuousWithinAt
  have hgi : IntegrableOn g (ball a r) :=
    (hgc.integrableOn_compact (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hmodel : IntegrableOn (fun z => c a / (z - a) + g z) (ball a r) :=
    (integrableOn_const_div_sub (c a) a r).add hgi

  refine hmodel.congr_fun_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
  filter_upwards [(Set.finite_singleton a).countable.ae_notMem volume] with z hza hz
  rw [mem_singleton_iff] at hza
  exact (hball₂ (mem_ball.1 (ball_subset_ball hr₂.le hz)) hza).symm

/-! ### The holomorphic case: `∫ G · ∂̄h = 0` -/

/-- **Pompeiu's identity, holomorphic case.**  For `G` holomorphic on an open `V` containing the
support of the `C¹` compactly supported `h`, the integral of `G · ∂̄h` vanishes. -/
theorem integral_mul_dbar_eq_zero_of_differentiableOn (V : Set ℂ) (hV : IsOpen V)
    (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
    ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 := by
  have hGa : AnalyticOnNhd ℂ G V := hG.analyticOnNhd hV
  have hGcont : ContinuousOn G V := hG.continuousOn
  have hGc1 : ContDiffOn ℝ 1 G V := (hGa.contDiffOn (n := 1) hV.uniqueDiffOn).restrict_scalars ℝ
  have hdGcont : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ G z v) V := fun v =>
    (hGc1.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hdh : ∀ v : ℂ, Continuous fun z => fderiv ℝ h z v := fun v =>
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdh_supp : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ h z v := fun v =>
    hsupp.fderiv_apply ℝ v
  have hdh_tsupp : ∀ v : ℂ, tsupport (fun z => fderiv ℝ h z v) ⊆ V := fun v =>
    (tsupport_fderiv_apply_subset ℝ v).trans hV'
  have hI2 : ∀ v : ℂ, Integrable fun z => G z * fderiv ℝ h z v := fun v =>
    integrable_mul_of_tsupport_subset hV hGcont (hdh v) (hdh_supp v) (hdh_tsupp v)

  have hibp : ∀ v : ℂ, ∫ z, G z * fderiv ℝ h z v = -∫ z, fderiv ℝ G z v * h z := by
    intro v
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_tsupport_subset hV (hdGcont v) hh.continuous hsupp hV'
    · exact hI2 v
    · exact integrable_mul_of_tsupport_subset hV hGcont hh.continuous hsupp hV'
    · intro x hx
      exact (hG.differentiableAt (hV.mem_nhds (hV' hx))).restrictScalars ℝ
    · intro x _
      exact hhd x

  have hCR : ∀ z ∈ V, fderiv ℝ G z 1 + I * fderiv ℝ G z I = 0 := by
    intro z hz
    have hd : DifferentiableAt ℂ G z := hG.differentiableAt (hV.mem_nhds hz)
    rw [hd.hasDerivAt.complexToReal_fderiv.fderiv]
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
    linear_combination deriv G z * I_mul_I
  have hA : ∫ z, fderiv ℝ G z 1 * h z = ∫ z, (-I) * (fderiv ℝ G z I * h z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport h
    · have := hCR z (hV' hz)
      show fderiv ℝ G z 1 * h z = (-I) * (fderiv ℝ G z I * h z)
      linear_combination (h z) * this
    · simp [image_eq_zero_of_notMem_tsupport hz]
  calc ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2)
      = ∫ z, ((1 / 2 : ℂ) * (G z * fderiv ℝ h z 1) + (I / 2) * (G z * fderiv ℝ h z I)) := by
        congr 1
        funext z
        ring
    _ = (1 / 2 : ℂ) * (∫ z, G z * fderiv ℝ h z 1) + (I / 2) * (∫ z, G z * fderiv ℝ h z I) := by
        rw [integral_add ((hI2 1).const_mul _) ((hI2 I).const_mul _), integral_const_mul,
          integral_const_mul]
    _ = 0 := by
        rw [hibp 1, hibp I, hA, integral_const_mul]
        ring

/-! ### The Cauchy kernel: `∫ z, (z - a)⁻¹ * ∂̄h z = -π * h a` -/

section FundamentalSolution

/-- A smooth cutoff of the real line: `1` on `(-∞, 1]` and `0` on `[2, ∞)`. -/
private def bumpProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

private theorem bumpProfile_contDiff : ContDiff ℝ 2 bumpProfile :=
  (Real.smoothTransition.contDiff (n := 2)).comp (contDiff_const.sub contDiff_id)

private theorem bumpProfile_of_le_one {t : ℝ} (ht : t ≤ 1) : bumpProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem bumpProfile_of_two_le {t : ℝ} (ht : 2 ≤ t) : bumpProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem bumpProfile_differentiable : Differentiable ℝ bumpProfile := bumpProfile_contDiff.differentiable (by norm_num)

private theorem deriv_φ_continuous : Continuous (deriv bumpProfile) :=
  bumpProfile_contDiff.continuous_deriv (by norm_num)

private theorem deriv_φ_of_two_lt {t : ℝ} (ht : 2 < t) : deriv bumpProfile t = 0 := by
  have : bumpProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact bumpProfile_of_two_le (le_of_lt hs)
  rw [this.deriv_eq, deriv_const]

private theorem deriv_φ_of_lt_one {t : ℝ} (ht : t < 1) : deriv bumpProfile t = 0 := by
  have : bumpProfile =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact bumpProfile_of_le_one (le_of_lt hs)
  rw [this.deriv_eq, deriv_const]

private theorem exists_bound_deriv_φ : ∃ C, 0 ≤ C ∧ ∀ t, ‖deriv bumpProfile t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    deriv_φ_continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 4
  · exact (hC t ht).trans (le_max_left _ _)
  · rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · rw [deriv_φ_of_lt_one (by linarith)]; simp
    · rw [deriv_φ_of_two_lt (by linarith)]; simp

/-- The radial cutoff `z ↦ bumpProfile (‖z - a‖² / ε²)`, equal to `1` near `a` and to `0` far from it. -/
private def bumpKernel (a : ℂ) (ε : ℝ) (z : ℂ) : ℂ := ((bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) : ℝ) : ℂ)

variable (a : ℂ) {ε : ℝ}

private theorem bumpKernel_contDiff (ε : ℝ) : ContDiff ℝ 1 (bumpKernel a ε) := by
  unfold bumpKernel
  refine ofRealCLM.contDiff.comp ?_
  refine (bumpProfile_contDiff.of_le (by norm_num)).comp ?_
  exact ((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const _

private theorem bumpKernel_eq_one (hε : 0 < ε) {z : ℂ} (hz : ‖z - a‖ ≤ ε) : bumpKernel a ε z = 1 := by
  unfold bumpKernel
  rw [bumpProfile_of_le_one, ofReal_one]
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hz 2

private theorem bumpKernel_eq_zero (hε : 0 < ε) {z : ℂ} (hz : 2 * ε ≤ ‖z - a‖) : bumpKernel a ε z = 0 := by
  unfold bumpKernel
  rw [bumpProfile_of_two_le, ofReal_zero]
  rw [le_div_iff₀ (by positivity)]
  have h4 : (2 * ε) ^ 2 ≤ ‖z - a‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
  nlinarith

private theorem bumpKernel_hasCompactSupport (hε : 0 < ε) : HasCompactSupport (bumpKernel a ε) := by
  refine HasCompactSupport.intro (isCompact_closedBall a (2 * ε)) fun z hz => ?_
  rw [mem_closedBall, dist_eq_norm, not_le] at hz
  exact bumpKernel_eq_zero a hε hz.le

private theorem hasFDerivAt_η (z : ℂ) :
    HasFDerivAt (bumpKernel a ε) (ofRealCLM.comp ((deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) * (1 / ε ^ 2)) •
      ((2 : ℕ) • ((innerSL ℝ) (z - a)).comp (ContinuousLinearMap.id ℝ ℂ)))) z := by
  have hN : HasFDerivAt (fun w : ℂ => ‖w - a‖ ^ 2)
      ((2 : ℕ) • ((innerSL ℝ) (z - a)).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    ((hasFDerivAt_id z).sub_const a).norm_sq
  have hg : HasDerivAt (fun t : ℝ => bumpProfile (t / ε ^ 2))
      (deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) * (1 / ε ^ 2)) (‖z - a‖ ^ 2) := by
    have h1 : HasDerivAt (fun t : ℝ => t / ε ^ 2) (1 / ε ^ 2) (‖z - a‖ ^ 2) :=
      (hasDerivAt_id _).div_const _
    exact ((bumpProfile_differentiable _).hasDerivAt).comp _ h1
  have key := ofRealCLM.hasFDerivAt.comp z (hg.comp_hasFDerivAt z hN)
  exact key.congr_of_eventuallyEq (Eventually.of_forall fun w => by
    simp only [bumpKernel, Function.comp_apply, ofRealCLM_apply])

private theorem fderiv_η_apply (z v : ℂ) :
    fderiv ℝ (bumpKernel a ε) z v =
      ((deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 * (2 * ⟪z - a, v⟫_ℝ) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_η a z).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_smul,
    Pi.smul_apply, two_smul, add_apply, ContinuousLinearMap.coe_id', id_eq,
    coe_innerSL_apply, smul_eq_mul, ofRealCLM_apply]
  push_cast
  ring

private theorem dbar_η (z : ℂ) :
    dbar (bumpKernel a ε) z = ((deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 : ℝ) : ℂ) * (z - a) := by
  rw [dbar_apply]
  rw [fderiv_η_apply a, fderiv_η_apply a]
  have h1 : ⟪z - a, (1 : ℂ)⟫_ℝ = (z - a).re := by simp [Complex.inner]
  have h2 : ⟪z - a, I⟫_ℝ = (z - a).im := by simp [Complex.inner]; ring
  rw [h1, h2]
  push_cast
  linear_combination (((deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) : ℝ) : ℂ) / (ε : ℂ) ^ 2) * re_add_im (z - a)

private theorem dbar_η_eq_zero (hε : 0 < ε) {z : ℂ} (hz : 2 * ε < ‖z - a‖) :
    dbar (bumpKernel a ε) z = 0 := by
  rw [dbar_η a, deriv_φ_of_two_lt, zero_div, ofReal_zero, zero_mul]
  rw [lt_div_iff₀ (by positivity)]
  have h0 : 0 ≤ 2 * ε := by positivity
  have h4 : (2 * ε) ^ 2 < ‖z - a‖ ^ 2 := pow_lt_pow_left₀ hz h0 two_ne_zero
  nlinarith

private theorem norm_dbar_η_le (hε : 0 < ε) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖deriv bumpProfile t‖ ≤ C)
    (z : ℂ) :
    ‖dbar (bumpKernel a ε) z‖ ≤ (2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hz : z ∈ closedBall a (2 * ε)
  · rw [indicator_of_mem hz, mul_one, dbar_η a, norm_mul, Complex.norm_real, norm_div,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2)‖ / ε ^ 2 * ‖z - a‖
        ≤ C / ε ^ 2 * (2 * ε) := by gcongr; exact hC _
      _ = 2 * C / ε := by field_simp
  · rw [indicator_of_notMem hz, mul_zero]
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    rw [dbar_η_eq_zero a hε hz, norm_zero]

private theorem norm_η_le_one (ε : ℝ) (z : ℂ) : ‖bumpKernel a ε z‖ ≤ 1 := by
  unfold bumpKernel bumpProfile
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

private theorem dbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  rw [dbar_apply, dbar_apply, dbar_apply]
  rw [fderiv_fun_add hf hg]
  simp only [add_apply]
  ring

private theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = f z * dbar g z + g z * dbar f z := by
  rw [dbar_apply, dbar_apply, dbar_apply]
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

private theorem integral_radial (f : ℝ → ℝ) :
    ∫ z : ℂ, f ‖z - a‖ = 2 * π * ∫ y in Ioi 0, y * f y := by
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun x : ℂ => f ‖x‖) a
  rw [h1, integral_fun_norm_addHaar]
  rw [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  simp [mul_assoc]

private theorem integral_indicator_inv_norm {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ z : ℂ, (Iic ρ).indicator (fun y : ℝ => y⁻¹) ‖z - a‖ = 2 * π * ρ := by
  rw [integral_radial a ((Iic ρ).indicator fun y : ℝ => y⁻¹)]
  have h1 : ∫ y in Ioi (0 : ℝ), y * (Iic ρ).indicator (fun y : ℝ => y⁻¹) y
      = ∫ y in Ioi (0 : ℝ), (Iic ρ).indicator (fun _ => (1 : ℝ)) y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    by_cases hyρ : y ∈ Iic ρ
    · rw [indicator_of_mem hyρ, indicator_of_mem hyρ, mul_inv_cancel₀ (ne_of_gt hy)]
    · rw [indicator_of_notMem hyρ, indicator_of_notMem hyρ, mul_zero]
  rw [h1, setIntegral_indicator measurableSet_Iic, setIntegral_const, Ioi_inter_Iic,
    Real.volume_real_Ioc_of_le hρ.le]
  simp

private theorem integral_deriv_φ (hε : 0 < ε) :
    ∫ z : ℂ, deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 = -π := by
  have h1 := integral_radial a (fun y => deriv bumpProfile (y ^ 2 / ε ^ 2) / ε ^ 2)
  rw [h1]

  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => bumpProfile (y ^ 2 / ε ^ 2) / 2)
      (y * (deriv bumpProfile (y ^ 2 / ε ^ 2) / ε ^ 2)) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / ε ^ 2) (2 * y / ε ^ 2) y := by
      have := (hasDerivAt_pow 2 y).div_const (ε ^ 2)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have h3 := (((bumpProfile_differentiable _).hasDerivAt).comp y h2).div_const 2
    refine h3.congr_deriv ?_
    ring
  have hzero : ∀ y : ℝ, 2 * ε ≤ |y| → deriv bumpProfile (y ^ 2 / ε ^ 2) = 0 := by
    intro y hy
    apply deriv_φ_of_two_lt
    rw [lt_div_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 * ε := by positivity
    have h4 : (2 * ε) ^ 2 ≤ |y| ^ 2 := pow_le_pow_left₀ h0 hy 2
    have h5 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith
  have hcont : Continuous fun y : ℝ => y * (deriv bumpProfile (y ^ 2 / ε ^ 2) / ε ^ 2) :=
    continuous_id.mul ((deriv_φ_continuous.comp ((continuous_pow 2).div_const _)).div_const _)
  have hcs : HasCompactSupport fun y : ℝ => y * (deriv bumpProfile (y ^ 2 / ε ^ 2) / ε ^ 2) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * ε)) (b := 2 * ε)) fun y hy => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    have : 2 * ε ≤ |y| := by
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hzero y this]
    simp
  have htend : Tendsto (fun y : ℝ => bumpProfile (y ^ 2 / ε ^ 2) / 2) atTop (𝓝 0) := by
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [eventually_ge_atTop (2 * ε)] with y hy
    rw [bumpProfile_of_two_le, zero_div]
    rw [le_div_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 * ε := by positivity
    have h4 : (2 * ε) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hy 2
    nlinarith
  have hΦc : Continuous fun y : ℝ => bumpProfile (y ^ 2 / ε ^ 2) / 2 :=
    (bumpProfile_differentiable.continuous.comp ((continuous_pow 2).div_const _)).div_const _
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    hΦc.continuousWithinAt (fun y _ => hderiv y)
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn htend
  rw [hI, bumpProfile_of_le_one (by norm_num)]
  ring

private theorem integral_inv_sub_mul_dbar_η (hε : 0 < ε) :
    ∫ z, (z - a)⁻¹ * dbar (bumpKernel a ε) z = -π := by
  have hae : (fun z => (z - a)⁻¹ * dbar (bumpKernel a ε) z)
      =ᵐ[volume] fun z => ((deriv bumpProfile (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 : ℝ) : ℂ) := by
    filter_upwards [(Set.countable_singleton a).ae_notMem volume] with z hz
    rw [mem_singleton_iff] at hz
    rw [dbar_η a, mul_left_comm, inv_mul_cancel₀ (sub_ne_zero.2 hz), mul_one]
  rw [integral_congr_ae hae, integral_complex_ofReal, integral_deriv_φ a hε]
  push_cast
  ring

private theorem cauchy_kernel_integral (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * dbar h z = -π * h a := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_φ
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hh one_ne_zero
  obtain ⟨M, hM⟩ := (dbar_continuous hh).bounded_above_of_compact_support
    (dbar_hasCompactSupport hsupp)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a)
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero

  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ z, (z - a)⁻¹ * dbar h z) - (-π * h a)‖ ≤ (4 * π * M + 8 * π * L * C) * ε := by
    intro ε hε

    set e : ℂ → ℂ := bumpKernel a ε with he_def
    have he1 : ContDiff ℝ 1 e := bumpKernel_contDiff a ε
    have hed : Differentiable ℝ e := he1.differentiable one_ne_zero
    have hecs : HasCompactSupport e := bumpKernel_hasCompactSupport a hε
    set k₁ : ℂ → ℂ := fun z => h z * e z with hk₁_def
    set k₂ : ℂ → ℂ := fun z => h z * (1 - e z) with hk₂_def
    have hk₁ : ContDiff ℝ 1 k₁ := hh.mul he1
    have hk₂ : ContDiff ℝ 1 k₂ := hh.mul (contDiff_const.sub he1)
    have hk₁cs : HasCompactSupport k₁ := hsupp.mul_right
    have hk₂cs : HasCompactSupport k₂ := hsupp.mul_right

    have hDsum : ∀ z, dbar h z = dbar k₁ z + dbar k₂ z := by
      intro z
      rw [← dbar_add (hk₁.differentiable one_ne_zero z) (hk₂.differentiable one_ne_zero z)]
      congr 1
      funext w
      simp only [hk₁_def, hk₂_def]
      ring
    have hDk₁ : ∀ z, dbar k₁ z = h z * dbar e z + e z * dbar h z := fun z =>
      dbar_mul (hhd z) (hed z)

    have hI₁ : Integrable fun z => (z - a)⁻¹ * dbar k₁ z :=
      integrable_inv_sub_mul a (dbar_continuous hk₁) (dbar_hasCompactSupport hk₁cs)
    have hI₂ : Integrable fun z => (z - a)⁻¹ * dbar k₂ z :=
      integrable_inv_sub_mul a (dbar_continuous hk₂) (dbar_hasCompactSupport hk₂cs)
    have hI₃ : Integrable fun z => (z - a)⁻¹ * ((h z - h a) * dbar e z) :=
      integrable_inv_sub_mul a ((hh.continuous.sub continuous_const).mul (dbar_continuous he1))
        (dbar_hasCompactSupport hecs).mul_left
    have hI₄ : Integrable fun z => (z - a)⁻¹ * (e z * dbar h z) :=
      integrable_inv_sub_mul a (he1.continuous.mul (dbar_continuous hh))
        (dbar_hasCompactSupport hsupp).mul_left
    have hI₅ : Integrable fun z => (z - a)⁻¹ * dbar e z :=
      integrable_inv_sub_mul a (dbar_continuous he1) (dbar_hasCompactSupport hecs)

    have hfar : ∫ z, (z - a)⁻¹ * dbar k₂ z = 0 := by
      have hVo : IsOpen {z : ℂ | ε / 2 < ‖z - a‖} :=
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      have hq : DifferentiableOn ℂ (fun z : ℂ => (z - a)⁻¹) {z : ℂ | ε / 2 < ‖z - a‖} := by
        intro z hz
        have hza : z - a ≠ 0 := by
          intro h0
          simp only [Set.mem_ofPred_eq, h0, norm_zero] at hz
          linarith
        exact ((differentiableAt_id.sub_const a).inv hza).differentiableWithinAt
      have hsub : tsupport k₂ ⊆ {z : ℂ | ε / 2 < ‖z - a‖} := by
        have hcl : IsClosed {z : ℂ | ε ≤ ‖z - a‖} :=
          isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        refine (closure_minimal (fun z hz => ?_) hcl).trans fun z hz => ?_
        · rw [Set.mem_ofPred_eq]
          by_contra hlt
          push Not at hlt
          apply hz
          simp only [hk₂_def, he_def, bumpKernel_eq_one a hε hlt.le, sub_self, mul_zero]
        · simp only [Set.mem_ofPred_eq] at hz ⊢
          linarith
      exact Complex.integral_mul_dbar_eq_zero_of_differentiableOn _ hVo _ hq k₂ hk₂ hk₂cs hsub

    have hmodel : ∫ z, (z - a)⁻¹ * dbar e z = -π := integral_inv_sub_mul_dbar_η a hε

    have hE₁ : ‖∫ z, (z - a)⁻¹ * (e z * dbar h z)‖ ≤ 4 * π * M * ε := by
      have hg : Integrable fun z : ℂ => M * (Iic (2 * ε)).indicator (fun y : ℝ => y⁻¹) ‖z - a‖ := by
        have h1 : Integrable ((closedBall a (2 * ε)).indicator fun z : ℂ => (z - a)⁻¹) :=
          ((integrableOn_inv_sub a (2 * ε + 1)).mono_set
            (closedBall_subset_ball (by linarith))).integrable_indicator measurableSet_closedBall
        refine (h1.norm.const_mul M).congr (Eventually.of_forall fun z => ?_)
        simp only [norm_indicator_eq_indicator_norm, norm_inv]
        congr 1
        by_cases hz : z ∈ closedBall a (2 * ε)
        · rw [indicator_of_mem hz, indicator_of_mem]
          rwa [mem_closedBall, dist_eq_norm] at hz
        · rw [indicator_of_notMem hz, indicator_of_notMem]
          rwa [mem_closedBall, dist_eq_norm] at hz
      calc ‖∫ z, (z - a)⁻¹ * (e z * dbar h z)‖
          ≤ ∫ z : ℂ, M * (Iic (2 * ε)).indicator (fun y : ℝ => y⁻¹) ‖z - a‖ := by
            refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun z => ?_)
            by_cases hz : ‖z - a‖ ∈ Iic (2 * ε)
            · rw [indicator_of_mem hz, norm_mul, norm_mul, norm_inv, mul_comm M]
              gcongr
              calc ‖e z‖ * ‖dbar h z‖ ≤ 1 * M := by
                    gcongr
                    · exact norm_η_le_one a ε z
                    · exact hM z
                _ = M := one_mul M
            · rw [indicator_of_notMem hz, mul_zero]
              rw [mem_Iic, not_le] at hz
              rw [he_def, bumpKernel_eq_zero a hε hz.le]
              simp
        _ = 4 * π * M * ε := by
            rw [integral_const_mul, integral_indicator_inv_norm a (by positivity)]
            ring

    have hE₂ : ‖∫ z, (z - a)⁻¹ * ((h z - h a) * dbar e z)‖ ≤ 8 * π * L * C * ε := by
      have hg : Integrable fun z : ℂ =>
          L * ((2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z) :=
        (((continuousOn_const.integrableOn_compact (isCompact_closedBall a (2 * ε))
          ).integrable_indicator measurableSet_closedBall).const_mul _).const_mul _
      calc ‖∫ z, (z - a)⁻¹ * ((h z - h a) * dbar e z)‖
          ≤ ∫ z : ℂ, L * ((2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z) := by
            refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun z => ?_)
            have hqa : ‖(z - a)⁻¹‖ * ‖z - a‖ ≤ 1 := by
              rw [norm_inv]
              rcases eq_or_ne ‖z - a‖ 0 with h0 | h0
              · simp [h0]
              · rw [inv_mul_cancel₀ h0]
            calc ‖(z - a)⁻¹ * ((h z - h a) * dbar e z)‖
                = ‖(z - a)⁻¹‖ * (‖h z - h a‖ * ‖dbar e z‖) := by rw [norm_mul, norm_mul]
              _ ≤ ‖(z - a)⁻¹‖ * ((L * ‖z - a‖) * ‖dbar e z‖) := by
                  gcongr
                  exact hL.norm_sub_le z a
              _ = (‖(z - a)⁻¹‖ * ‖z - a‖) * (L * ‖dbar e z‖) := by ring
              _ ≤ 1 * (L * ‖dbar e z‖) := by gcongr
              _ ≤ L * ((2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z) := by
                  rw [one_mul]
                  gcongr
                  exact norm_dbar_η_le a hε hC0 hC z
        _ = 8 * π * L * C * ε := by
            rw [integral_const_mul, integral_const_mul,
              integral_indicator_const _ measurableSet_closedBall, measureReal_def,
              Complex.volume_closedBall]
            simp only [smul_eq_mul, mul_one]
            rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow (by positivity), ENNReal.toReal_ofReal
              (by positivity)]
            simp
            field_simp
            ring

    have hsplit : (∫ z, (z - a)⁻¹ * dbar h z) - (-π * h a)
        = (∫ z, (z - a)⁻¹ * (e z * dbar h z))
          + ∫ z, (z - a)⁻¹ * ((h z - h a) * dbar e z) := by
      have h1 : ∫ z, (z - a)⁻¹ * dbar h z
          = (∫ z, (z - a)⁻¹ * dbar k₁ z) + ∫ z, (z - a)⁻¹ * dbar k₂ z := by
        rw [← integral_add hI₁ hI₂]
        congr 1
        funext z
        rw [hDsum z]
        ring
      have h2 : ∫ z, (z - a)⁻¹ * dbar k₁ z
          = (∫ z, (z - a)⁻¹ * ((h z - h a) * dbar e z)) + (h a * ∫ z, (z - a)⁻¹ * dbar e z)
            + ∫ z, (z - a)⁻¹ * (e z * dbar h z) := by
        have h3 : (fun z => (z - a)⁻¹ * dbar k₁ z) = fun z =>
            ((z - a)⁻¹ * ((h z - h a) * dbar e z) + h a * ((z - a)⁻¹ * dbar e z))
              + (z - a)⁻¹ * (e z * dbar h z) := by
          funext z
          rw [hDk₁ z]
          ring
        have hI₆ : Integrable fun z =>
            (z - a)⁻¹ * ((h z - h a) * dbar e z) + h a * ((z - a)⁻¹ * dbar e z) :=
          hI₃.add (hI₅.const_mul _)
        rw [h3, integral_add hI₆ hI₄, integral_add hI₃ (hI₅.const_mul _), integral_const_mul]
      rw [h1, hfar, add_zero, h2, hmodel]
      ring
    rw [hsplit]
    calc ‖(∫ z, (z - a)⁻¹ * (e z * dbar h z))
          + ∫ z, (z - a)⁻¹ * ((h z - h a) * dbar e z)‖
        ≤ 4 * π * M * ε + 8 * π * L * C * ε := norm_add_le_of_le hE₁ hE₂
      _ = (4 * π * M + 8 * π * L * C) * ε := by ring

  set K : ℝ := 4 * π * M + 8 * π * L * C with hK
  have hK0 : 0 ≤ K := by positivity
  have h0 : ‖(∫ z, (z - a)⁻¹ * dbar h z) - (-π * h a)‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := key (δ / (K + 1)) (by positivity)
    rw [zero_add]
    refine this.trans ?_
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := norm_le_zero_iff.1 h0
  exact sub_eq_zero.1 this

/-- **The Cauchy kernel is a fundamental solution of `∂̄`:** for a `C¹` compactly supported `h`,
`∫ z, (z - a)⁻¹ * ∂̄h z = -π * h a`. -/
theorem integral_inv_sub_mul_dbar_eq_neg_pi_mul (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a :=
  cauchy_kernel_integral a h hh hsupp

end FundamentalSolution

/-! ### Simple poles: `∫ F · ∂̄h = -π · ∑ᶠ a, c a * h a` -/

section SimplePoles

private theorem tsupport_dbar_subset (f : ℂ → ℂ) : tsupport (dbar f) ⊆ tsupport f :=
  closure_minimal (fun _ hz => by
    by_contra h'
    exact hz (dbar_eq_zero_of_notMem_tsupport h')) (isClosed_tsupport f)

/-- The analytic part of `F` at `z`: `F` minus the simple pole of residue `c z`. -/
private noncomputable def regularPart (F c : ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[≠] z) fun w => F w - c z / (w - z)

private theorem regularPart_eq {F c : ℂ → ℂ} {a : ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g a)
    (hev : ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) : regularPart F c a = g a := by
  have ht : Tendsto (fun w => F w - c a / (w - a)) (𝓝[≠] a) (𝓝 (g a)) := by
    refine ((hg.tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with w hw
    rw [hw]
    ring
  exact ht.limUnder_eq

section

variable {U : Set ℂ} {F c : ℂ → ℂ} (hU : IsOpen U)
  (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
include hU hloc

private theorem local_analytic_form {a : ℂ} (ha : a ∈ U) : ∃ g : ℂ → ℂ, ∃ r > 0, ball a r ⊆ U ∧
    (∀ z ∈ ball a r, AnalyticAt ℂ g z) ∧ ∀ z ∈ ball a r, z ≠ a → F z = c a / (z - a) + g z := by
  obtain ⟨g, hg, hev⟩ := hloc a ha
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hg.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₂, hε₂, hball₂⟩ := hev
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds ha)
  have h1 : min ε₁ (min ε₂ ε₃) ≤ ε₁ := min_le_left _ _
  have h2 : min ε₁ (min ε₂ ε₃) ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min ε₁ (min ε₂ ε₃) ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨g, min ε₁ (min ε₂ ε₃), by positivity, (ball_subset_ball h3).trans hball₃,
    fun z hz => hball₁ (ball_subset_ball h1 hz), fun z hz hza => ?_⟩
  exact hball₂ (mem_ball.1 (ball_subset_ball h2 hz)) hza

omit hU in

private theorem residue_eq_zero_near {a : ℂ} {g : ℂ → ℂ} {r : ℝ} (hsub : ball a r ⊆ U)
    (hg : ∀ z ∈ ball a r, AnalyticAt ℂ g z)
    (hF : ∀ z ∈ ball a r, z ≠ a → F z = c a / (z - a) + g z) {z : ℂ} (hz : z ∈ ball a r)
    (hza : z ≠ a) : c z = 0 := by
  obtain ⟨gz, hgz, hevz⟩ := hloc z (hsub hz)
  have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ball a r ∧ w ≠ a :=
    (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
  have hΦ : ContinuousAt (fun w => c a / (w - a) + g w - gz w) z := by
    have h1 : ContinuousAt (fun w => c a / (w - a)) z :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hza)
    exact (h1.add (hg z hz).continuousAt).sub hgz.continuousAt
  have hev : (fun w => (c a / (w - a) + g w - gz w) * (w - z)) =ᶠ[𝓝[≠] z] fun _ => c z := by
    filter_upwards [hevz, mem_nhdsWithin_of_mem_nhds hnhds, self_mem_nhdsWithin]
      with w hw1 hw2 hw3
    have hwz : w - z ≠ 0 := sub_ne_zero.2 hw3
    have : c z / (w - z) = c a / (w - a) + g w - gz w := by
      rw [← hF w hw2.1 hw2.2, hw1]
      ring
    exact ((div_eq_iff hwz).1 this).symm
  have ht : Tendsto (fun w => (c a / (w - a) + g w - gz w) * (w - z)) (𝓝[≠] z) (𝓝 0) := by
    have h2 : Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 0) := by
      have := ((continuous_id.sub continuous_const).tendsto z : Tendsto (fun w : ℂ => w - z) _ _)
      simp at this
      exact this
    have := (hΦ.tendsto.mul h2).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    simpa using this
  exact tendsto_const_nhds_iff.1 (ht.congr' hev)

private theorem local_clean {a : ℂ} (ha : a ∈ U) : ∃ g : ℂ → ℂ, ∃ r > 0, ball a r ⊆ U ∧
    (∀ z ∈ ball a r, AnalyticAt ℂ g z) ∧
    (∀ z ∈ ball a r, regularPart F c z = c a / (z - a) + g z) ∧
    ∀ z ∈ ball a r, z ≠ a → c z = 0 ∧ F z = regularPart F c z := by
  obtain ⟨g, r, hr, hsub, hg, hF⟩ := local_analytic_form hU hloc ha
  have hc0 : ∀ z ∈ ball a r, z ≠ a → c z = 0 := fun z hz hza =>
    residue_eq_zero_near hloc hsub hg hF hz hza
  have hFF : ∀ z ∈ ball a r, z ≠ a → F z = regularPart F c z := by
    intro z hz hza
    obtain ⟨gz, hgz, hevz⟩ := hloc z (hsub hz)
    rw [regularPart_eq hgz.continuousAt hevz]
    have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ball a r ∧ w ≠ a :=
      (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
    have hΦc : ContinuousAt (fun w => c a / (w - a) + g w) z :=
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 hza)).add (hg z hz).continuousAt
    have h1 : Tendsto (fun w => c a / (w - a) + g w) (𝓝[≠] z) (𝓝 (gz z)) := by
      refine ((hgz.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hevz, mem_nhdsWithin_of_mem_nhds hnhds] with w hw1 hw2
      rw [← hF w hw2.1 hw2.2, hw1, hc0 z hz hza, zero_div, zero_add]
    have h2 : Tendsto (fun w => c a / (w - a) + g w) (𝓝[≠] z) (𝓝 (c a / (z - a) + g z)) :=
      hΦc.tendsto.mono_left nhdsWithin_le_nhds
    rw [hF z hz hza]
    exact tendsto_nhds_unique h2 h1
  refine ⟨g, r, hr, hsub, hg, fun z hz => ?_, fun z hz hza => ⟨hc0 z hz hza, hFF z hz hza⟩⟩
  by_cases hza : z = a
  · rw [hza, sub_self, div_zero, zero_add]
    refine regularPart_eq (hg a (mem_ball_self hr)).continuousAt ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin]
      with w hw hwa
    exact hF w hw hwa
  · rw [← hFF z hz hza, hF z hz hza]

private theorem finite_exceptional {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {z ∈ K | c z ≠ 0 ∨ F z ≠ regularPart F c z}.Finite := by
  choose g r hr hsub hg hFreg hexc using fun (x : ℂ) (hx : x ∈ K) => local_clean hU hloc (hKU hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => ball x (r x hx))
    fun x hx => ball_mem_nhds x (hr x hx)
  refine (t.finite_toSet.image (fun x : K => (x : ℂ))).subset ?_
  rintro z ⟨hzK, hz⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (ht hzK)
  refine ⟨x, hxt, ?_⟩
  by_contra hne
  have := hexc x x.2 z hzx (fun h' => hne h'.symm)
  rcases hz with hz | hz
  · exact hz this.1
  · exact hz this.2

end

private theorem residue_finsum_integral (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * dbar h z = -π * ∑ᶠ a, c a * h a := by
  have hK : IsCompact (tsupport h) := hsupp
  have hfin := finite_exceptional hU hloc hK hU'

  obtain ⟨T, hmemT⟩ : ∃ T : Finset ℂ, ∀ p, p ∈ T ↔ p ∈ tsupport h ∧ c p ≠ 0 := by
    have hfinT : {z ∈ tsupport h | c z ≠ 0}.Finite :=
      hfin.subset fun z hz => ⟨hz.1, Or.inl hz.2⟩
    exact ⟨hfinT.toFinset, fun p => by simp [Set.Finite.mem_toFinset]⟩

  obtain ⟨R, hR⟩ : ∃ R : ℂ → ℂ, ∀ z, R z = ∑ p ∈ T, c p / (z - p) := ⟨_, fun z => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ z, G z = regularPart F c z - R z := ⟨_, fun z => rfl⟩

  obtain ⟨V, hV⟩ : ∃ V : Set ℂ, ∀ z, z ∈ V ↔ z ∈ U ∧ (c z ≠ 0 → z ∈ tsupport h) :=
    ⟨{z | z ∈ U ∧ (c z ≠ 0 → z ∈ tsupport h)}, fun z => Iff.rfl⟩
  have hKV : tsupport h ⊆ V := fun z hz => (hV z).2 ⟨hU' hz, fun _ => hz⟩
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hxV
    obtain ⟨hxU, hx⟩ := (hV x).1 hxV
    obtain ⟨g, r, hr, hsub, hg, hFreg, hexc⟩ := local_clean hU hloc hxU
    refine mem_of_superset (ball_mem_nhds x hr) fun z hz => (hV z).2 ⟨hsub hz, fun hcz => ?_⟩
    by_cases hzx : z = x
    · rw [hzx]
      exact hx (hzx ▸ hcz)
    · exact absurd (hexc z hz hzx).1 hcz
  have hGd : DifferentiableOn ℂ G V := by
    intro x hxV
    obtain ⟨hxU, hx⟩ := (hV x).1 hxV
    obtain ⟨g, r, hr, hsub, hg, hFreg, hexc⟩ := local_clean hU hloc hxU
    have hGev : G =ᶠ[𝓝 x] fun w => c x / (w - x) + g w - R w := by
      filter_upwards [ball_mem_nhds x hr] with w hw
      rw [hG w, hFreg w hw]
    have hRd : ∀ s : Finset ℂ, x ∉ s →
        DifferentiableAt ℂ (fun w => ∑ p ∈ s, c p / (w - p)) x := by
      intro s hxs
      refine DifferentiableAt.fun_sum fun p hp => ?_
      have hxp : x - p ≠ 0 := sub_ne_zero.2 fun h' => hxs (h' ▸ hp)
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const p) hxp
    have hΦ : DifferentiableAt ℂ (fun w => c x / (w - x) + g w - R w) x := by
      by_cases hxT : x ∈ T
      · have hfun : (fun w => c x / (w - x) + g w - R w)
            = fun w => g w - ∑ p ∈ T.erase x, c p / (w - p) := by
          funext w
          rw [hR w, ← Finset.add_sum_erase T (fun p => c p / (w - p)) hxT]
          ring
        rw [hfun]
        exact (hg x (mem_ball_self hr)).differentiableAt.sub (hRd _ (Finset.notMem_erase x T))
      · have hcx : c x = 0 := by
          by_contra hcx
          exact hxT ((hmemT x).2 ⟨hx hcx, hcx⟩)
        have hfun : (fun w => c x / (w - x) + g w - R w)
            = fun w => g w - ∑ p ∈ T, c p / (w - p) := by
          funext w
          rw [hR w, hcx, zero_div, zero_add]
        rw [hfun]
        exact (hg x (mem_ball_self hr)).differentiableAt.sub (hRd _ hxT)
    exact (hΦ.congr_of_eventuallyEq hGev).differentiableWithinAt

  have hdh_cont : Continuous (dbar h) := dbar_continuous hh
  have hdh_supp : HasCompactSupport (dbar h) := dbar_hasCompactSupport hsupp
  have hIG : Integrable fun z => G z * dbar h z :=
    integrable_mul_of_tsupport_subset hVo hGd.continuousOn hdh_cont hdh_supp
      ((tsupport_dbar_subset h).trans hKV)
  have hIp : ∀ p, Integrable fun z => c p * ((z - p)⁻¹ * dbar h z) := fun p =>
    (integrable_inv_sub_mul p hdh_cont hdh_supp).const_mul _
  have hIR : Integrable fun z => ∑ p ∈ T, c p * ((z - p)⁻¹ * dbar h z) :=
    integrable_finsetSum _ fun p _ => hIp p

  have hae : (fun z => F z * dbar h z)
      =ᵐ[volume] fun z => G z * dbar h z + ∑ p ∈ T, c p * ((z - p)⁻¹ * dbar h z) := by
    filter_upwards [hfin.countable.ae_notMem volume] with z hz
    by_cases hzK : z ∈ tsupport h
    · have hFz : F z = regularPart F c z := by
        by_contra hne
        exact hz ⟨hzK, Or.inr hne⟩
      have hsum : ∑ p ∈ T, c p / (z - p) * dbar h z = ∑ p ∈ T, c p * ((z - p)⁻¹ * dbar h z) :=
        Finset.sum_congr rfl fun p _ => by ring
      rw [hFz, hG z, hR z, sub_mul, Finset.sum_mul, hsum]
      ring
    · have h0 : ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 :=
        dbar_eq_zero_of_notMem_tsupport hzK
      simp [h0]

  have hHG : ∫ z, G z * dbar h z = 0 :=
    Complex.integral_mul_dbar_eq_zero_of_differentiableOn V hVo G hGd h hh hsupp hKV
  have hHp : ∀ p, ∫ z, (z - p)⁻¹ * dbar h z = -π * h p := fun p =>
    Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul p h hh hsupp

  have hfs : ∑ᶠ a, c a * h a = ∑ p ∈ T, c p * h p := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    rw [Function.mem_support, mul_ne_zero_iff] at ha
    rw [Finset.mem_coe, hmemT]
    exact ⟨subset_tsupport _ ha.2, ha.1⟩
  rw [integral_congr_ae hae, integral_add hIG hIR, integral_finsetSum _ (fun p _ => hIp p), hHG,
    zero_add, hfs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul, hHp p]
  ring

end SimplePoles

/-- **The residue form of Pompeiu's identity.**  If `F` has only simple poles on an open `U`, with
residue `c a` at `a`, then for a `C¹` compactly supported `h` with support in `U` the integral of
`F · ∂̄h` is `-π` times the sum of the residues weighted by `h`. -/
theorem integral_mul_dbar_eq_neg_pi_mul_finsum_residue (U : Set ℂ) (hU : IsOpen U)
    (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a :=
  residue_finsum_integral U hU F c hloc h hh hsupp hU'
