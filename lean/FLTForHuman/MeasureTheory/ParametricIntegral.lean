/-
  Derivatives and limits of parametric integrals, and the variance inequality.

  Three leaves of the analytic floor of the D–S shelf:

  * `differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le` — if every
    section `z ↦ F z a` is holomorphic on an open `U ⊆ ℂ` and the family is locally
    dominated by one integrable `M`, then `z ↦ ∫ a, F z a ∂ν` is holomorphic on `U`
    (dominated convergence for a derivative, then Cauchy's estimate);
  * `tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` — a Fatou sandwich: if
    `F i ≤ G i`, `F i → 0` pointwise and `G i → g` with `∫⁻ g ≠ ∞` and
    `limsup ∫⁻ G i ≤ ∫⁻ g`, then `∫⁻ F i → 0`;
  * `lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` — the
    variance (Jensen) inequality in `L²`: the squared `enorm` of
    `u x - ∫ a, U x a * p a ∂ρ` is bounded by the `ρ`-average of the squared deviations,
    weighted by the probability density `p`.

  Transcribed from the D–S shelf's nine `MeasureTheory` leaves (pinned `aa2d8b34`), the
  first two rows of this module from
  `S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.lean`,
  `S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le.lean` and
  `S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq.lean`.
  Generic measure theory, so its home is `MeasureTheory/` (playbook §3.1); the pin's
  generation namespaces are dropped and the statements stay the pin's.

  spec-pin: P2M/Sol/S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.lean
  spec-pin: P2M/Sol/S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le.lean
  spec-pin: P2M/Sol/S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq.lean
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

open MeasureTheory Metric Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory

namespace ParametricIntegral

/-- Derivative of a parametric integral under a locally bounded holomorphic family. -/
theorem main
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨ε, hε, M, hM, hbd⟩ := hdom z₀ hz₀
  obtain ⟨δ₀, hδ₀, hballU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set δ : ℝ := min ε δ₀ / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have h2δε : 2 * δ ≤ ε := by rw [hδdef]; linarith [min_le_left ε δ₀]
  have h2δ₀ : 2 * δ ≤ δ₀ := by rw [hδdef]; linarith [min_le_right ε δ₀]
  have hBU : ball z₀ (2 * δ) ⊆ U := (ball_subset_ball h2δ₀).trans hballU
  have hBε : ball z₀ (2 * δ) ⊆ ball z₀ ε := ball_subset_ball h2δε

  set F' : ℂ → Y → ℂ := fun z a => deriv (fun w => F w a) z with hF'
  have hderiv : ∀ a : Y, ∀ z ∈ ball z₀ δ, HasDerivAt (fun w => F w a) (F' z a) z := by
    intro a z hz
    have hzU : z ∈ U := hBU (ball_subset_ball (by linarith) hz)
    exact ((hhol a).differentiableAt (hU.mem_nhds hzU)).hasDerivAt

  have hsub : ∀ z ∈ ball z₀ δ, closedBall z δ ⊆ ball z₀ (2 * δ) := by
    intro z hz w hw
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < δ + δ := by linarith
      _ = 2 * δ := by ring
  have hbound : ∀ a : Y, ∀ z ∈ ball z₀ δ, ‖F' z a‖ ≤ M a / δ := by
    intro a z hz
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · have hcl : closure (ball z δ) ⊆ U :=
        closure_ball_subset_closedBall.trans ((hsub z hz).trans hBU)
      exact ((hhol a).mono hcl).diffContOnCl
    · intro w hw
      exact hbd w (hBε (hsub z hz (sphere_subset_closedBall hw))) a

  have hF'meas : AEStronglyMeasurable (F' z₀) ν := by
    set t : ℕ → ℂ := fun n => ((δ / ((n : ℝ) + 2) : ℝ) : ℂ) with ht
    have htpos : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := fun n => by positivity
    have ht_ne : ∀ n : ℕ, t n ≠ 0 := fun n => by
      show (((δ / ((n : ℝ) + 2) : ℝ)) : ℂ) ≠ 0
      exact_mod_cast (htpos n).ne'
    have ht_lt : ∀ n : ℕ, ‖t n‖ < δ := fun n => by
      show ‖((((δ / ((n : ℝ) + 2) : ℝ)) : ℂ))‖ < δ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n), div_lt_iff₀ (by positivity)]
      nlinarith [hδ]
    have ht_mem : ∀ n : ℕ, z₀ + t n ∈ U := fun n =>
      hBU (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith [ht_lt n])
    have ht0 : Tendsto t atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have ht0' : Tendsto t atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨ht0, Eventually.of_forall fun n => ht_ne n⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) (fun n => ?_) ?_
    · show AEStronglyMeasurable (fun a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) ν
      exact ((hmeas _ (ht_mem n)).sub (hmeas z₀ hz₀)).const_smul ((t n)⁻¹)
    · refine Eventually.of_forall fun a => ?_
      have h := (hderiv a z₀ (mem_ball_self hδ)).tendsto_slope_zero
      exact h.comp ht0'

  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun a => M a / δ) (ball_mem_nhds z₀ hδ)
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) hmeas)
    (Integrable.mono' hM (hmeas z₀ hz₀) (Eventually.of_forall fun a => hbd z₀ (mem_ball_self hε) a))
    hF'meas
    (Eventually.of_forall fun a z hz => hbound a z hz)
    (hM.div_const δ)
    (Eventually.of_forall fun a z hz => hderiv a z hz)
  exact key.2.differentiableAt.differentiableWithinAt

end ParametricIntegral

theorem differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by
  exact ParametricIntegral.main ν hU F hmeas hhol hdom

theorem tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F G : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hFG : ∀ i, ∀ᵐ x ∂μ, F i x ≤ G i x)
    (hF0 : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0))
    (hGg : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (𝓝 (g x)))
    (hg : ∫⁻ x, g x ∂μ ≠ ∞)
    (hlim : limsup (fun i => ∫⁻ x, G i x ∂μ) l ≤ ∫⁻ x, g x ∂μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂μ) l (𝓝 0) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot

  have hHmeas : ∀ i, AEMeasurable (fun x => G i x - F i x) μ := fun i => (hG i).sub (hF i)
  have hHlim : ∀ᵐ x ∂μ, liminf (fun i => G i x - F i x) l = g x := by
    filter_upwards [hF0, hGg] with x hx0 hxg
    have h := ENNReal.Tendsto.sub hxg hx0 (Or.inr ENNReal.zero_ne_top)
    rw [tsub_zero] at h
    exact h.liminf_eq

  have hFatou : ∫⁻ x, g x ∂μ ≤ liminf (fun i => ∫⁻ x, G i x - F i x ∂μ) l :=
    calc ∫⁻ x, g x ∂μ = ∫⁻ x, liminf (fun i => G i x - F i x) l ∂μ :=
          lintegral_congr_ae (hHlim.mono fun x hx => hx.symm)
      _ ≤ liminf (fun i => ∫⁻ x, G i x - F i x ∂μ) l := lintegral_liminf_le' hHmeas

  have hsum : ∀ i, ∫⁻ x, F i x ∂μ + ∫⁻ x, G i x - F i x ∂μ = ∫⁻ x, G i x ∂μ := by
    intro i
    rw [← lintegral_add_left' (hF i)]
    exact lintegral_congr_ae ((hFG i).mono fun x hx => add_tsub_cancel_of_le hx)

  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have h1 : ∀ᶠ i in l, ∫⁻ x, G i x ∂μ < ∫⁻ x, g x ∂μ + ε / 2 :=
    eventually_lt_of_limsup_lt (hlim.trans_lt (ENNReal.lt_add_right hg hε2))
  have h2 : ∀ᶠ i in l, ∫⁻ x, g x ∂μ - ε / 2 ≤ ∫⁻ x, G i x - F i x ∂μ := by
    rcases eq_or_ne (∫⁻ x, g x ∂μ) 0 with h0 | h0
    · exact Eventually.of_forall fun i => by rw [h0, zero_tsub]; exact zero_le
    · exact (eventually_lt_of_lt_liminf ((ENNReal.sub_lt_self hg h0 hε2).trans_le hFatou)).mono
        fun i hi => hi.le
  filter_upwards [h1, h2] with i hi1 hi2
  have hfin : ∫⁻ x, g x ∂μ - ε / 2 ≠ ∞ := ENNReal.sub_ne_top hg
  have h3 : ∫⁻ x, F i x ∂μ + (∫⁻ x, g x ∂μ - ε / 2) ≤ ∫⁻ x, g x ∂μ + ε / 2 :=
    calc ∫⁻ x, F i x ∂μ + (∫⁻ x, g x ∂μ - ε / 2)
          ≤ ∫⁻ x, F i x ∂μ + ∫⁻ x, G i x - F i x ∂μ := by gcongr
      _ = ∫⁻ x, G i x ∂μ := hsum i
      _ ≤ ∫⁻ x, g x ∂μ + ε / 2 := hi1.le
  calc ∫⁻ x, F i x ∂μ ≤ (∫⁻ x, g x ∂μ + ε / 2) - (∫⁻ x, g x ∂μ - ε / 2) :=
        ENNReal.le_sub_of_add_le_right hfin h3
    _ ≤ ε := by
        refine tsub_le_iff_right.2 ?_
        calc ∫⁻ x, g x ∂μ + ε / 2 ≤ (∫⁻ x, g x ∂μ - ε / 2 + ε / 2) + ε / 2 := by
              gcongr; exact le_tsub_add
          _ = ε + (∫⁻ x, g x ∂μ - ε / 2) := by rw [add_assoc, ENNReal.add_halves, add_comm]

variable {A : Type*} [MeasurableSpace A] in
private theorem enorm_integral_mul_sq_le (ρ : Measure A) (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∫⁻ a, ENNReal.ofReal (p a) ∂ρ = 1) (G : A → ℂ) (hG : AEStronglyMeasurable G ρ) :
    ‖∫ a, G a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ≤ ∫⁻ a, ENNReal.ofReal (p a) * ‖G a‖ₑ ^ 2 ∂ρ := by

  set w : A → ℝ≥0∞ := fun a => ENNReal.ofReal (p a) with hw
  have hwm : Measurable w := hp.ennreal_ofReal
  have hGm : AEMeasurable (fun a => ‖G a‖ₑ) ρ := hG.enorm

  have h1 : ‖∫ a, G a * (p a : ℂ) ∂ρ‖ₑ ≤ ∫⁻ a, ‖G a‖ₑ * w a ∂ρ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun a => ?_
    rw [enorm_mul, hw]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 a)]

  have h2 : ∫⁻ a, ‖G a‖ₑ * w a ∂ρ ≤ (∫⁻ a, w a * ‖G a‖ₑ ^ 2 ∂ρ) ^ (1 / 2 : ℝ) := by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two
      (f := fun a => ‖G a‖ₑ * w a ^ (1 / 2 : ℝ)) (g := fun a => w a ^ (1 / 2 : ℝ))
      (hGm.mul (hwm.pow_const _).aemeasurable) (hwm.pow_const _).aemeasurable
    have hfg : (fun a => ‖G a‖ₑ * w a ^ (1 / 2 : ℝ)) * (fun a => w a ^ (1 / 2 : ℝ)) = fun a => ‖G a‖ₑ * w a := by
      funext a
      simp only [Pi.mul_apply]
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    have hf2 : ∀ a, (‖G a‖ₑ * w a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w a * ‖G a‖ₑ ^ 2 := by
      intro a
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul]
      norm_num
      rw [mul_comm]
    have hg2 : ∀ a, (w a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w a := by
      intro a
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hfg] at hH
    simp_rw [hf2, hg2] at hH
    rw [hp1, ENNReal.one_rpow, mul_one] at hH
    exact hH

  calc ‖∫ a, G a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ≤ ((∫⁻ a, w a * ‖G a‖ₑ ^ 2 ∂ρ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' (h1.trans h2) 2
    _ = ∫⁻ a, w a * ‖G a‖ₑ ^ 2 ∂ρ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

theorem lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (ν : Measure X) (ρ : Measure A) [SFinite ν] [SFinite ρ]
    (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∫ a, p a ∂ρ = 1)
    (u : X → ℂ) (hu : Measurable u) (U : X → A → ℂ) (hU : Measurable (Function.uncurry U))
    (hint : ∀ x, Integrable (fun a => U x a * (p a : ℂ)) ρ) :
    ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by
  have hpi : Integrable p ρ := Integrable.of_integral_ne_zero (by rw [hp1]; exact one_ne_zero)
  have hp1' : ∫⁻ a, ENNReal.ofReal (p a) ∂ρ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hpi (ae_of_all _ hp0), hp1, ENNReal.ofReal_one]

  have hpt : ∀ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ‖u x - U x a‖ₑ ^ 2 ∂ρ := by
    intro x
    have hux : u x = ∫ a, u x * (p a : ℂ) ∂ρ := by
      rw [integral_const_mul, integral_complex_ofReal, hp1, Complex.ofReal_one, mul_one]
    have hsub : u x - ∫ a, U x a * (p a : ℂ) ∂ρ = ∫ a, (u x - U x a) * (p a : ℂ) ∂ρ := by
      have hpc : Integrable (fun a => (p a : ℂ)) ρ := hpi.ofReal (𝕜 := ℂ)
      conv_lhs => rw [hux]
      rw [← integral_sub (hpc.const_mul (u x)) (hint x)]
      refine integral_congr_ae (ae_of_all _ fun a => ?_)
      ring
    rw [hsub]
    have hGx : AEStronglyMeasurable (fun a => u x - U x a) ρ :=
      (aestronglyMeasurable_const.sub (hU.of_uncurry_left.aestronglyMeasurable))
    exact enorm_integral_mul_sq_le ρ p hp hp0 hp1' _ hGx

  calc ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ x, ∫⁻ a, ENNReal.ofReal (p a) * ‖u x - U x a‖ₑ ^ 2 ∂ρ ∂ν := lintegral_mono hpt
    _ = ∫⁻ a, ∫⁻ x, ENNReal.ofReal (p a) * ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by
        refine lintegral_lintegral_swap ?_
        refine ((hp.ennreal_ofReal.comp measurable_snd).mul ?_).aemeasurable
        exact ((hu.comp measurable_fst).sub hU).enorm.pow_const 2
    _ = ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by
        refine lintegral_congr fun a => ?_
        rw [lintegral_const_mul]
        exact ((hu.sub hU.of_uncurry_right).enorm.pow_const 2)

end MeasureTheory
