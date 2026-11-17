/-
  `q`-coefficients of modular forms: `qCoeff`, the `q`-expansion certificate
  `HasQCoeff` with its conversions to and from the three regularity conditions, that
  equal coefficients force equal functions, and the coefficient algebra.

  The pin statements of this layer are port-owned (`topics/TOPIC-interface-changes.md`);
  their `spec-pin:` lines are parked in `Reserve/ModularForms/PortOwnedSpecPins.lean`.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace ModularFormClass

/-- The `n`-th `q`-coefficient of `f`. -/
def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

end ModularFormClass

open ModularForm ModularFormClass

/-! ## The `q`-expansion presentation -/

/-- `f` is presented everywhere on `ℍ` by its own `q`-expansion. This is the
certificate that replaces the three regularity conditions `Periodic (f ∘ ofComplex) 1`,
`MDiff f` and `IsBoundedAtImInfty f` wherever they travel together: it is closed under
the operations, which those three are not. -/
abbrev HasQCoeff (f : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ)

/-- A function with a `q`-expansion has `qCoeff` as its `HasSum` coefficients. -/
theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

/-- A function presented by its own `q`-expansion is bounded at `∞`. -/
theorem isBoundedAtImInfty_of_hasSum_qCoeff {f : ℍ → ℂ} (hF : HasQCoeff f) :
    IsBoundedAtImInfty f :=
  UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion one_pos hF

/-- A function presented by its own `q`-expansion is `1`-periodic. The lower half
plane needs no argument: `ofComplex` sends it to one fixed point. -/
theorem periodic_of_hasSum_qCoeff {f : ℍ → ℂ} (hF : HasQCoeff f) :
    Periodic (f ∘ ofComplex) 1 := by
  have key : ∀ z : ℂ, Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
    intro z
    have h : (2 * ↑π * I * (z + 1)) / (1 : ℝ) = (2 * ↑π * I * z) / (1 : ℝ) + 2 * ↑π * I := by
      push_cast
      ring
    rw [Periodic.qParam, Periodic.qParam, h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    have h1 := hF ⟨w, hw⟩
    have h2 := hF ⟨w + 1, hw1⟩
    rw [key w] at h2
    simp only [comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    exact h2.unique h1
  · have hw' : (w + 1).im ≤ 0 := by simpa using not_lt.mp hw
    rw [Function.comp_apply, Function.comp_apply, ofComplex_apply_of_im_nonpos hw',
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

/-! ## Regularity from a `q`-expansion -/

/-- A `HasSum` on `ℍ` reads as one for the descended `cuspFunction` on the punctured disc. -/
theorem hasSum_cuspFunction_of_hasSum_punctured {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hh : 0 < h) (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Periodic.qParam h (τ : ℂ) ^ m) (f τ))
    {q : ℂ} (hq : ‖q‖ < 1) (hq1 : q ≠ 0) :
    HasSum (fun m : ℕ => c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1
  have h3 : cuspFunction h f q = f τ := by
    simpa [τ, cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : Periodic.qParam h (τ : ℂ) = q := Periodic.qParam_right_inv hh.ne' hq1
  rw [h3, ← h4]
  exact hf τ

/-- A `HasSum` on `ℍ`, with `q = 0` filled in by `c 0`, is a radius-`1` power series. -/
theorem hasFPowerSeriesOnBall_update {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Periodic.qParam h (τ : ℂ) ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      have : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [smul_eq_mul, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hasSum_cuspFunction_of_hasSum_punctured hh hf (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured hh hf hy hy'

/-- `f` is the `cuspFunction` value at `q(τ)`. -/
theorem apply_eq_cuspFunction {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Periodic.qParam h (τ : ℂ) ^ m) (f τ)) (τ : ℍ) :
    f τ = cuspFunction h f (Periodic.qParam h (τ : ℂ)) :=
  (hf τ).unique (hasSum_cuspFunction_of_hasSum_punctured hh hf
    (Periodic.norm_qParam_lt_one hh τ.im_pos) (Periodic.qParam_ne_zero _))

/-- The `cuspFunction` of a `HasSum` presentation is differentiable at every punctured disc point. -/
theorem differentiableAt_cuspFunction_of_hasSum {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hh : 0 < h) (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Periodic.qParam h (τ : ℂ) ^ m) (f τ))
    {q : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0) : DifferentiableAt ℂ (cuspFunction h f) q := by
  have h1 : DifferentiableOn ℂ (update (cuspFunction h f) 0 (c 0)) (Metric.ball 0 1) := by
    have h := (hasFPowerSeriesOnBall_update hh hf).differentiableOn
    rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h
  have hqball : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hq
  have h2 : DifferentiableAt ℂ (update (cuspFunction h f) 0 (c 0)) q :=
    h1.differentiableAt (Metric.isOpen_ball.mem_nhds hqball)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hq'] with y hy
  exact (update_of_ne hy (c 0) (cuspFunction h f)).symm

/-- A function presented by a `q`-expansion is `MDiff`: the disc power series composed with `q ↦ q(τ)`. -/
theorem mdifferentiable_of_hasSum {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * Periodic.qParam h (τ : ℂ) ^ m) (f τ)) :
    MDiff f := by
  have hf' : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Periodic.qParam h (τ : ℂ) ^ m) (f τ) := fun τ => by
    simpa only [smul_eq_mul] using hf τ
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ => cuspFunction h f (Periodic.qParam h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzq : ‖Periodic.qParam h z‖ < 1 := Periodic.norm_qParam_lt_one hh hz
    have hzq' : Periodic.qParam h z ≠ 0 := Periodic.qParam_ne_zero _
    exact ((differentiableAt_cuspFunction_of_hasSum hh hf' hzq hzq').comp z
      ((Periodic.differentiable_qParam (h := h)) z)).differentiableWithinAt
  refine h1.congr fun z hz => ?_
  rw [Function.comp_apply, apply_eq_cuspFunction hh hf' (ofComplex z)]
  exact congrArg (fun w : ℍ => cuspFunction h f (Periodic.qParam h (w : ℂ)))
    (UpperHalfPlane.ofComplex_apply_of_im_pos hz)

/-- A function presented by its own `q`-expansion is `MDiff`. -/
theorem mdifferentiable_of_hasSum_qCoeff {f : ℍ → ℂ} (hF : HasQCoeff f) : MDiff f :=
  mdifferentiable_of_hasSum one_pos fun τ => by
    simpa only [smul_eq_mul] using hF τ

/-- The cusp function of a function presented by its `q`-expansion is analytic at `0`. -/
theorem ModularFormClass.analyticAt_cuspFunction_zero_of_hasSum_qCoeff {f : ℍ → ℂ}
    (hF : HasQCoeff f) : AnalyticAt ℂ (cuspFunction 1 f) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic_of_hasSum_qCoeff hF)
    (mdifferentiable_of_hasSum_qCoeff hF) (isBoundedAtImInfty_of_hasSum_qCoeff hF)

/-! ## Equal coefficients force equality -/

/-- Two functions presented by their `q`-expansions and with equal coefficients are
equal. -/
theorem UpperHalfPlane.eq_of_forall_qCoeff_eq {f g : UpperHalfPlane → ℂ} (hF : HasQCoeff f)
    (hG : HasQCoeff g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) :
    f = g := by
  funext τ
  have hf := hF τ
  simp only [h] at hf
  exact hf.unique (hG τ)

/-! ## The `q`-coefficient algebra -/

/-- `qCoeff` is additive. -/
theorem ModularFormClass.qCoeff_add {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (n : ℕ) :
    qCoeff (f + g) n = qCoeff f n + qCoeff g n := by
  simp only [qCoeff]
  rw [qExpansion_add (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

/-- `qCoeff` is subtractive. -/
theorem ModularFormClass.qCoeff_sub {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (n : ℕ) :
    qCoeff (f - g) n = qCoeff f n - qCoeff g n := by
  simp only [qCoeff]
  rw [qExpansion_sub (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

/-- `qCoeff` is `ℂ`-linear. -/
theorem ModularFormClass.qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) :
    qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

/-- `qCoeff` is additive, stated on the certificate. -/
theorem ModularFormClass.qCoeff_add_of_hasSum {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g)
    (n : ℕ) : qCoeff (f + g) n = qCoeff f n + qCoeff g n :=
  qCoeff_add (periodic_of_hasSum_qCoeff hf) (mdifferentiable_of_hasSum_qCoeff hf)
    (isBoundedAtImInfty_of_hasSum_qCoeff hf) (periodic_of_hasSum_qCoeff hg)
    (mdifferentiable_of_hasSum_qCoeff hg) (isBoundedAtImInfty_of_hasSum_qCoeff hg) n

/-- `qCoeff` is subtractive, stated on the certificate. -/
theorem ModularFormClass.qCoeff_sub_of_hasSum {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g)
    (n : ℕ) : qCoeff (f - g) n = qCoeff f n - qCoeff g n :=
  qCoeff_sub (periodic_of_hasSum_qCoeff hf) (mdifferentiable_of_hasSum_qCoeff hf)
    (isBoundedAtImInfty_of_hasSum_qCoeff hf) (periodic_of_hasSum_qCoeff hg)
    (mdifferentiable_of_hasSum_qCoeff hg) (isBoundedAtImInfty_of_hasSum_qCoeff hg) n

/-- `qCoeff` is `ℂ`-linear, stated on the certificate. -/
theorem ModularFormClass.qCoeff_const_smul_of_hasSum {f : ℍ → ℂ} (hF : HasQCoeff f) (c : ℂ)
    (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n :=
  qCoeff_const_smul (periodic_of_hasSum_qCoeff hF) (mdifferentiable_of_hasSum_qCoeff hF)
    (isBoundedAtImInfty_of_hasSum_qCoeff hF) c n

/-! ## The `q`-expansion is closed under the operations -/

/-- The `q`-expansion of a sum is the sum of the expansions. -/
theorem hasSum_qCoeff_add {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g) :
    HasQCoeff (f + g) := by
  intro τ
  have hs : HasSum (fun m ↦ (qCoeff f m + qCoeff g m) • Periodic.qParam 1 τ ^ m)
      ((f + g) τ) := by
    simpa only [Pi.add_apply, add_smul] using (hf τ).add (hg τ)
  have hc : ∀ m : ℕ, qCoeff (f + g) m = qCoeff f m + qCoeff g m := fun m =>
    qCoeff_add (periodic_of_hasSum_qCoeff hf) (mdifferentiable_of_hasSum_qCoeff hf)
      (isBoundedAtImInfty_of_hasSum_qCoeff hf) (periodic_of_hasSum_qCoeff hg)
      (mdifferentiable_of_hasSum_qCoeff hg) (isBoundedAtImInfty_of_hasSum_qCoeff hg) m
  simpa only [hc] using hs

/-- The `q`-expansion of a difference is the difference of the expansions. -/
theorem hasSum_qCoeff_sub {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g) :
    HasQCoeff (f - g) := by
  intro τ
  have hs : HasSum (fun m ↦ (qCoeff f m - qCoeff g m) • Periodic.qParam 1 τ ^ m)
      ((f - g) τ) := by
    simpa only [Pi.sub_apply, sub_smul] using (hf τ).sub (hg τ)
  have hc : ∀ m : ℕ, qCoeff (f - g) m = qCoeff f m - qCoeff g m := fun m =>
    qCoeff_sub (periodic_of_hasSum_qCoeff hf) (mdifferentiable_of_hasSum_qCoeff hf)
      (isBoundedAtImInfty_of_hasSum_qCoeff hf) (periodic_of_hasSum_qCoeff hg)
      (mdifferentiable_of_hasSum_qCoeff hg) (isBoundedAtImInfty_of_hasSum_qCoeff hg) m
  simpa only [hc] using hs

/-- The `q`-expansion of a scalar multiple scales. -/
theorem hasSum_qCoeff_const_smul {f : ℍ → ℂ} (hF : HasQCoeff f) (c : ℂ) :
    HasQCoeff (c • f) := by
  intro τ
  have hs : HasSum (fun m ↦ (c * qCoeff f m) • Periodic.qParam 1 τ ^ m) ((c • f) τ) := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_smul, mul_assoc] using (hF τ).mul_left c
  have hc : ∀ m : ℕ, qCoeff (c • f) m = c * qCoeff f m := fun m =>
    qCoeff_const_smul (periodic_of_hasSum_qCoeff hF) (mdifferentiable_of_hasSum_qCoeff hF)
      (isBoundedAtImInfty_of_hasSum_qCoeff hF) c m
  simpa only [hc] using hs

end
