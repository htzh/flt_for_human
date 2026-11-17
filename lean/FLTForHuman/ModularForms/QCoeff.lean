/-
  `q`-coefficients of modular forms: `qCoeff`, the `q`-expansion presentation
  `HasQCoeffWith` and its diagonal `HasQCoeff`, their reading of the coefficients and their
  conversions to and from the three regularity conditions, that equal coefficients force
  equal functions, and the coefficient algebra.

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

/-- `f` is presented everywhere on `ℍ` by the coefficients `c`. This is the layer an
operator acts on: a presentation transports along a reindexing of the `q`-parameter, so
the coefficients of the result are known before its `q`-expansion is. -/
abbrev HasQCoeffWith (f : ℍ → ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (f τ)

/-- `f` is presented everywhere on `ℍ` by its own `q`-expansion: the diagonal of
`HasQCoeffWith`. This is the certificate that replaces the three regularity conditions
`Periodic (f ∘ ofComplex) 1`, `MDiff f` and `IsBoundedAtImInfty f` wherever they travel
together: it is closed under the operations, which those three are not. -/
abbrev HasQCoeff (f : ℍ → ℂ) : Prop := HasQCoeffWith f (qCoeff f)

/-- A function with a `q`-expansion has `qCoeff` as its `HasSum` coefficients. -/
theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

/-- A function presented by its own `q`-expansion is bounded at `∞`. -/
theorem isBoundedAtImInfty_of_hasSum_qCoeff {f : ℍ → ℂ} (hF : HasQCoeff f) :
    IsBoundedAtImInfty f :=
  UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion one_pos hF

/-- A function presented by coefficients of period `h` is `h`-periodic. The lower half
plane needs no argument: `ofComplex` sends it to one fixed point. -/
theorem periodic_of_hasSum {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam h (τ : ℂ) ^ m) (f τ)) :
    Periodic (f ∘ ofComplex) h := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have key : ∀ z : ℂ, Periodic.qParam h (z + h) = Periodic.qParam h z := by
    intro z
    rw [Periodic.qParam, Periodic.qParam, mul_add, add_div, mul_div_cancel_right₀ _ hh',
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + h).im := by simpa using hw
    have h1 := hf ⟨w, hw⟩
    have h2 := hf ⟨w + h, hw1⟩
    rw [key w] at h2
    simp only [comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    exact h2.unique h1
  · have hw' : (w + h).im ≤ 0 := by simpa using not_lt.mp hw
    rw [Function.comp_apply, Function.comp_apply, ofComplex_apply_of_im_nonpos hw',
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

/-- A function presented by its own `q`-expansion is `1`-periodic. -/
theorem periodic_of_hasSum_qCoeff {f : ℍ → ℂ} (hF : HasQCoeff f) :
    Periodic (f ∘ ofComplex) 1 :=
  periodic_of_hasSum one_pos hF

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

/-- A `HasSum` presentation pins the coefficients: they are the `q`-expansion's. Stated at
the bare function type, because mathlib's `UpperHalfPlane.qExpansion_coeff_unique` is
`FunLike`-generic and instantiating it here unfolds `DFunLike.coe` without bound. The
analyticity at the cusp is read off the presentation, not assumed. -/
theorem qExpansion_coeff_unique_of_hasSum {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have hg : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_zero hh (periodic_of_hasSum hh hc)
      (mdifferentiable_of_hasSum hh fun τ => by simpa only [smul_eq_mul] using hc τ)
      (UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion hh hc)
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

/-- A presentation off the diagonal of `HasQCoeffWith` is a coefficient identity. -/
theorem qCoeff_eq_of_hasSum {g : ℍ → ℂ} {c : ℕ → ℂ} (hs : HasQCoeffWith g c) (n : ℕ) :
    qCoeff g n = c n :=
  (qExpansion_coeff_unique_of_hasSum one_pos hs n).symm

/-- A presentation is a certificate: reading the coefficients off `HasQCoeffWith g c` gives
`HasQCoeff g`. -/
theorem hasQCoeff_of_hasSum {g : ℍ → ℂ} {c : ℕ → ℂ} (hs : HasQCoeffWith g c) :
    HasQCoeff g := by
  intro τ
  simpa only [qCoeff_eq_of_hasSum hs] using hs τ

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

/-! ## The presentation is an algebra

A presentation transports along the operations, the coefficients transforming in step.
This is the layer an operator acts on, and none of it uses regularity. -/

/-- Presentations add. -/
theorem HasQCoeffWith.add {f g : ℍ → ℂ} {c d : ℕ → ℂ} (hf : HasQCoeffWith f c)
    (hg : HasQCoeffWith g d) : HasQCoeffWith (f + g) (c + d) := by
  intro τ
  simpa only [Pi.add_apply, add_smul] using (hf τ).add (hg τ)

/-- Presentations subtract. -/
theorem HasQCoeffWith.sub {f g : ℍ → ℂ} {c d : ℕ → ℂ} (hf : HasQCoeffWith f c)
    (hg : HasQCoeffWith g d) : HasQCoeffWith (f - g) (c - d) := by
  intro τ
  simpa only [Pi.sub_apply, sub_smul] using (hf τ).sub (hg τ)

/-- Presentations scale. -/
theorem HasQCoeffWith.const_smul {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : HasQCoeffWith f c) (a : ℂ) :
    HasQCoeffWith (a • f) (a • c) := by
  intro τ
  simpa only [Pi.smul_apply, smul_eq_mul, mul_smul, mul_assoc] using (hf τ).mul_left a

/-! ## The `q`-coefficient algebra

Each identity is a presentation read through `qCoeff_eq_of_hasSum`, and each certificate is
the same presentation read through `hasQCoeff_of_hasSum`: no regularity is spent. -/

/-- `qCoeff` is additive, stated on the certificate. -/
theorem ModularFormClass.qCoeff_add_of_hasSum {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g)
    (n : ℕ) : qCoeff (f + g) n = qCoeff f n + qCoeff g n :=
  qCoeff_eq_of_hasSum (hf.add hg) n

/-- `qCoeff` is subtractive, stated on the certificate. -/
theorem ModularFormClass.qCoeff_sub_of_hasSum {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g)
    (n : ℕ) : qCoeff (f - g) n = qCoeff f n - qCoeff g n :=
  qCoeff_eq_of_hasSum (hf.sub hg) n

/-- `qCoeff` is `ℂ`-linear, stated on the certificate. -/
theorem ModularFormClass.qCoeff_const_smul_of_hasSum {f : ℍ → ℂ} (hF : HasQCoeff f) (c : ℂ)
    (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n :=
  qCoeff_eq_of_hasSum (hF.const_smul c) n

/-- `qCoeff` is additive. -/
theorem ModularFormClass.qCoeff_add {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (n : ℕ) :
    qCoeff (f + g) n = qCoeff f n + qCoeff g n :=
  qCoeff_add_of_hasSum (hasSum_qCoeff hfper hfhol hfbdd)
    (hasSum_qCoeff hgper hghol hgbdd) n

/-- `qCoeff` is subtractive. -/
theorem ModularFormClass.qCoeff_sub {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (n : ℕ) :
    qCoeff (f - g) n = qCoeff f n - qCoeff g n :=
  qCoeff_sub_of_hasSum (hasSum_qCoeff hfper hfhol hfbdd)
    (hasSum_qCoeff hgper hghol hgbdd) n

/-- `qCoeff` is `ℂ`-linear. -/
theorem ModularFormClass.qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) :
    qCoeff (c • f) n = c * qCoeff f n :=
  qCoeff_const_smul_of_hasSum (hasSum_qCoeff hper hhol hbdd) c n

/-! ## The `q`-expansion is closed under the operations -/

/-- The `q`-expansion of a sum is the sum of the expansions. -/
theorem hasSum_qCoeff_add {f g : ℍ → ℂ} (hf : HasQCoeff f) (hg : HasQCoeff g) :
    HasQCoeff (f + g) :=
  hasQCoeff_of_hasSum (hf.add hg)

/-- The `q`-expansion of a scalar multiple scales. -/
theorem hasSum_qCoeff_const_smul {f : ℍ → ℂ} (hF : HasQCoeff f) (c : ℂ) :
    HasQCoeff (c • f) :=
  hasQCoeff_of_hasSum (hF.const_smul c)

end
