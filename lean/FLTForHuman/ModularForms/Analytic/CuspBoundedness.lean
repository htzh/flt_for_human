/-
  Boundedness and periodicity at the cusp.

  Three half-plane analytic facts the Eichler–Shimura period map needs:

  * `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` — if `v' = u`
    with `u` holomorphic, periodic and bounded at the cusp, and `v` periodic,
    then `v` is bounded at the cusp (Liouville-type, on the `q`-expansion);
  * `UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty` — the
    mean-value/periodic-integral identity behind it;
  * `UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero` — the generic
    "zero derivative on `ℍ` ⇒ constant" fact, promoted public here because both
    the boundedness argument and the Eichler-integral uniqueness lemma
    (`EichlerIntegral.exists_sub_eq_const`) use it (the pin duplicates it
    `private`).

  FLT provenance, pinned `aa2d8b3`:
  * `Theorems/Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.lean`
    / `P2M/Sol/S_*`
  * `Theorems/Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.lean`
    / `P2M/Sol/S_*`
  * the promoted helper is `private` in the pin's
    `P2M/Sol/S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.lean`.

  Public sources:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.lean>.
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ModularForms.QExpansion

open scoped Interval Manifold Topology Real UpperHalfPlane
open Function Filter Topology Complex Metric Set MeasureTheory intervalIntegral

/-! ## 3. Boundedness and periodicity at the cusp -/

namespace UpperHalfPlane

private theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam h) (2 * π * Complex.I / h * Function.Periodic.qParam h z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * ↑π * Complex.I * w / ↑h)
      (2 * ↑π * Complex.I / ↑h) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * ↑π * Complex.I)).div_const (↑h : ℂ)
  have h2 := h1.cexp
  have hval : 2 * (π:ℂ) * Complex.I / ↑h * Function.Periodic.qParam h z
      = cexp (2 * ↑π * Complex.I * z / ↑h) * (2 * ↑π * Complex.I / ↑h) := by
    simp only [Function.Periodic.qParam]
    ring
  rw [hval]
  exact h2

private theorem qParam_add_period (h : ℝ) (hh : h ≠ 0) (z : ℂ) :
    Function.Periodic.qParam h (z + h) = Function.Periodic.qParam h z := by
  simp only [Function.Periodic.qParam]
  have hne : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
  rw [show 2 * ↑π * Complex.I * (z + ↑h) / ↑h = 2 * ↑π * Complex.I * z / ↑h + 2 * ↑π * Complex.I by field_simp,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private theorem ofComplex_coe_add_real (τ : ℍ) (p : ℝ) :
    ofComplex ((τ : ℂ) + (p : ℂ)) = (p +ᵥ τ) := by
  have him : 0 < ((τ : ℂ) + (p : ℂ)).im := by simpa using τ.im_pos
  rw [ofComplex_apply_of_im_pos him]
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_vadd, add_comm]

/-- A function `ℂ → ℂ` whose restriction to `ℍ` has vanishing derivative at every
point of `ℍ` is constant there. Generic calculus, reused by the Eichler-integral
uniqueness lemma (`exists_sub_eq_const`) as well as the boundedness argument, so
it is public here rather than duplicated as a `private` copy in the theory. -/
theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

private theorem exists_periodic_primitive {h : ℝ} {g : ℍ → ℂ} (hh : 0 < h)
    (hper : Periodic (g ∘ ofComplex) h)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : IsZeroAtImInfty g) :
    ∃ G : ℂ → ℂ, (∀ τ : ℍ, HasDerivAt G (g τ) ↑τ) ∧ Periodic G h := by
  have hbdd : IsBoundedAtImInfty g := hzero.boundedAtFilter
  set Φ : ℂ → ℂ := cuspFunction h g with hΦ
  have hΦdiff : DifferentiableOn ℂ Φ (ball 0 1) :=
    differentiableOn_cuspFunction_ball hh hper hhol hbdd
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ, cuspFunction_apply_zero hh (analyticAt_cuspFunction_zero hh hper hhol hbdd) hper]
    exact hzero.valueAtInfty_eq_zero
  set Φ₁ : ℂ → ℂ := dslope Φ 0 with hΦ₁
  have hΦ₁diff : DifferentiableOn ℂ Φ₁ (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hΦdiff
  have hΦ₁mul : ∀ q : ℂ, q * Φ₁ q = Φ q := fun q => by
    have := sub_smul_dslope Φ 0 q
    simpa [hΦ0, smul_eq_mul] using this
  obtain ⟨Ψ, hΨ0, hΨ⟩ := (hΦ₁diff.isExactOn_ball).with_val_at 0 0
  have hqball : ∀ τ : ℍ, Function.Periodic.qParam h ↑τ ∈ ball (0:ℂ) 1 := by
    intro τ
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑τ := τ.2
    calc Real.exp (-2 * π * Complex.im ↑τ / h) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hh
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  refine ⟨fun z : ℂ => ↑h / (2 * π * Complex.I) * Ψ (Function.Periodic.qParam h z), fun τ => ?_, fun z => ?_⟩
  · have h1 : HasDerivAt (fun z : ℂ => Ψ (Function.Periodic.qParam h z))
        (Φ₁ (Function.Periodic.qParam h ↑τ) * (2 * π * Complex.I / h * Function.Periodic.qParam h ↑τ)) ↑τ :=
      (hΨ _ (hqball τ)).comp (↑τ : ℂ) (hasDerivAt_qParam h ↑τ)
    have h2 := h1.const_mul (↑h / (2 * π * Complex.I))
    refine h2.congr_deriv ?_
    have hne : (↑h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    have h3 : ↑h / (2 * ↑π * Complex.I) *
        (Φ₁ (Function.Periodic.qParam h ↑τ) * (2 * ↑π * Complex.I / ↑h * Function.Periodic.qParam h ↑τ))
        = Function.Periodic.qParam h ↑τ * Φ₁ (Function.Periodic.qParam h ↑τ) := by
      field_simp
    rw [h3, hΦ₁mul, hΦ]
    exact eq_cuspFunction τ hh.ne' hper
  · show ↑h / (2 * π * Complex.I) * Ψ (Function.Periodic.qParam h (z + h))
      = ↑h / (2 * π * Complex.I) * Ψ (Function.Periodic.qParam h z)
    rw [qParam_add_period h hh.ne' z]

end UpperHalfPlane

/-- A primitive of a periodic function that is zero at the cusp is itself
periodic (mean-value/periodic-integral identity). FLT `aa2d8b3`,
`Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty`. -/
theorem UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty {h : ℝ} (hh : 0 < h) {g : UpperHalfPlane → ℂ} (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) h) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g) {φ : ℂ → ℂ} (hφ : ∀ τ : UpperHalfPlane, HasDerivAt φ (g τ) ↑τ) (τ : UpperHalfPlane) : φ (↑τ + h) = φ ↑τ := by
  obtain ⟨G, hG, hGper⟩ := UpperHalfPlane.exists_periodic_primitive hh hper hhol hzero
  have hD : ∀ σ : ℍ, HasDerivAt (fun z => φ z - G z) 0 ↑σ := fun σ => by
    convert (hφ σ).sub (hG σ) using 1
    all_goals first | rfl | simp
  have key := UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero hD (h +ᵥ τ) τ
  simp only [UpperHalfPlane.coe_vadd] at key
  rw [add_comm] at key
  rw [hGper] at key
  linear_combination key

/-- If `v' = u` with `u` holomorphic, periodic and bounded at the cusp, and `v`
is periodic, then `v` is bounded at the cusp. FLT `aa2d8b3`,
`Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic`. -/
theorem UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic {h : ℝ} (hh : 0 < h) {u v : UpperHalfPlane → ℂ} (hu_per : Function.Periodic (u ∘ UpperHalfPlane.ofComplex) h) (hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (hu_bdd : UpperHalfPlane.IsBoundedAtImInfty u) (hv : ∀ τ : UpperHalfPlane, HasDerivAt (v ∘ UpperHalfPlane.ofComplex) (u τ) ↑τ) (hv_per : Function.Periodic (v ∘ UpperHalfPlane.ofComplex) h) : UpperHalfPlane.IsBoundedAtImInfty v := by
  set Φ : ℂ → ℂ := UpperHalfPlane.cuspFunction h u with hΦ
  have hΦdiff : DifferentiableOn ℂ Φ (ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball hh hu_per hu_hol hu_bdd
  set L : ℂ := Φ 0 with hL
  set Φ₁ : ℂ → ℂ := dslope Φ 0 with hΦ₁
  have hΦ₁diff : DifferentiableOn ℂ Φ₁ (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hΦdiff
  have hΦ₁mul : ∀ q : ℂ, q * Φ₁ q = Φ q - L := fun q => by
    have := sub_smul_dslope Φ 0 q
    simpa [smul_eq_mul] using this
  obtain ⟨Ψ, -, hΨ⟩ := (hΦ₁diff.isExactOn_ball).with_val_at 0 0
  have hnormq : ∀ τ : ℍ, ‖Function.Periodic.qParam h ↑τ‖ = Real.exp (-2 * π * τ.im / h) := fun τ => by
    rw [Function.Periodic.norm_qParam]; rfl
  have hqball : ∀ τ : ℍ, Function.Periodic.qParam h ↑τ ∈ ball (0:ℂ) 1 := by
    intro τ
    rw [mem_ball_zero_iff, hnormq]
    calc Real.exp (-2 * π * τ.im / h) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hh
            have := τ.im_pos
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero

  set G : ℂ → ℂ := fun z => ↑h / (2 * π * Complex.I) * Ψ (Function.Periodic.qParam h z) with hGdef
  have hG : ∀ τ : ℍ, HasDerivAt G (u τ - L) ↑τ := by
    intro τ
    have h1 : HasDerivAt (fun z : ℂ => Ψ (Function.Periodic.qParam h z))
        (Φ₁ (Function.Periodic.qParam h ↑τ) * (2 * π * Complex.I / h * Function.Periodic.qParam h ↑τ)) ↑τ :=
      (hΨ _ (hqball τ)).comp (↑τ : ℂ) (UpperHalfPlane.hasDerivAt_qParam h ↑τ)
    have h2 := h1.const_mul (↑h / (2 * π * Complex.I))
    refine h2.congr_deriv ?_
    have hne : (↑h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    have h3 : ↑h / (2 * ↑π * Complex.I) *
        (Φ₁ (Function.Periodic.qParam h ↑τ) * (2 * ↑π * Complex.I / ↑h * Function.Periodic.qParam h ↑τ))
        = Function.Periodic.qParam h ↑τ * Φ₁ (Function.Periodic.qParam h ↑τ) := by
      field_simp
    rw [h3, hΦ₁mul, hΦ]
    rw [UpperHalfPlane.eq_cuspFunction τ hh.ne' hu_per]
  have hGper : ∀ z : ℂ, G (z + h) = G z := fun z => by
    simp only [hGdef]
    rw [UpperHalfPlane.qParam_add_period h hh.ne' z]

  have hD : ∀ σ : ℍ, HasDerivAt (fun z : ℂ => (v ∘ UpperHalfPlane.ofComplex) z - G z - L * z) 0 ↑σ := by
    intro σ
    have := ((hv σ).sub (hG σ)).sub ((hasDerivAt_id (σ : ℂ)).const_mul L)
    convert this using 1
    all_goals first | rfl | simp
  have hconst : ∀ τ : ℍ, v τ - G ↑τ - L * ↑τ = v UpperHalfPlane.I - G ↑UpperHalfPlane.I - L * ↑UpperHalfPlane.I := by
    intro τ
    have := UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero hD τ UpperHalfPlane.I
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at this
    exact this

  have hL0 : L = 0 := by
    have h1 := hconst ((h : ℝ) +ᵥ UpperHalfPlane.I)
    have hvper : v ((h : ℝ) +ᵥ UpperHalfPlane.I) = v UpperHalfPlane.I := by
      have := hv_per (UpperHalfPlane.I : ℂ)
      simp only [Function.comp_apply] at this
      rw [UpperHalfPlane.ofComplex_coe_add_real UpperHalfPlane.I h,
        UpperHalfPlane.ofComplex_apply] at this
      exact this
    have hGI : G ↑((h : ℝ) +ᵥ UpperHalfPlane.I) = G ↑UpperHalfPlane.I := by
      rw [UpperHalfPlane.coe_vadd, add_comm]
      exact hGper _
    rw [hvper, hGI, UpperHalfPlane.coe_vadd] at h1
    have : L * (h : ℂ) = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd (ofReal_eq_zero.mp h0) hh.ne'

  set r : ℝ := Real.exp (-2 * π) with hr
  have hr1 : r < 1 := by
    rw [hr]
    calc Real.exp (-2 * π) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  have hΨcont : ContinuousOn Ψ (closedBall (0:ℂ) r) := by
    intro q hq
    have hq' : q ∈ ball (0:ℂ) 1 := by
      rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hq; linarith
    exact (hΨ q hq').continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) r).exists_bound_of_continuousOn hΨcont

  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨‖(↑h / (2 * π * Complex.I) : ℂ)‖ * M + ‖v UpperHalfPlane.I - G ↑UpperHalfPlane.I‖, h, fun τ hτ => ?_⟩
  have hqr : Function.Periodic.qParam h ↑τ ∈ closedBall (0:ℂ) r := by
    rw [mem_closedBall_zero_iff, hnormq, hr]
    apply Real.exp_le_exp.mpr
    have him : 0 < τ.im := τ.im_pos
    rw [neg_mul, neg_mul, neg_div, neg_le_neg_iff]
    rw [le_div_iff₀ hh]
    nlinarith [Real.pi_pos]
  have hvτ : v τ = G ↑τ + (v UpperHalfPlane.I - G ↑UpperHalfPlane.I) := by
    have := hconst τ
    rw [hL0] at this
    linear_combination this
  rw [hvτ]
  calc ‖G ↑τ + (v UpperHalfPlane.I - G ↑UpperHalfPlane.I)‖
        ≤ ‖G ↑τ‖ + ‖v UpperHalfPlane.I - G ↑UpperHalfPlane.I‖ := norm_add_le _ _
    _ ≤ ‖(↑h / (2 * π * Complex.I) : ℂ)‖ * M + ‖v UpperHalfPlane.I - G ↑UpperHalfPlane.I‖ := by
        gcongr
        simp only [hGdef]
        rw [norm_mul]
        gcongr
        exact hM _ hqr

