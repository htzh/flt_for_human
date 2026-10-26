/-
  The residue formula for the circle integral, and the differentiability in `t` of
  `t ↦ ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t)`.

  Both are supplements to mathlib's `circleIntegral` (`Complex.circleIntegral`), whose API already
  provides `∮ z in C(c, R), (z - w)⁻¹ = 2 π i` for `w` inside the ball and the vanishing of
  `∮ z in C(c, R), f z` for `f` analytic on the closed ball.

  * The first theorem, `circleIntegral_eq_sum_residue_of_simplePole`, assembles those into the
    residue formula: if `h` has exactly the simple poles `a ∈ Z` inside the circle, with residues
    `c a` — that is, `h z = c a / (z - a) + g z` near `a` with `g` analytic, and `h` analytic off
    `Z` on the closed ball — then `∮ z in C(z₀, R), h z = 2 π i ∑ a ∈ Z, c a`. The proof subtracts
    the principal parts `c a / (z - a)` from `h`; the difference extends to a function analytic on
    the closed ball and so integrates to zero, and each principal part is a circle integral of
    `(z - a)⁻¹` with `a` in the ball.
  * The second theorem, `hasDerivAt_circleIntegral_mul_deriv_div_sub`, is the derivative of that
    family in the pole parameter: on the circle `Φ` stays at a positive distance `δ` from `t₀`,
    and differentiating
    `F t θ = deriv (circleMap z₀ r) θ • (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ) /
    (Φ (circleMap z₀ r θ) - t))` under the integral sign (dominated convergence on
    `[0, 2π]`, with bound `r * (M G * M Φ / (δ/2)²)`) gives
    `HasDerivAt (fun t => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
    (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀`. The two circle integrals agree by the
    quotient identity `(deriv G * (Φ - t₀) - G * deriv Φ) / (Φ - t₀)² =
    deriv G / (Φ - t₀) - G * deriv Φ / (Φ - t₀)²` whose left side is the derivative along the
    circle of `G y / (Φ y - t₀)`, hence integrates to zero.

  spec-pin: Theorems/Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole.lean
  spec-pin: P2M/Sol/S_Complex_circleIntegral_eq_sum_residue_of_simplePole.lean
  spec-pin: Theorems/Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub.lean
  spec-pin: P2M/Sol/S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub.lean
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option autoImplicit false

noncomputable section

open scoped Topology Real

open Metric Filter MeasureTheory

namespace Complex

/-- The circle `∮` picks up a distance from `t₀`: if `Φ` is analytic on `sphere z₀ r` and never
equals `t₀` there, `‖Φ z - t₀‖` is bounded below by a positive constant on the sphere. -/
private theorem exists_pos_le_norm_sub {Φ : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ z ∈ sphere z₀ r, AnalyticAt ℂ Φ z) (hne : ∀ z ∈ sphere z₀ r, Φ z ≠ t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ sphere z₀ r, δ ≤ ‖Φ z - t₀‖ := by
  have hcont : ContinuousOn (fun z => ‖Φ z - t₀‖) (sphere z₀ r) := fun z hz =>
    ((hΦ z hz).continuousAt.sub continuousAt_const).norm.continuousWithinAt
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    ((NormedSpace.sphere_nonempty (x := z₀)).2 hr.le) hcont
  refine ⟨‖Φ x - t₀‖, norm_pos_iff.2 (sub_ne_zero.2 (hne x hx)), fun z hz => ?_⟩
  exact (isMinOn_iff.1 hmin) z hz

private theorem norm_deriv_circleMap_le {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖deriv (circleMap z₀ r) θ‖ ≤ r := by
  rw [deriv_circleMap]
  simp [circleMap, abs_of_pos hr]

/-- The quotient identity behind the differentiation in `t`: the derivative along the circle of
`G y / (Φ y - t₀)` integrates to zero, which rewrites `∮ G · Φ' / (Φ - t₀)²` as
`∮ G' / (Φ - t₀)`. -/
private theorem circleIntegral_mul_deriv_div_sq_eq {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hΦ : ∀ z ∈ sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ sphere z₀ r, Φ z ≠ t₀) :
    (∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t₀) ^ 2) =
      ∮ z in C(z₀, r), deriv G z / (Φ z - t₀) := by
  have hH : ∀ z ∈ sphere z₀ r, HasDerivWithinAt (fun y => G y / (Φ y - t₀))
      ((deriv G z * (Φ z - t₀) - G z * deriv Φ z) / (Φ z - t₀) ^ 2) (sphere z₀ r) z := by
    intro z hz
    have h1 : HasDerivAt G (deriv G z) z := (hG z hz).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun y => Φ y - t₀) (deriv Φ z) z :=
      (hΦ z hz).differentiableAt.hasDerivAt.sub_const t₀
    exact (h1.div h2 (sub_ne_zero.2 (hne z hz))).hasDerivWithinAt
  have h0 := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le hH

  have cG : ContinuousOn G (sphere z₀ r) := fun z hz => (hG z hz).continuousAt.continuousWithinAt
  have cG' : ContinuousOn (deriv G) (sphere z₀ r) := fun z hz =>
    (hG z hz).deriv.continuousAt.continuousWithinAt
  have cΦ' : ContinuousOn (deriv Φ) (sphere z₀ r) := fun z hz =>
    (hΦ z hz).deriv.continuousAt.continuousWithinAt
  have cD : ContinuousOn (fun z => Φ z - t₀) (sphere z₀ r) := fun z hz =>
    ((hΦ z hz).continuousAt.sub continuousAt_const).continuousWithinAt
  have hD0 : ∀ z ∈ sphere z₀ r, Φ z - t₀ ≠ 0 := fun z hz => sub_ne_zero.2 (hne z hz)
  have cA : ContinuousOn (fun z => deriv G z / (Φ z - t₀)) (sphere z₀ r) := cG'.div cD hD0
  have cB : ContinuousOn (fun z => G z * deriv Φ z / (Φ z - t₀) ^ 2) (sphere z₀ r) :=
    (cG.mul cΦ').div (cD.pow 2) fun z hz => pow_ne_zero 2 (hD0 z hz)

  have hcongr : (∮ z in C(z₀, r),
        (deriv G z * (Φ z - t₀) - G z * deriv Φ z) / (Φ z - t₀) ^ 2) =
      ∮ z in C(z₀, r), (deriv G z / (Φ z - t₀) - G z * deriv Φ z / (Φ z - t₀) ^ 2) := by
    refine circleIntegral.integral_congr hr.le fun z hz => ?_
    have h := hD0 z hz
    field_simp
  rw [hcongr, circleIntegral.integral_sub (cA.circleIntegrable hr.le) (cB.circleIntegrable hr.le)]
    at h0
  exact (sub_eq_zero.1 h0).symm

/-- **The residue formula in `circleIntegral` form.** If `h` has only simple poles inside the
circle `C(z₀, R)`, at the points of `Z` with residues `c a`, and is analytic elsewhere on the
closed ball, then `∮ z in C(z₀, R), h z = 2 π i ∑ a ∈ Z, c a`. -/
theorem circleIntegral_eq_sum_residue_of_simplePole {R : ℝ} {z₀ : ℂ} (hR : 0 < R)
    (h c : ℂ → ℂ) (Z : Finset ℂ) (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a := by
  classical
  choose g hg hgeq using hloc
  have hZclosed : IsClosed ((Z : Set ℂ)) := Z.finite_toSet.isClosed

  have hsum_an : ∀ (S : Finset ℂ) (z : ℂ), (∀ b ∈ S, b ≠ z) →
      AnalyticAt ℂ (fun w => ∑ b ∈ S, c b * (w - b)⁻¹) z := by
    intro S z hne
    have h₁ : AnalyticAt ℂ (∑ b ∈ S, fun w => c b * (w - b)⁻¹) z :=
      Finset.analyticAt_sum S fun b hb =>
        analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.mpr (Ne.symm (hne b hb))))
    have heq : (∑ b ∈ S, fun w => c b * (w - b)⁻¹)
        = fun w => ∑ b ∈ S, c b * (w - b)⁻¹ := by
      funext w; simp
    exact heq ▸ h₁

  have hΦan : ∀ z ∈ Metric.closedBall z₀ R, AnalyticAt ℂ
      (fun w => if hw : w ∈ Z then g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
                else h w - ∑ b ∈ Z, c b * (w - b)⁻¹) z := by
    intro z hz
    by_cases hzZ : z ∈ Z
    ·
      have hevNotZ : ∀ᶠ w in 𝓝[≠] z, w ∉ Z := by
        have hcl : IsClosed ((Z.erase z : Finset ℂ) : Set ℂ) :=
          (Z.erase z).finite_toSet.isClosed
        have hmem : z ∈ (((Z.erase z : Finset ℂ) : Set ℂ))ᶜ := by simp
        have h₁ : ∀ᶠ w in 𝓝 z, w ∈ (((Z.erase z : Finset ℂ) : Set ℂ))ᶜ :=
          hcl.isOpen_compl.eventually_mem hmem
        have h₂ : ∀ᶠ w in 𝓝[≠] z, w ∈ ({z}ᶜ : Set ℂ) := eventually_mem_nhdsWithin
        filter_upwards [h₁.filter_mono nhdsWithin_le_nhds, h₂] with w hw₁ hw₂ hwZ
        simp only [Set.mem_compl_iff, Finset.coe_erase, Set.mem_sdiff,
          Set.mem_singleton_iff, Finset.mem_coe, not_and, not_not] at hw₁
        exact hw₂ (hw₁ hwZ)
      have hev : (fun w => if hw : w ∈ Z then g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
            else h w - ∑ b ∈ Z, c b * (w - b)⁻¹)
          =ᶠ[𝓝[≠] z] fun w => g z hzZ w - ∑ b ∈ Z.erase z, c b * (w - b)⁻¹ := by
        filter_upwards [hgeq z hzZ, hevNotZ] with w hw hwZ
        simp only [dite_eq_right hwZ]
        rw [hw, ← Finset.add_sum_erase Z _ hzZ]
        simp only [div_eq_mul_inv]
        ring
      have hΨan : AnalyticAt ℂ
          (fun w => g z hzZ w - ∑ b ∈ Z.erase z, c b * (w - b)⁻¹) z :=
        (hg z hzZ).sub (hsum_an _ z fun b hb => (Finset.mem_erase.mp hb).1)
      have hfull : (fun w => if hw : w ∈ Z then g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
            else h w - ∑ b ∈ Z, c b * (w - b)⁻¹)
          =ᶠ[𝓝 z] fun w => g z hzZ w - ∑ b ∈ Z.erase z, c b * (w - b)⁻¹ :=
        eventuallyEq_nhds_of_eventuallyEq_nhdsNE hev (by simp only [dite_eq_left hzZ])
      exact hΨan.congr hfull.symm
    ·
      have hopen : ∀ᶠ w in 𝓝 z, w ∉ Z := by
        have : ∀ᶠ w in 𝓝 z, w ∈ ((Z : Set ℂ))ᶜ :=
          hZclosed.isOpen_compl.eventually_mem (by simpa using hzZ)
        simpa using this
      have hev : (fun w => if hw : w ∈ Z then g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
            else h w - ∑ b ∈ Z, c b * (w - b)⁻¹)
          =ᶠ[𝓝 z] fun w => h w - ∑ b ∈ Z, c b * (w - b)⁻¹ := by
        filter_upwards [hopen] with w hw
        simp only [dite_eq_right hw]
      have han : AnalyticAt ℂ (fun w => h w - ∑ b ∈ Z, c b * (w - b)⁻¹) z :=
        (hh z hz hzZ).sub (hsum_an Z z fun b hb hbz => hzZ (hbz ▸ hb))
      exact han.congr hev.symm

  have h0 : (∮ z in C(z₀, R),
      (if hz : z ∈ Z then g z hz z - ∑ b ∈ Z.erase z, c b * (z - b)⁻¹
       else h z - ∑ b ∈ Z, c b * (z - b)⁻¹)) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      (fun z hz => ((hΦan z hz).continuousAt).continuousWithinAt)
      (fun z hz => (hΦan z (Metric.ball_subset_closedBall hz.1)).differentiableAt)

  have hZsphere : ∀ z ∈ Metric.sphere z₀ R, z ∉ Z := by
    intro z hzs hzZ
    have h₁ := hZ z hzZ
    rw [Metric.mem_ball] at h₁
    rw [Metric.mem_sphere] at hzs
    exact absurd hzs (ne_of_lt h₁)

  have h1 : (∮ z in C(z₀, R), (h z - ∑ b ∈ Z, c b * (z - b)⁻¹)) = 0 := by
    rw [circleIntegral.integral_congr (R := R) (c := z₀)
      (f := fun z => h z - ∑ b ∈ Z, c b * (z - b)⁻¹)
      (g := fun z => if hz : z ∈ Z then g z hz z - ∑ b ∈ Z.erase z, c b * (z - b)⁻¹
            else h z - ∑ b ∈ Z, c b * (z - b)⁻¹)
      hR.le (fun z hzs => by simp only [dite_eq_right (hZsphere z hzs)])]
    exact h0

  have hIntTerm : ∀ b ∈ Z, CircleIntegrable (fun z => c b * (z - b)⁻¹) z₀ R := by
    intro b hb
    have hbs : b ∉ Metric.sphere z₀ |R| := by
      intro hmem
      have h₁ := hZ b hb
      rw [Metric.mem_ball] at h₁
      rw [Metric.mem_sphere, abs_of_pos hR] at hmem
      exact absurd hmem (ne_of_lt h₁)
    have h₁ : CircleIntegrable (fun z => (z - b)⁻¹) z₀ R :=
      circleIntegrable_sub_inv_iff.mpr (Or.inr hbs)
    have heq : (c b • fun z : ℂ => (z - b)⁻¹) = fun z => c b * (z - b)⁻¹ := by
      funext w; simp [smul_eq_mul]
    exact heq ▸ h₁.const_smul
  have hInth : CircleIntegrable h z₀ R :=
    ContinuousOn.circleIntegrable hR.le fun z hzs =>
      ((hh z (Metric.sphere_subset_closedBall hzs) (hZsphere z hzs)).continuousAt).continuousWithinAt
  have hIntP : CircleIntegrable (fun z => ∑ b ∈ Z, c b * (z - b)⁻¹) z₀ R := by
    have h₁ := CircleIntegrable.sum Z hIntTerm
    have heq : (∑ b ∈ Z, fun z => c b * (z - b)⁻¹)
        = fun z => ∑ b ∈ Z, c b * (z - b)⁻¹ := by
      funext w; simp
    exact heq ▸ h₁

  have h2 : (∮ z in C(z₀, R), h z) = ∮ z in C(z₀, R), ∑ b ∈ Z, c b * (z - b)⁻¹ := by
    have h₁ : (∮ z in C(z₀, R), h z) - (∮ z in C(z₀, R), ∑ b ∈ Z, c b * (z - b)⁻¹) = 0 := by
      rw [← circleIntegral.integral_sub hInth hIntP]
      exact h1
    exact sub_eq_zero.mp h₁

  have hterm : ∀ b ∈ Z, (∮ z in C(z₀, R), c b * (z - b)⁻¹)
      = c b * (2 * Real.pi * Complex.I) := by
    intro b hb
    have h₁ := circleIntegral.integral_smul (c b) (fun z => (z - b)⁻¹) z₀ R
    simp only [smul_eq_mul] at h₁
    rw [h₁, circleIntegral.integral_sub_inv_of_mem_ball (hZ b hb)]
  have h3 : (∮ z in C(z₀, R), ∑ b ∈ Z, c b * (z - b)⁻¹)
      = ∑ b ∈ Z, c b * (2 * Real.pi * Complex.I) := by
    rw [circleIntegral.integral_fun_sum hIntTerm]
    exact Finset.sum_congr rfl hterm
  rw [h2, h3, ← Finset.sum_mul]
  ring

/-- **Differentiability of the circle integral in the pole parameter.** For `Φ`, `G` analytic on
the circle `C(z₀, r)` and `Φ` avoiding `t₀` there, the function
`t ↦ ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t)` is complex differentiable at `t₀`, with
derivative `∮ z in C(z₀, r), deriv G z / (Φ z - t₀)`. -/
theorem hasDerivAt_circleIntegral_mul_deriv_div_sub {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀ := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_sub hr hΦ hne

  have cG : ContinuousOn G (sphere z₀ r) := fun z hz => (hG z hz).continuousAt.continuousWithinAt
  have cΦ : ContinuousOn Φ (sphere z₀ r) := fun z hz => (hΦ z hz).continuousAt.continuousWithinAt
  have cΦ' : ContinuousOn (deriv Φ) (sphere z₀ r) := fun z hz =>
    (hΦ z hz).deriv.continuousAt.continuousWithinAt
  obtain ⟨MG, hMG⟩ := (isCompact_sphere z₀ r).exists_bound_of_continuousOn cG
  obtain ⟨MΦ, hMΦ⟩ := (isCompact_sphere z₀ r).exists_bound_of_continuousOn cΦ'
  have hMG0 : 0 ≤ MG := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := z₀)).2 hr.le
    exact (norm_nonneg _).trans (hMG x hx)
  have hMΦ0 : 0 ≤ MΦ := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := z₀)).2 hr.le
    exact (norm_nonneg _).trans (hMΦ x hx)

  have hlow : ∀ t ∈ ball t₀ (δ / 2), ∀ z ∈ sphere z₀ r, δ / 2 ≤ ‖Φ z - t‖ := by
    intro t ht z hz
    have h1 := hδle z hz
    have h2 : ‖t - t₀‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at ht
    have h3 : ‖Φ z - t₀‖ ≤ ‖Φ z - t‖ + ‖t - t₀‖ := by
      calc ‖Φ z - t₀‖ = ‖(Φ z - t) + (t - t₀)‖ := by ring_nf
        _ ≤ ‖Φ z - t‖ + ‖t - t₀‖ := norm_add_le _ _
    linarith
  have hne' : ∀ t ∈ ball t₀ (δ / 2), ∀ z ∈ sphere z₀ r, Φ z - t ≠ 0 := by
    intro t ht z hz h
    have := hlow t ht z hz
    rw [h, norm_zero] at this
    linarith

  set F : ℂ → ℝ → ℂ := fun t θ =>
    deriv (circleMap z₀ r) θ • (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ) /
      (Φ (circleMap z₀ r θ) - t)) with hF
  set F' : ℂ → ℝ → ℂ := fun t θ =>
    deriv (circleMap z₀ r) θ • (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ) /
      (Φ (circleMap z₀ r θ) - t) ^ 2) with hF'
  have hsph : ∀ θ : ℝ, circleMap z₀ r θ ∈ sphere z₀ r := fun θ => circleMap_mem_sphere z₀ hr.le θ
  have hcd : Continuous (deriv (circleMap z₀ r)) :=
    (contDiff_circleMap z₀ r).continuous_deriv le_top

  have hFc : ∀ t ∈ ball t₀ (δ / 2), Continuous (F t) := by
    intro t ht
    have hK : ContinuousOn (fun z => G z * deriv Φ z / (Φ z - t)) (sphere z₀ r) :=
      (cG.mul cΦ').div (cΦ.sub continuousOn_const) (hne' t ht)
    exact hcd.smul (hK.comp_continuous (continuous_circleMap z₀ r) hsph)
  have hF'c : ∀ t ∈ ball t₀ (δ / 2), Continuous (F' t) := by
    intro t ht
    have hK : ContinuousOn (fun z => G z * deriv Φ z / (Φ z - t) ^ 2) (sphere z₀ r) :=
      (cG.mul cΦ').div ((cΦ.sub continuousOn_const).pow 2)
        fun z hz => pow_ne_zero 2 (hne' t ht z hz)
    exact hcd.smul (hK.comp_continuous (continuous_circleMap z₀ r) hsph)
  have ht₀ : t₀ ∈ ball t₀ (δ / 2) := mem_ball_self (half_pos hδ)

  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume) (a := 0) (b := 2 * π) (F := F) (F' := F') (x₀ := t₀)
    (s := ball t₀ (δ / 2)) (bound := fun _ => r * (MG * MΦ / (δ / 2) ^ 2))
    (ball_mem_nhds t₀ (half_pos hδ))
    (by
      filter_upwards [ball_mem_nhds t₀ (half_pos hδ)] with t ht
      exact (hFc t ht).aestronglyMeasurable)
    ((hFc t₀ ht₀).intervalIntegrable 0 (2 * π))
    (hF'c t₀ ht₀).aestronglyMeasurable
    (by
      refine Filter.Eventually.of_forall fun θ _ t ht => ?_
      have hz := hsph θ
      have hlo := hlow t ht _ hz
      have hpos : 0 < ‖Φ (circleMap z₀ r θ) - t‖ := lt_of_lt_of_le (half_pos hδ) hlo
      simp only [hF', norm_smul, norm_div, norm_mul, norm_pow]
      have hnum : ‖G (circleMap z₀ r θ)‖ * ‖deriv Φ (circleMap z₀ r θ)‖ ≤ MG * MΦ :=
        mul_le_mul (hMG _ hz) (hMΦ _ hz) (norm_nonneg _) hMG0
      have hden : (δ / 2) ^ 2 ≤ ‖Φ (circleMap z₀ r θ) - t‖ ^ 2 :=
        pow_le_pow_left₀ (half_pos hδ).le hlo 2
      have hfrac : ‖G (circleMap z₀ r θ)‖ * ‖deriv Φ (circleMap z₀ r θ)‖ /
          ‖Φ (circleMap z₀ r θ) - t‖ ^ 2 ≤ MG * MΦ / (δ / 2) ^ 2 :=
        div_le_div₀ (mul_nonneg hMG0 hMΦ0) hnum (pow_pos (half_pos hδ) 2) hden
      exact mul_le_mul (norm_deriv_circleMap_le hr θ) hfrac
        (div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2))
        hr.le)
    intervalIntegrable_const
    (by
      refine Filter.Eventually.of_forall fun θ _ t ht => ?_
      have hz := hsph θ
      have hne0 : Φ (circleMap z₀ r θ) - t ≠ 0 := hne' t ht _ hz
      have h1 : HasDerivAt (fun s : ℂ => Φ (circleMap z₀ r θ) - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (Φ (circleMap z₀ r θ))
      have h2 := (h1.inv hne0).const_mul (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ))
      have h3 := h2.const_smul (deriv (circleMap z₀ r) θ)
      refine (h3.congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [hF', neg_neg, one_mul, div_eq_mul_inv]
      · exact Filter.Eventually.of_forall fun s => by
          simp only [hF, div_eq_mul_inv, Pi.smul_apply, Pi.inv_apply, smul_eq_mul])
  have hd := key.2

  have hval : (∫ θ in (0 : ℝ)..2 * π, F' t₀ θ) = ∮ z in C(z₀, r), deriv G z / (Φ z - t₀) := by
    rw [← circleIntegral_mul_deriv_div_sq_eq hr hΦ hG hne]
    rfl
  rw [hval] at hd
  exact hd

end Complex
