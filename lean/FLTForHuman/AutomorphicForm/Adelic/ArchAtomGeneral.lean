/-
  The general archimedean atom integrals.

  The two evaluations of `ArchAtomValues` are the `k = 0` and `a = b = 0` cases of the two general
  statements carried here, and each of these proofs *uses* its special case at the point where the
  recursion bottoms out:

  * `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` — at a real place, with the
    weight `((x - I)/√(1+x²))^k`:

      `∫ x, ((x - I)/√(1+x²))^k · (1+x²)^-(s+1/2)
         = (-I)^k · Γ_ℝ(2s)·Γ_ℝ(2s+1) / (Γ_ℝ(2s+1+k)·Γ_ℝ(2s+1-k))`   (`re s > 0`),

    by a recursion on `k`: `HasDerivAt` of the phase and its integer powers, a primitive `Q` of the
    weight, the boundary terms at `±∞` and the `k = 0` base case;
  * `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` — at a complex place, the moment integral

      `∫ z, z^a · conj z^b · (1+‖z‖²)^-t = π · a! · Γ(t-1-a) / Γ t` if `a = b`, else `0`
      (`((a:ℝ)+b)/2 + 1 < re t`),

    by a recursion on the moment: the angular integral vanishes off the diagonal, and the radial
    moment advances by integration by parts against the `t = 2s+1` case.

  Transcribed from two pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg.lean`

  The pin's file-level labels (`M4aP2DGK.ArchRealWeight`, `M4aP2DGK.ArchComplexMoments`) become the
  subject namespaces below, with the pin's file prefix dropped. The pin's `S_` files import `Mathlib`;
  this module names the modules they need.

  **Visibility.** Both pin files are private preludes with one public headline each, and both are kept
  that way here: the checked surface at the pin's visibility is the two headlines, and the helpers are
  matched only by the dropped-`private` reading.

  **Wiring.** `spec/check_port.py` owns the two headlines: the two wrappers and the two `S_` files are
  the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchAtomValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace AutomorphicForm

namespace LocalIntertwining

namespace ArchRealWeight

open MeasureTheory Filter Topology Complex

private def rad (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

private def base (x : ℝ) : ℂ := ((1 + x ^ 2 : ℝ) : ℂ)

private def phase (x : ℝ) : ℂ := ((x : ℂ) - I) / ((rad x : ℝ) : ℂ)

private def Q (c : ℂ) (x : ℝ) : ℂ := base x ^ (-c)

private def J (k : ℤ) (c : ℂ) : ℂ := ∫ x : ℝ, phase x ^ k * Q c x

private def RHS (k : ℤ) (s : ℂ) : ℂ :=
  (-I) ^ k * (Gammaℝ (2 * s) * Gammaℝ (2 * s + 1)) / (Gammaℝ (2 * s + 1 + k) * Gammaℝ (2 * s + 1 - k))

private theorem one_add_sq_pos (x : ℝ) : (0 : ℝ) < 1 + x ^ 2 := by positivity

private theorem rad_pos (x : ℝ) : 0 < rad x := Real.sqrt_pos.mpr (one_add_sq_pos x)

private theorem rad_sq (x : ℝ) : rad x ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (one_add_sq_pos x).le

private theorem radC_ne_zero (x : ℝ) : ((rad x : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (rad_pos x).ne'

private theorem radC_sq (x : ℝ) : ((rad x : ℝ) : ℂ) ^ 2 = base x := by
  unfold base
  exact_mod_cast rad_sq x

private theorem radC_sq' (x : ℝ) : ((rad x : ℝ) : ℂ) ^ 2 = 1 + (x : ℂ) ^ 2 := by
  rw [radC_sq]
  unfold base
  push_cast
  ring

private theorem base_ne_zero (x : ℝ) : base x ≠ 0 := by
  unfold base
  exact_mod_cast (one_add_sq_pos x).ne'

private theorem base_mem_slitPlane (x : ℝ) : base x ∈ slitPlane := by
  unfold base
  exact Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

private theorem sub_I_ne_zero (x : ℝ) : (x : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem phase_ne_zero (x : ℝ) : phase x ≠ 0 :=
  div_ne_zero (sub_I_ne_zero x) (radC_ne_zero x)

private theorem norm_sub_I (x : ℝ) : ‖(x : ℂ) - I‖ = rad x := by
  have h : ‖(x : ℂ) - I‖ ^ 2 = 1 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im,
      Complex.ofReal_im, Complex.I_im, zero_sub]
    ring
  rw [← Real.sqrt_sq (norm_nonneg ((x : ℂ) - I)), h]
  rfl

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [norm_div, norm_sub_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rad_pos x)]
  exact div_self (rad_pos x).ne'

private theorem norm_Q (c : ℂ) (x : ℝ) : ‖Q c x‖ = (1 + x ^ 2) ^ (-c.re) := by
  unfold Q base
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  simp

private theorem norm_phase_zpow_mul_Q (k : ℤ) (c : ℂ) (x : ℝ) :
    ‖phase x ^ k * Q c x‖ = (1 + x ^ 2) ^ (-c.re) := by
  rw [norm_mul, norm_zpow, norm_phase, one_zpow, one_mul, norm_Q]

private theorem Q_div_base (c : ℂ) (x : ℝ) : Q c x / base x = Q (c + 1) x := by
  unfold Q
  rw [div_eq_mul_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (base_ne_zero x)]
  congr 1
  ring

private theorem base_cpow_neg_sub_one (c : ℂ) (x : ℝ) : base x ^ (-c - 1) = Q (c + 1) x := by
  unfold Q
  congr 1
  ring

private theorem radC_eq_base_cpow_half (x : ℝ) : ((rad x : ℝ) : ℂ) = base x ^ ((1 / 2 : ℂ)) := by
  unfold rad base
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (one_add_sq_pos x).le]
  congr 1
  push_cast
  ring

private theorem rad_mul_Q (c : ℂ) (x : ℝ) : ((rad x : ℝ) : ℂ) * Q (c + 1) x = Q (c + 1 / 2) x := by
  unfold Q
  rw [radC_eq_base_cpow_half, ← Complex.cpow_add _ _ (base_ne_zero x)]
  congr 1
  ring

private theorem ofReal_eq_rad_mul_phase_add_I (x : ℝ) : (x : ℂ) = ((rad x : ℝ) : ℂ) * phase x + I := by
  unfold phase
  rw [mul_comm ((rad x : ℝ) : ℂ) _, div_mul_cancel₀ _ (radC_ne_zero x)]
  ring

private theorem phase_mul_phase_neg (x : ℝ) : phase x * phase (-x) = -1 := by
  have hr : rad (-x) = rad x := by
    unfold rad
    rw [neg_sq]
  have hR := radC_ne_zero x
  unfold phase
  rw [hr, div_mul_div_comm, div_eq_iff (mul_ne_zero hR hR), ← pow_two, radC_sq']
  push_cast
  linear_combination Complex.I_sq

private theorem phase_neg (x : ℝ) : phase (-x) = -(phase x)⁻¹ := by
  have h0 := phase_ne_zero x
  have h1 : phase (-x) = -1 / phase x := by
    rw [eq_div_iff h0, mul_comm]
    exact phase_mul_phase_neg x
  rw [h1, neg_div, one_div]

private theorem Q_neg (c : ℂ) (x : ℝ) : Q c (-x) = Q c x := by
  unfold Q base
  rw [neg_sq]

private theorem continuous_phase : Continuous phase := by
  unfold phase rad
  refine Continuous.div (Complex.continuous_ofReal.sub continuous_const)
    (Complex.continuous_ofReal.comp ((continuous_const.add (continuous_pow 2)).sqrt)) ?_
  intro x
  exact radC_ne_zero x

private theorem continuous_Q (c : ℂ) : Continuous (Q c) := by
  unfold Q base
  refine Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.add (continuous_pow 2)))
    continuous_const ?_
  intro x
  left
  rw [Complex.ofReal_re]
  exact one_add_sq_pos x

private theorem continuous_phase_zpow_mul_Q (k : ℤ) (c : ℂ) :
    Continuous (fun x : ℝ => phase x ^ k * Q c x) :=
  (continuous_phase.zpow₀ k fun x => Or.inl (phase_ne_zero x)).mul (continuous_Q c)

private theorem integrable_phase_zpow_mul_Q (k : ℤ) {c : ℂ} (hc : 1 / 2 < c.re) :
    Integrable (fun x : ℝ => phase x ^ k * Q c x) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * c.re := by
    simp
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono'
    (continuous_phase_zpow_mul_Q k c).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_phase_zpow_mul_Q, Real.norm_eq_abs, sq_abs]
  apply le_of_eq
  congr 1
  ring

private theorem tendsto_phase_zpow_mul_Q_atTop (k : ℤ) {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun x : ℝ => phase x ^ k * Q c x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun t : ℝ => t ^ (-c.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  have h3 := h2.comp h1
  refine h3.congr fun x => ?_
  show (1 + x ^ 2) ^ (-c.re) = ‖phase x ^ k * Q c x‖
  rw [norm_phase_zpow_mul_Q]

private theorem tendsto_phase_zpow_mul_Q_atBot (k : ℤ) {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun x : ℝ => phase x ^ k * Q c x) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun x : ℝ => 1 + x ^ 2) atBot atTop := by
    have : Tendsto (fun x : ℝ => 1 + (-x) ^ 2) atBot atTop :=
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)).comp tendsto_neg_atBot_atTop
    simpa [neg_sq] using this
  have h2 : Tendsto (fun t : ℝ => t ^ (-c.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  have h3 := h2.comp h1
  refine h3.congr fun x => ?_
  show (1 + x ^ 2) ^ (-c.re) = ‖phase x ^ k * Q c x‖
  rw [norm_phase_zpow_mul_Q]

private theorem hasDerivAt_phase (x : ℝ) : HasDerivAt phase (I * phase x / base x) x := by
  have hN : HasDerivAt (fun y : ℝ => (y : ℂ) - I) 1 x := by
    have h := (hasDerivAt_id x).ofReal_comp
    simpa using h.sub_const I
  have hsq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_pow 2 x).const_add 1
    simpa using h
  have hne : 1 + x ^ 2 ≠ 0 := (one_add_sq_pos x).ne'
  have hs0 : Real.sqrt (1 + x ^ 2) ≠ 0 := (rad_pos x).ne'
  have hR : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2)) (2 * x / (2 * Real.sqrt (1 + x ^ 2))) x :=
    hsq.sqrt hne
  have hRC : HasDerivAt (fun y : ℝ => ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ))
      (((2 * x / (2 * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ)) x := hR.ofReal_comp
  have hdiv := hN.div hRC (radC_ne_zero x)
  refine hdiv.congr_deriv ?_
  have hrC := radC_ne_zero x
  have hd : ((2 * x / (2 * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ) = (x : ℂ) / ((rad x : ℝ) : ℂ) := by
    have e : (2 * x / (2 * Real.sqrt (1 + x ^ 2)) : ℝ) = x / rad x := by
      unfold rad
      rw [div_eq_div_iff (mul_ne_zero two_ne_zero hs0) hs0]
      ring
    rw [e, Complex.ofReal_div]
  rw [hd]
  unfold phase
  change (1 * ((rad x : ℝ) : ℂ) - ((x : ℂ) - I) * ((x : ℂ) / ((rad x : ℝ) : ℂ))) / ((rad x : ℝ) : ℂ) ^ 2
      = I * (((x : ℂ) - I) / ((rad x : ℝ) : ℂ)) / base x
  rw [← radC_sq x, div_left_inj' (pow_ne_zero 2 hrC), ← mul_left_inj' hrC, sub_mul, one_mul]
  rw [show ((x : ℂ) - I) * ((x : ℂ) / ((rad x : ℝ) : ℂ)) * ((rad x : ℝ) : ℂ) = ((x : ℂ) - I) * x by
        rw [mul_assoc, div_mul_cancel₀ _ hrC]]
  rw [show I * (((x : ℂ) - I) / ((rad x : ℝ) : ℂ)) * ((rad x : ℝ) : ℂ) = I * ((x : ℂ) - I) by
        rw [mul_assoc, div_mul_cancel₀ _ hrC]]
  linear_combination radC_sq' x + Complex.I_sq

private theorem hasDerivAt_phase_zpow (k : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => phase y ^ k) ((k : ℂ) * I * (phase x ^ k / base x)) x := by
  have h := (hasDerivAt_zpow k (phase x) (Or.inl (phase_ne_zero x))).comp x (hasDerivAt_phase x)
  refine h.congr_deriv ?_
  have h0 := phase_ne_zero x
  rw [zpow_sub_one₀ h0 k]
  calc (k : ℂ) * (phase x ^ k * (phase x)⁻¹) * (I * phase x / base x)
      = (k : ℂ) * I * (phase x ^ k / base x) * ((phase x)⁻¹ * phase x) := by ring
    _ = (k : ℂ) * I * (phase x ^ k / base x) := by rw [inv_mul_cancel₀ h0, mul_one]

private theorem hasDerivAt_Q (c : ℂ) (x : ℝ) :
    HasDerivAt (Q c) (-(2 * c) * (x : ℂ) * Q (c + 1) x) x := by
  have hu : HasDerivAt (fun y : ℝ => ((1 + y ^ 2 : ℝ) : ℂ)) (((2 * x : ℝ)) : ℂ) x := by
    have h := ((hasDerivAt_pow 2 x).const_add 1).ofReal_comp
    refine h.congr_deriv ?_
    push_cast
    ring
  have hc := (Complex.hasStrictDerivAt_cpow_const (c := -c) (base_mem_slitPlane x)).hasDerivAt.comp x hu
  have hc' : HasDerivAt (Q c) (-c * base x ^ (-c - 1) * (((2 * x : ℝ)) : ℂ)) x := hc
  refine hc'.congr_deriv ?_
  rw [base_cpow_neg_sub_one]
  push_cast
  ring

private theorem hasDerivAt_G (k : ℤ) (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => phase y ^ k * Q c y)
      (I * ((k : ℂ) - 2 * c) * (phase x ^ k * Q (c + 1) x)
        - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x)) x := by
  have h := (hasDerivAt_phase_zpow k x).mul (hasDerivAt_Q c x)
  refine h.congr_deriv ?_
  have hQ : phase x ^ k / base x * Q c x = phase x ^ k * Q (c + 1) x := by
    rw [div_mul_eq_mul_div, mul_div_assoc, Q_div_base]
  have hx : (x : ℂ) * (phase x ^ k * Q (c + 1) x)
      = phase x ^ (k + 1) * Q (c + 1 / 2) x + I * (phase x ^ k * Q (c + 1) x) := by
    conv_lhs => rw [ofReal_eq_rad_mul_phase_add_I x]
    rw [zpow_add_one₀ (phase_ne_zero x), ← rad_mul_Q c x]
    ring
  calc (k : ℂ) * I * (phase x ^ k / base x) * Q c x + phase x ^ k * (-(2 * c) * (x : ℂ) * Q (c + 1) x)
      = (k : ℂ) * I * (phase x ^ k / base x * Q c x)
          - 2 * c * ((x : ℂ) * (phase x ^ k * Q (c + 1) x)) := by ring
    _ = (k : ℂ) * I * (phase x ^ k * Q (c + 1) x)
          - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x + I * (phase x ^ k * Q (c + 1) x)) := by
        rw [hQ, hx]
    _ = I * ((k : ℂ) - 2 * c) * (phase x ^ k * Q (c + 1) x)
          - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x) := by ring

private theorem recursion_raw (k : ℤ) {c : ℂ} (hc : 0 < c.re) :
    2 * c * J (k + 1) (c + 1 / 2) = I * ((k : ℂ) - 2 * c) * J k (c + 1) := by
  have hc1 : 1 / 2 < (c + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hc2 : 1 / 2 < (c + 1 / 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hI1 : Integrable (fun x : ℝ => phase x ^ k * Q (c + 1) x) :=
    integrable_phase_zpow_mul_Q k hc1
  have hI2 : Integrable (fun x : ℝ => phase x ^ (k + 1) * Q (c + 1 / 2) x) :=
    integrable_phase_zpow_mul_Q (k + 1) hc2
  have hderiv := fun x => hasDerivAt_G k c x
  have hint : Integrable (fun x : ℝ => I * ((k : ℂ) - 2 * c) * (phase x ^ k * Q (c + 1) x)
      - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x)) :=
    (hI1.const_mul _).sub (hI2.const_mul _)
  have hzero := integral_of_hasDerivAt_of_tendsto hderiv hint
    (tendsto_phase_zpow_mul_Q_atBot k hc) (tendsto_phase_zpow_mul_Q_atTop k hc)
  rw [sub_zero, integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
    integral_const_mul] at hzero
  unfold J
  linear_combination (-1 : ℂ) * hzero

private theorem recursion (k : ℤ) {s : ℂ} (hs : 0 < s.re) :
    J (k + 1) (s + 1 / 2) = -I * ((s - (k : ℂ) / 2) / s) * J k (s + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have h := recursion_raw k hs
  have h2 : (2 : ℂ) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have h3 : J (k + 1) (s + 1 / 2) = (2 * s)⁻¹ * (I * ((k : ℂ) - 2 * s) * J k (s + 1)) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  rw [h3]
  field_simp
  ring

private theorem closed_form_zero {s : ℂ} (hs : 0 < s.re) : J 0 (s + 1 / 2) = RHS 0 s := by
  have hB : Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  have hbase := AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div s hs
  unfold J RHS
  simp only [zpow_zero, one_mul, Int.cast_zero, add_zero, sub_zero]
  unfold Q base
  rw [hbase, mul_div_mul_right _ _ hB]

private theorem RHS_step (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    RHS ((k : ℤ) + 1) s = -I * ((s - (k : ℂ) / 2) / s) * RHS k (s + 1 / 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hA : Gammaℝ (2 * s) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.mul_re]
    norm_num
    linarith
  have hB : Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  have hD : Gammaℝ (2 * s + 2 + k) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.add_re, Complex.mul_re, Complex.natCast_re]
    norm_num
    linarith
  have hC : Gammaℝ (2 * s + 2) = Gammaℝ (2 * s) * (2 * s) / 2 / Real.pi :=
    Complex.Gammaℝ_add_two (mul_ne_zero two_ne_zero hs0)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero

  have g1 : Gammaℝ (2 * s + 1 + (((k : ℤ) + 1 : ℤ) : ℂ)) = Gammaℝ (2 * s + 2 + k) := by
    congr 1; push_cast; ring
  have g2 : Gammaℝ (2 * s + 1 - (((k : ℤ) + 1 : ℤ) : ℂ)) = Gammaℝ (2 * s - k) := by
    congr 1; push_cast; ring
  have g3 : Gammaℝ (2 * (s + 1 / 2)) = Gammaℝ (2 * s + 1) := by
    congr 1; ring
  have g4 : Gammaℝ (2 * (s + 1 / 2) + 1) = Gammaℝ (2 * s + 2) := by
    congr 1; ring
  have g5 : Gammaℝ (2 * (s + 1 / 2) + 1 + ((k : ℤ) : ℂ)) = Gammaℝ (2 * s + 2 + k) := by
    congr 1; push_cast; ring
  have g6 : Gammaℝ (2 * (s + 1 / 2) + 1 - ((k : ℤ) : ℂ)) = Gammaℝ (2 * s + 2 - k) := by
    congr 1; push_cast; ring
  unfold RHS
  rw [g1, g2, g3, g4, g5, g6]
  by_cases hE : Gammaℝ (2 * s - k) = 0
  ·
    rw [hE, mul_zero, div_zero]
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hE
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    ·
      subst hn0
      have hsk : s - (k : ℂ) / 2 = 0 := by
        simp only [Nat.cast_zero, mul_zero, neg_zero] at hn
        linear_combination hn / 2
      rw [hsk]
      simp
    ·
      have hF : Gammaℝ (2 * s + 2 - k) = 0 := by
        refine Complex.Gammaℝ_eq_zero_iff.mpr ⟨n - 1, ?_⟩
        have e : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          rw [Nat.cast_sub hnpos]
          simp
        rw [e]
        linear_combination hn
      rw [hF, mul_zero, div_zero, mul_zero]
  ·
    have hk0 : (2 * s - k : ℂ) ≠ 0 := by
      intro h0
      apply hE
      rw [h0]
      exact Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
    have hF : Gammaℝ (2 * s + 2 - k) = Gammaℝ (2 * s - k) * (2 * s - k) / 2 / Real.pi := by
      rw [show (2 * s + 2 - k : ℂ) = (2 * s - k) + 2 by ring]
      exact Complex.Gammaℝ_add_two hk0
    rw [hF, hC, zpow_add_one₀ hI0]
    field_simp

private theorem closed_form_nat (k : ℕ) : ∀ {s : ℂ}, 0 < s.re → J k (s + 1 / 2) = RHS k s := by
  induction k with
  | zero =>
      intro s hs
      exact_mod_cast closed_form_zero hs
  | succ k ih =>
      intro s hs
      have hs' : 0 < (s + 1 / 2).re := by
        rw [Complex.add_re]
        norm_num
        linarith
      have hrec := recursion (k : ℤ) hs
      push_cast at hrec
      have hih := ih hs'
      have e1 : J (k : ℤ) (s + 1) = RHS k (s + 1 / 2) := by
        rw [← hih]
        congr 1
        ring
      push_cast
      rw [hrec, e1, RHS_step k hs]

private theorem J_neg (k : ℤ) (c : ℂ) : J (-k) c = (-1) ^ k * J k c := by
  unfold J
  have h := integral_neg_eq_self (fun x : ℝ => phase x ^ (-k) * Q c x) volume
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [phase_neg, Q_neg]
  have e : -(phase x)⁻¹ = (-1) * (phase x)⁻¹ := by ring
  rw [e, mul_zpow, inv_zpow', neg_neg, zpow_neg, ← inv_zpow, inv_neg_one]
  ring

private theorem RHS_neg (k : ℤ) (s : ℂ) : RHS (-k) s = (-1) ^ k * RHS k s := by
  have hI : (-I : ℂ) ^ (-k) = (-1) ^ k * (-I) ^ k := by
    rw [zpow_neg, ← inv_zpow, ← mul_zpow]
    congr 1
    rw [inv_neg, Complex.inv_I]
    ring
  have e1 : Gammaℝ (2 * s + 1 + ((-k : ℤ) : ℂ)) = Gammaℝ (2 * s + 1 - k) := by
    congr 1; push_cast; ring
  have e2 : Gammaℝ (2 * s + 1 - ((-k : ℤ) : ℂ)) = Gammaℝ (2 * s + 1 + k) := by
    congr 1; push_cast; ring
  unfold RHS
  rw [hI, e1, e2]
  ring

private theorem closed_form (k : ℤ) {s : ℂ} (hs : 0 < s.re) : J k (s + 1 / 2) = RHS k s := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact closed_form_nat n hs
  · rw [J_neg, RHS_neg, closed_form_nat n hs]

private theorem main (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (-Complex.I) ^ k * (Complex.Gammaℝ (2 * s) * Complex.Gammaℝ (2 * s + 1))
          / (Complex.Gammaℝ (2 * s + 1 + k) * Complex.Gammaℝ (2 * s + 1 - k)) :=
  closed_form k hs

end ArchRealWeight

theorem integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
    (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (-Complex.I) ^ k * (Complex.Gammaℝ (2 * s) * Complex.Gammaℝ (2 * s + 1))
          / (Complex.Gammaℝ (2 * s + 1 + k) * Complex.Gammaℝ (2 * s + 1 - k)) :=
  ArchRealWeight.main k s hs

namespace ArchComplexMoments

open MeasureTheory Set Complex Filter
open scoped ComplexConjugate

private def W (t : ℂ) (z : ℂ) : ℂ := ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)

private def M (a : ℕ) (t : ℂ) : ℂ := ∫ z : ℂ, z ^ a * conj z ^ a * W t z

private theorem one_add_norm_sq_pos (z : ℂ) : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity

private theorem baseC_ne_zero (z : ℂ) : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (one_add_norm_sq_pos z).ne'

private theorem continuous_W (t : ℂ) : Continuous (W t) := by
  unfold W
  refine Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2)))
    continuous_const ?_
  intro z
  exact Complex.ofReal_mem_slitPlane.mpr (one_add_norm_sq_pos z)

private theorem norm_W (t : ℂ) (z : ℂ) : ‖W t z‖ = (1 + ‖z‖ ^ 2) ^ (-t.re) := by
  unfold W
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (one_add_norm_sq_pos z)]
  simp

private theorem conj_ofReal_mul_exp (r θ : ℝ) :
    conj ((r : ℂ) * cexp ((θ : ℂ) * I)) = (r : ℂ) * cexp (-((θ : ℂ) * I)) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg]

private theorem angular_eq_zero {a b : ℕ} (hab : a ≠ b) :
    ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b = 0 := by
  set c : ℂ := ((a : ℂ) - b) * I with hc_def
  have hc : c ≠ 0 := by
    refine mul_ne_zero (sub_ne_zero.mpr ?_) Complex.I_ne_zero
    exact_mod_cast hab
  have hpt : ∀ θ : ℝ, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b = cexp (c * θ) := by
    intro θ
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [hc_def]
    ring
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b
      = ∫ θ in Ioo (-Real.pi) Real.pi, cexp (c * θ) :=
        setIntegral_congr_fun measurableSet_Ioo fun θ _ => hpt θ
    _ = ∫ θ in Ioc (-Real.pi) Real.pi, cexp (c * θ) := (integral_Ioc_eq_integral_Ioo).symm
    _ = ∫ θ in (-Real.pi)..Real.pi, cexp (c * θ) := (intervalIntegral.integral_of_le hle).symm
    _ = (cexp (c * Real.pi) - cexp (c * (-Real.pi : ℝ))) / c := integral_exp_mul_complex hc
    _ = 0 := by
        have hper : c * (Real.pi : ℂ) = c * ((-Real.pi : ℝ) : ℂ) + (((a : ℤ) - b : ℤ) : ℂ) * (2 * Real.pi * I) := by
          rw [hc_def]
          push_cast
          ring
        rw [hper, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]

private theorem integral_eq_zero_of_ne (a b : ℕ) (t : ℂ) (hab : a ≠ b) :
    ∫ z : ℂ, z ^ a * conj z ^ b * W t z = 0 := by
  have hEq : EqOn
      (fun p : ℝ × ℝ => p.1 • ((Complex.polarCoord.symm p) ^ a * conj (Complex.polarCoord.symm p) ^ b
        * W t (Complex.polarCoord.symm p)))
      (fun p : ℝ × ℝ => ((p.1 : ℂ) * (p.1 : ℂ) ^ (a + b) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-t))
        * (cexp ((p.2 : ℂ) * I) ^ a * cexp (-((p.2 : ℂ) * I)) ^ b))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    intro p _
    simp only []
    unfold W
    rw [Complex.norm_polarCoord_symm, sq_abs, Complex.polarCoord_symm_apply, Complex.ofReal_cos,
      Complex.ofReal_sin, ← Complex.exp_mul_I, conj_ofReal_mul_exp, mul_pow, mul_pow, Complex.real_smul,
      pow_add]
    ring
  have hprod : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ((p.1 : ℂ) * (p.1 : ℂ) ^ (a + b) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-t))
          * (cexp ((p.2 : ℂ) * I) ^ a * cexp (-((p.2 : ℂ) * I)) ^ b) ∂((volume : Measure ℝ).prod volume))
      = (∫ r in Ioi (0 : ℝ), (r : ℂ) * (r : ℂ) ^ (a + b) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-t))
          * ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b :=
    setIntegral_prod_mul (fun r : ℝ => (r : ℂ) * (r : ℂ) ^ (a + b) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-t))
      (fun θ : ℝ => cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
  calc ∫ z : ℂ, z ^ a * conj z ^ b * W t z
      = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((Complex.polarCoord.symm p) ^ a * conj (Complex.polarCoord.symm p) ^ b
            * W t (Complex.polarCoord.symm p)) :=
        (Complex.integral_comp_polarCoord_symm (fun z : ℂ => z ^ a * conj z ^ b * W t z)).symm
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ((p.1 : ℂ) * (p.1 : ℂ) ^ (a + b) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-t))
            * (cexp ((p.2 : ℂ) * I) ^ a * cexp (-((p.2 : ℂ) * I)) ^ b)
            ∂((volume : Measure ℝ).prod volume) := by
        rw [Measure.volume_eq_prod]
        exact setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hEq
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * (r : ℂ) ^ (a + b) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-t))
          * ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b := hprod
    _ = 0 := by rw [angular_eq_zero hab, mul_zero]

private theorem norm_moment (a : ℕ) (t : ℂ) (z : ℂ) :
    ‖z ^ a * conj z ^ a * W t z‖ = (‖z‖ ^ 2) ^ a * (1 + ‖z‖ ^ 2) ^ (-t.re) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_W, ← pow_mul, ← pow_add]
  congr 1
  ring

private theorem continuous_moment (a b : ℕ) (t : ℂ) : Continuous fun z : ℂ => z ^ a * conj z ^ b * W t z :=
  ((continuous_id.pow a).mul (Complex.continuous_conj.pow b)).mul (continuous_W t)

private theorem integrable_moment (a : ℕ) {t : ℂ} (ht : (a : ℝ) + 1 < t.re) :
    Integrable (fun z : ℂ => z ^ a * conj z ^ a * W t z) := by
  have hr : (Module.finrank ℝ ℂ : ℝ) < 2 * (t.re - a) := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono' (continuous_moment a a t).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [norm_moment]
  have hpos := one_add_norm_sq_pos z
  have h1 : (‖z‖ ^ 2) ^ a ≤ (1 + ‖z‖ ^ 2) ^ a :=
    pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg ‖z‖]) a
  have h2 : (0 : ℝ) ≤ (1 + ‖z‖ ^ 2) ^ (-t.re) := Real.rpow_nonneg hpos.le _
  calc (‖z‖ ^ 2) ^ a * (1 + ‖z‖ ^ 2) ^ (-t.re)
      ≤ (1 + ‖z‖ ^ 2) ^ a * (1 + ‖z‖ ^ 2) ^ (-t.re) := mul_le_mul_of_nonneg_right h1 h2
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * (t.re - a)) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
        congr 1
        ring

private theorem moment_succ_pointwise (a : ℕ) (t : ℂ) (z : ℂ) :
    z ^ (a + 1) * conj z ^ (a + 1) * W t z = z ^ a * conj z ^ a * W (t - 1) z - z ^ a * conj z ^ a * W t z := by
  have hW : W (t - 1) z = W t z * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    unfold W
    rw [show (-(t - 1) : ℂ) = -t + 1 by ring, Complex.cpow_add _ _ (baseC_ne_zero z), Complex.cpow_one]
  have hzz : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hb : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) = 1 + ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
  rw [hW, hb, pow_succ, pow_succ]
  calc z ^ a * z * (conj z ^ a * conj z) * W t z
      = z ^ a * conj z ^ a * W t z * (z * conj z) := by ring
    _ = z ^ a * conj z ^ a * W t z * ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [hzz]
    _ = z ^ a * conj z ^ a * (W t z * (1 + ((‖z‖ ^ 2 : ℝ) : ℂ))) - z ^ a * conj z ^ a * W t z := by ring

private theorem moment_succ (a : ℕ) {t : ℂ} (ht : (a : ℝ) + 2 < t.re) : M (a + 1) t = M a (t - 1) - M a t := by
  have h1 : Integrable (fun z : ℂ => z ^ a * conj z ^ a * W (t - 1) z) := by
    refine integrable_moment a ?_
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h2 : Integrable (fun z : ℂ => z ^ a * conj z ^ a * W t z) := integrable_moment a (by linarith)
  unfold M
  rw [← integral_sub h1 h2]
  exact integral_congr_ae (Eventually.of_forall fun z => moment_succ_pointwise a t z)

private theorem moment_zero {t : ℂ} (ht : 1 < t.re) : M 0 t = (Real.pi : ℂ) / (t - 1) := by
  have hs : 0 < ((t - 1) / 2).re := by
    have e : ((t - 1) / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) * (t - 1) := by
      push_cast
      ring
    rw [e, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
    linarith
  have h := AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div ((t - 1) / 2) hs
  have e1 : (2 * ((t - 1) / 2) + 1 : ℂ) = t := by ring
  have e2 : (2 * ((t - 1) / 2) : ℂ) = t - 1 := by ring
  rw [e1, e2] at h
  unfold M W
  simp only [pow_zero, one_mul]
  exact h

private theorem closed_form (a : ℕ) :
    ∀ {t : ℂ}, (a : ℝ) + 1 < t.re →
      M a t = (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t := by
  induction a with
  | zero =>
      intro t ht
      push_cast at ht
      have ht1 : 1 < t.re := by linarith
      have hne : t - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
        linarith
      have hGt : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
        have h := Complex.Gamma_add_one (t - 1) hne
        rw [sub_add_cancel] at h
        exact h
      have hG1 : Complex.Gamma (t - 1) ≠ 0 := by
        refine Complex.Gamma_ne_zero_of_re_pos ?_
        rw [Complex.sub_re, Complex.one_re]
        linarith
      rw [moment_zero ht1]
      simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one]
      rw [hGt]
      field_simp
  | succ a ih =>
      intro t ht
      push_cast at ht
      have hrec := moment_succ a (t := t) (by linarith)
      have ih1 := ih (t := t - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith)
      have ih2 := ih (t := t) (by linarith)
      have hne1 : t - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
        linarith
      have hne2 : t - 2 - (a : ℂ) ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        rw [Complex.sub_re, Complex.sub_re, Complex.natCast_re, Complex.zero_re] at this
        norm_num at this
        linarith
      have hGt : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
        have h := Complex.Gamma_add_one (t - 1) hne1
        rw [sub_add_cancel] at h
        exact h
      have hGa : Complex.Gamma (t - 1 - a) = (t - 2 - a) * Complex.Gamma (t - 2 - a) := by
        have h := Complex.Gamma_add_one (t - 2 - a) hne2
        rw [show (t - 2 - (a : ℂ) + 1) = t - 1 - a by ring] at h
        exact h
      have hG1 : Complex.Gamma (t - 1) ≠ 0 := by
        refine Complex.Gamma_ne_zero_of_re_pos ?_
        rw [Complex.sub_re, Complex.one_re]
        linarith
      have e1 : Complex.Gamma (t - 1 - 1 - (a : ℂ)) = Complex.Gamma (t - 2 - a) := by
        congr 1
        ring
      have e2 : Complex.Gamma (t - 1 - ((a + 1 : ℕ) : ℂ)) = Complex.Gamma (t - 2 - a) := by
        congr 1
        push_cast
        ring
      rw [hrec, ih1, ih2, e1, e2, hGa, hGt, Nat.factorial_succ]
      push_cast
      field_simp
      ring

private theorem main (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 := by
  split_ifs with hab
  · subst hab
    have ht' : (a : ℝ) + 1 < t.re := by linarith
    exact closed_form a ht'
  · exact integral_eq_zero_of_ne a b t hab

end ArchComplexMoments

theorem integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
    (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 :=
  ArchComplexMoments.main a b t ht

end LocalIntertwining

end AutomorphicForm
