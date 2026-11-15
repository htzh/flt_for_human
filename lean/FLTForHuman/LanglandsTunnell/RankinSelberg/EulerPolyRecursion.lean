/-
  The Rankin–Selberg Euler polynomial: its inverse's Taylor expansion on the unit disc, and the ODE
  lemma the Euler product's analytic continuation runs on.

  * `RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one`: for
    `a b` with `‖b‖ = 1`, `a²` a nonnegative multiple of `b`, and `‖a‖² < N + 2 + N⁻¹`, there is a
    nonnegative coefficient sequence `c` with `c 0 = 0`, `c 1 = ‖a‖²`, `c m ≤ 4 N^m`, such that
    `exp (∑' m, c m y^m) = (rsEulerPoly (a/b) b⁻¹ a b 0).eval y)⁻¹` on `‖y‖ < N⁻¹` — the explicit
    reciprocal of the Euler factor, with the growth that makes the logarithm converge.
  * `eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow`: a differentiable `f` on `t > 0` with
    `f' = (α/t + β) f`, `Re β > 0`, and polynomial growth at infinity is identically zero. This is the
    uniqueness half of the Euler product's continuation (no nonzero solution decays polynomially against
    a `t^(-α)` singularity and an exponential `e^(βt)`).

  Both pins are small: the Rankin–Selberg file is 231 lines with four private engines, the ODE file 104
  with six. The row's engines are the order's transcription (see `lean/tmp/af84/WO.md` step 1).

  Heartbeat probe: the whole module is silent at 25000 and aborts at 12000 (probe run with
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N`; no in-file option — playbook §3.5, FR-0225).
  The aborting declaration is the Rankin–Selberg row (its `‖ρ⁻¹ * y‖ < 1` estimate). Nothing in the
  module needs a cap.

  `dedup.py --within` reports one shape cluster: the private `ode_main` and the public row
  `eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow`, which is **the pin's own pair** — the
  pin declares `OsOde17.main` private (`:60`) and the row `solution` (`:98`) with the identical
  statement, and FR-0221 requires the row at the row's name, so this pair stays.

  Transcribed from the two `S_` files below (pinned `aa2d8b3`).

  spec-pin: P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow.lean
-/
import FLTForHuman.LanglandsTunnell.RankinSelberg.Euler
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex
open scoped Classical NNReal

namespace LanglandsTunnell

namespace RankinSelberg

open Polynomial

theorem eval_rsEulerPoly_roots (α₁ α₂ y : ℂ) (h₁ : α₁ ≠ 0) (h₂ : α₂ ≠ 0) :
    (rsEulerPoly ((α₁ + α₂) / (α₁ * α₂)) (α₁ * α₂)⁻¹ (α₁ + α₂) (α₁ * α₂) 0).eval y =
      (1 - y) ^ 2 * (1 - α₁ / α₂ * y) * (1 - α₂ / α₁ * y) := by
  simp only [rsEulerPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp
  ring

theorem lt_of_add_inv_lt {x N : ℝ} (hx : 0 < x) (hN : 1 ≤ N) (h : x + x⁻¹ < N + N⁻¹) : x < N := by
  by_contra hcon
  push Not at hcon
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hxN : 1 ≤ x * N := by nlinarith
  have key : N + N⁻¹ ≤ x + x⁻¹ := by
    rw [← sub_nonneg]
    have : x + x⁻¹ - (N + N⁻¹) = (x - N) * (x * N - 1) / (x * N) := by
      field_simp
      ring
    rw [this]
    apply div_nonneg (mul_nonneg (sub_nonneg.2 hcon) (by linarith)) (by positivity)
  linarith

theorem real_pos_or_norm_eq_one {ρ : ℂ} (hρ : ρ ≠ 0) {s : ℝ} (hs : ρ + ρ⁻¹ = (s : ℂ)) (hs2 : -2 ≤ s) :
    (∃ r : ℝ, 0 < r ∧ ρ = (r : ℂ)) ∨ ‖ρ‖ = 1 := by
  by_cases h1 : ‖ρ‖ = 1
  · exact Or.inr h1
  left

  have hns : normSq ρ ≠ 0 := by rwa [Ne, normSq_eq_zero]
  have him : (ρ + ρ⁻¹).im = 0 := by rw [hs, ofReal_im]
  rw [add_im, inv_im] at him
  have hρim : ρ.im = 0 := by
    have hfac : ρ.im * (1 - (normSq ρ)⁻¹) = 0 := by
      have hnd : -ρ.im / normSq ρ = -(ρ.im / normSq ρ) := neg_div _ _
      rw [mul_sub, mul_one, ← div_eq_mul_inv]; linarith
    rcases mul_eq_zero.1 hfac with h | h
    · exact h
    · exfalso
      have hn1 : normSq ρ = 1 := by
        have := sub_eq_zero.1 h
        rw [eq_comm, inv_eq_one] at this
        exact this
      apply h1
      have : ‖ρ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hn1
      nlinarith [norm_nonneg ρ]

  have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hρim]
  have hre0 : ρ.re ≠ 0 := by
    intro h; apply hρ; rw [hρre, h, ofReal_zero]
  refine ⟨ρ.re, ?_, hρre⟩
  rcases lt_or_gt_of_ne hre0 with hneg | hpos
  · exfalso

    have hsr : s = ρ.re + (ρ.re)⁻¹ := by
      have := hs
      rw [hρre, ← ofReal_inv, ← ofReal_add, ofReal_inj] at this
      exact this.symm
    set r := ρ.re with hr
    have hle : r + r⁻¹ ≤ -2 := by
      have : r + r⁻¹ + 2 = (r + 1) ^ 2 / r := by field_simp; ring
      have h2 : (r + 1) ^ 2 / r ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
      linarith
    have heq : r + r⁻¹ = -2 := le_antisymm hle (by rw [← hsr]; exact hs2)
    have hr1 : r = -1 := by
      have : (r + 1) ^ 2 = 0 := by
        have h3 : (r + 1) ^ 2 = (r + r⁻¹ + 2) * r := by field_simp; ring
        rw [h3, heq]; ring
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    apply h1
    rw [hρre, hr1]
    simp
  · exact hpos

theorem exists_real_pow_add_inv_pow {ρ : ℂ} (hρ : ρ ≠ 0)
    (hcase : (∃ r : ℝ, 0 < r ∧ ρ = (r : ℂ)) ∨ ‖ρ‖ = 1) (m : ℕ) :
    ∃ u : ℝ, ρ ^ m + ρ⁻¹ ^ m = (u : ℂ) ∧ -2 ≤ u ∧ u ≤ ‖ρ‖ ^ m + ‖ρ‖⁻¹ ^ m := by
  rcases hcase with ⟨r, hr, rfl⟩ | h1
  · refine ⟨r ^ m + r⁻¹ ^ m, by push_cast; ring, ?_, ?_⟩
    · have : 0 ≤ r ^ m + r⁻¹ ^ m := by positivity
      linarith
    · have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real]; exact abs_of_pos hr
      rw [hnr]
  ·
    have hinv : ρ⁻¹ = (starRingEnd ℂ) ρ := inv_eq_conj h1
    refine ⟨2 * (ρ ^ m).re, ?_, ?_, ?_⟩
    · rw [hinv, ← map_pow, Complex.add_conj]
    · have hb : |(ρ ^ m).re| ≤ ‖ρ ^ m‖ := Complex.abs_re_le_norm _
      rw [norm_pow, h1, one_pow] at hb
      have := neg_le_of_abs_le hb
      linarith
    · have hb : |(ρ ^ m).re| ≤ ‖ρ ^ m‖ := Complex.abs_re_le_norm _
      rw [norm_pow, h1, one_pow] at hb
      have := le_of_abs_le hb
      rw [h1, inv_one, one_pow]
      linarith

theorem exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
    (a b : ℂ) (N : ℝ) (hN : 1 < N) (hb : ‖b‖ = 1) (hab : ∃ t : ℝ, 0 ≤ t ∧ a ^ 2 = (t : ℂ) * b)
    (ha : ‖a‖ ^ 2 < N + 2 + N⁻¹) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧ c 1 = ‖a‖ ^ 2 ∧ (∀ m : ℕ, 0 ≤ c m) ∧ (∀ m : ℕ, c m ≤ 4 * N ^ m) ∧
      ∀ y : ℂ, ‖y‖ < N⁻¹ →
        Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) = ((rsEulerPoly (a / b) b⁻¹ a b 0).eval y)⁻¹ := by
  obtain ⟨t, ht0, hat⟩ := hab
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hN1 : (1 : ℝ) ≤ N := hN.le
  have hN0 : (0 : ℝ) < N := by linarith

  have hat2 : ‖a‖ ^ 2 = t := by
    rw [← norm_pow, hat, norm_mul, hb, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a ^ 2 - 4 * b) (n := 2) two_pos
  set α₁ : ℂ := (a + s) / 2 with hα₁
  set α₂ : ℂ := (a - s) / 2 with hα₂
  have hsum : α₁ + α₂ = a := by rw [hα₁, hα₂]; ring
  have hprod : α₁ * α₂ = b := by
    rw [hα₁, hα₂]
    have : (a + s) / 2 * ((a - s) / 2) = (a ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have hα0 : α₁ ≠ 0 ∧ α₂ ≠ 0 := by
    rw [← not_or, ← mul_eq_zero, hprod]; exact hb0
  set ρ : ℂ := α₁ / α₂ with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hα0.1 hα0.2
  have hρinv : ρ⁻¹ = α₂ / α₁ := by rw [hρ, inv_div]

  have hρsum : ρ + ρ⁻¹ = ((t - 2 : ℝ) : ℂ) := by
    have h1 : ρ + ρ⁻¹ = ((α₁ + α₂) ^ 2 - 2 * (α₁ * α₂)) / (α₁ * α₂) := by
      rw [hρinv, hρ]; field_simp; ring
    rw [h1, hsum, hprod, hat]; push_cast; field_simp; try ring
  have hcase := real_pos_or_norm_eq_one hρ0 hρsum (by linarith)

  have hρN : ‖ρ‖ < N ∧ ‖ρ‖⁻¹ < N := by
    rcases hcase with ⟨r, hr, hrρ⟩ | h1
    · have hnr : ‖ρ‖ = r := by rw [hrρ, Complex.norm_real]; exact abs_of_pos hr
      have hrs : r + r⁻¹ = t - 2 := by
        have := hρsum; rw [hrρ, ← ofReal_inv, ← ofReal_add, ofReal_inj] at this; exact this
      have hlt : r + r⁻¹ < N + N⁻¹ := by rw [hrs, ← hat2]; linarith
      have hlt' : r⁻¹ + r⁻¹⁻¹ < N + N⁻¹ := by rw [inv_inv, add_comm]; exact hlt
      rw [hnr]
      exact ⟨lt_of_add_inv_lt hr hN1 hlt, lt_of_add_inv_lt (inv_pos.2 hr) hN1 hlt'⟩
    · rw [h1, inv_one]; exact ⟨hN, hN⟩

  choose u hu using fun m => exists_real_pow_add_inv_pow hρ0 hcase m
  refine ⟨fun m => (2 + u m) / m, by simp, ?_, ?_, ?_, ?_⟩
  ·
    have h1 := (hu 1).1
    rw [pow_one, pow_one, hρsum, ofReal_inj] at h1
    simp only [Nat.cast_one, div_one]
    rw [← h1, hat2]; ring
  · intro m
    exact div_nonneg (by linarith [(hu m).2.1]) (Nat.cast_nonneg m)
  · intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hNm : (1 : ℝ) ≤ N ^ m := one_le_pow₀ hN1
    have hb1 : ‖ρ‖ ^ m ≤ N ^ m := pow_le_pow_left₀ (norm_nonneg _) hρN.1.le m
    have hb2 : ‖ρ‖⁻¹ ^ m ≤ N ^ m := pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) hρN.2.le m
    have hum : u m ≤ 2 * N ^ m := by linarith [(hu m).2.2]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (2 + u m) / m ≤ (2 + u m) / 1 := by
          apply div_le_div_of_nonneg_left (by linarith [(hu m).2.1]) one_pos hm1
      _ ≤ 4 * N ^ m := by rw [div_one]; linarith
  · intro y hy
    have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hy (inv_le_one_of_one_le₀ hN1)
    have hρy : ‖ρ * y‖ < 1 := by
      rw [norm_mul]
      calc ‖ρ‖ * ‖y‖ ≤ N * ‖y‖ := by gcongr; exact hρN.1.le
        _ < N * N⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hN0.ne'
    have hρy' : ‖ρ⁻¹ * y‖ < 1 := by
      rw [norm_mul, norm_inv]
      calc ‖ρ‖⁻¹ * ‖y‖ ≤ N * ‖y‖ := by gcongr; exact hρN.2.le
        _ < N * N⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hN0.ne'
    have h1 := hasSum_taylorSeries_neg_log hy1
    have h2 := hasSum_taylorSeries_neg_log hρy
    have h3 := hasSum_taylorSeries_neg_log hρy'
    have hsum3 := ((h1.mul_left 2).add h2).add h3
    have hterm : ∀ n : ℕ, (((2 + u n) / n : ℝ) : ℂ) * y ^ n =
        2 * (y ^ n / n) + (ρ * y) ^ n / n + (ρ⁻¹ * y) ^ n / n := by
      intro n
      have hun := (hu n).1
      push_cast
      rw [← hun, mul_pow, mul_pow]
      ring
    have hS : HasSum (fun n : ℕ => (((2 + u n) / n : ℝ) : ℂ) * y ^ n)
        (2 * -Complex.log (1 - y) + -Complex.log (1 - ρ * y) + -Complex.log (1 - ρ⁻¹ * y)) := by
      (convert hsum3 using 1; first | rfl | (funext n; exact hterm n))
    refine ⟨hS.summable, ?_⟩
    rw [hS.tsum_eq]

    have hne : ∀ z : ℂ, ‖z‖ < 1 → (1 - z) ≠ 0 := by
      intro z hz h
      have : z = 1 := (sub_eq_zero.1 h).symm
      rw [this, norm_one] at hz; exact lt_irrefl _ hz
    have e1 : Complex.exp (2 * -Complex.log (1 - y) + -Complex.log (1 - ρ * y) + -Complex.log (1 - ρ⁻¹ * y)) =
        ((1 - y) ^ 2 * (1 - ρ * y) * (1 - ρ⁻¹ * y))⁻¹ := by
      rw [Complex.exp_add, Complex.exp_add, show (2 : ℂ) * -Complex.log (1 - y) =
        -Complex.log (1 - y) + -Complex.log (1 - y) by ring, Complex.exp_add, Complex.exp_neg, Complex.exp_neg,
        Complex.exp_neg, Complex.exp_log (hne y hy1), Complex.exp_log (hne _ hρy), Complex.exp_log (hne _ hρy')]
      field_simp
    rw [e1]
    congr 1

    have := eval_rsEulerPoly_roots α₁ α₂ y hα0.1 hα0.2
    rw [hsum, hprod] at this
    rw [this, hρinv, hρ]

end RankinSelberg

section Ode

open Real Filter Topology

private def sol (α β : ℂ) (t : ℝ) : ℂ := Complex.exp (α * (Real.log t : ℂ) + β * (t : ℂ))

private theorem hasDerivAt_sol (α β : ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (sol α β) ((α / t + β) * sol α β t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (Real.log s : ℂ)) ((t : ℂ)⁻¹) t := by
    have h := (Real.hasDerivAt_log ht).ofReal_comp
    simpa [Complex.ofReal_inv] using h
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h3 : HasDerivAt (fun s : ℝ => α * (Real.log s : ℂ) + β * (s : ℂ)) (α * (t : ℂ)⁻¹ + β * 1) t :=
    (h1.const_mul α).add (h2.const_mul β)
  have h4 := h3.cexp
  unfold sol
  convert h4 using 1
  rw [div_eq_mul_inv, mul_one, mul_comm]

private theorem sol_ne_zero (α β : ℂ) (t : ℝ) : sol α β t ≠ 0 := Complex.exp_ne_zero _

private theorem norm_sol (α β : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖sol α β t‖ = t ^ α.re * Real.exp (β.re * t) := by
  unfold sol
  rw [Complex.norm_exp, Complex.add_re, Real.exp_add, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Real.rpow_def_of_pos ht, mul_comm (Real.log t)]

private theorem exists_eq_const_mul_sol (α β : ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, 0 < t → HasDerivAt f ((α / t + β) * f t) t) :
    ∃ c : ℂ, ∀ t : ℝ, 0 < t → f t = c * sol α β t := by
  set g : ℝ → ℂ := fun t => f t / sol α β t with hg
  have hgd : ∀ t : ℝ, 0 < t → HasDerivAt g 0 t := by
    intro t ht
    have h := (hf t ht).div (hasDerivAt_sol α β ht.ne') (sol_ne_zero α β t)
    convert h using 1
    ring
  refine ⟨g 1, fun t ht => ?_⟩
  have hconst : g t = g 1 := by
    refine isOpen_Ioi.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f := g) isPreconnected_Ioi
      (fun s hs => (hgd s hs).differentiableAt.differentiableWithinAt) (fun s hs => ?_) ht
      (Set.mem_Ioi.mpr one_pos)
    rw [(hgd s hs).hasFDerivAt.fderiv]
    ext
    simp
  rw [← hconst, hg]
  field_simp [sol_ne_zero α β t]

private theorem ode_main (α β : ℂ) (hβ : 0 < β.re) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + β) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 := by
  have hf' : ∀ t : ℝ, 0 < t → HasDerivAt f ((α / t + β) * f t) t := by
    intro t ht
    rw [← hfeq t ht]
    exact (hf.differentiableAt (Ioi_mem_nhds ht)).hasDerivAt
  obtain ⟨c, hc⟩ := exists_eq_const_mul_sol α β f hf'
  suffices hc0 : c = 0 by intro t ht; rw [hc t ht, hc0, zero_mul]
  by_contra hc0
  have hlim : Tendsto (fun x : ℝ => Real.exp (β.re * x) / x ^ ((N : ℝ) - α.re)) atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop ((N : ℝ) - α.re) β.re hβ
  have hev := (hlim.eventually (eventually_gt_atTop (C / ‖c‖))).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x, hx, hx1⟩ := hev.exists
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hb := hgrowth x hx1
  rw [hc x hxpos, norm_mul, norm_sol α β hxpos, ← Real.rpow_natCast] at hb
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hxr : 0 < x ^ ((N : ℝ) - α.re) := Real.rpow_pos_of_pos hxpos _
  have hxa : 0 < x ^ α.re := Real.rpow_pos_of_pos hxpos _
  have h1 : C * x ^ ((N : ℝ) - α.re) < ‖c‖ * Real.exp (β.re * x) := by
    have h := (lt_div_iff₀ hxr).mp hx
    rw [div_mul_eq_mul_div, div_lt_iff₀ hcpos] at h
    linarith [mul_comm (Real.exp (β.re * x)) ‖c‖]
  have h2 : C * x ^ (N : ℝ) < ‖c‖ * (x ^ α.re * Real.exp (β.re * x)) := by
    have h3 := mul_lt_mul_of_pos_right h1 hxa
    have hsplit : x ^ (N : ℝ) = x ^ ((N : ℝ) - α.re) * x ^ α.re := by
      rw [← Real.rpow_add hxpos]; ring_nf
    rw [hsplit]
    nlinarith [h3]
  linarith

end Ode

theorem eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
    (α β : ℂ) (hβ : 0 < β.re) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + β) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 :=
  ode_main α β hβ f hf hfeq C N hgrowth

end LanglandsTunnell
