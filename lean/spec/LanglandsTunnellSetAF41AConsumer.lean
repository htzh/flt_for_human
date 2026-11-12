/-
  Consumer zone for `FLTForHuman/LanglandsTunnell/WhittakerODENearZero.lean` (order AF41A).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`.

  The headlines are the two local growth bounds for a solution of the unforced Whittaker equation
  `y ^ 2 f'' + (1 / 4 - ν ^ 2 + 2 π k y - 4 π ^ 2 y ^ 2) f = 0` at the cusp `y = 0`:

  * **A1** `norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` is a conjunction: on `(0, 1]`
    the solution obeys `‖f y‖ ≤ C · y ^ (1/2 - |Re ν|)` when `ν ≠ 0` (the sharp indicial exponent), and
    for **every** `ε > 0` it obeys `‖f y‖ ≤ C · y ^ (1/2 - |Re ν| - ε)`.

  * **A2** `exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half` is the existential form:
    for `|Re ν| < 1/2` there are `δ > 0` and `C` with `‖f y‖ ≤ C · y ^ δ` on `(0, 1]`.

  The two zones below read them at the same spectral data, `Re ν = 1/4` and `k = 0`:

  * **Zone 1** is A1's second conjunct at `ε = 1/5`. At `Re ν = 1/4` the exponent is
    `1/2 - 1/4 - 1/5 = 1/20`, so a solution of the equation at `ν = 1/4`, `k = 0` is bounded by
    `C · y ^ (1/20)` on `(0, 1]`. Zone 1b is the same reading at `ε = 1/10`, whose exponent is
    `3/20` — the two `ε`s differ, so the two exponents differ, and both are recorded.

  * **Zone 2** applies A2 at `ν = 1/4` (`|1/4| < 1/2`) to the same data, getting some `δ₂ > 0`, and
    then compares the two exponents. On `(0, 1]` a bound with exponent `β` implies one with every
    `β' ≤ β` (the `rpow` is monotone *decreasing* in the exponent there), so the two bounds are
    simultaneous exactly up to `max δ₂ (1/20)`: the exponent `max δ₂ (1/20)` dominates both `δ₂` and
    the `1/20` of Zone 1, and a single constant `max C₁ C₂` carries the bound at it.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF41AConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.WhittakerODENearZero

set_option autoImplicit false

open scoped Real

noncomputable section

namespace LanglandsTunnellSetAF41AConsumer

section quarter

variable (ν : ℂ) (k : ℝ) (f : ℝ → ℂ)
variable (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)

/-- The real part of the spectral parameter `ν = 1/4` — the number both zones read off. -/
private lemma re_quarter : ((1 / 4 : ℂ)).re = 1 / 4 := by norm_num

include hf hf' hfeq in
/-- **Zone 1.** A1's `ε`-conjunct at `ν = 1/4`, `k = 0`, `ε = 1/5`: the exponent
`1/2 - |Re ν| - ε` is `1/2 - 1/4 - 1/5 = 1/20`, so `‖f y‖ ≤ C · y ^ (1/20)` on `(0, 1]`. -/
theorem quarter_eps_one_fifth (hν : ν = 1 / 4) (hk : k = 0) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 / 20 : ℝ) := by
  subst hν
  subst hk
  obtain ⟨C, hC⟩ :=
    (LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
        (1 / 4) 0 f hf hf' hfeq).2
      (1 / 5) (by norm_num)
  refine ⟨C, fun y hy hy1 => ?_⟩
  have h := hC y hy hy1
  rw [re_quarter] at h
  have hexp : (1 : ℝ) / 2 - |1 / 4| - 1 / 5 = 1 / 20 := by norm_num
  rwa [hexp] at h

include hf hf' hfeq in
/-- **Zone 1b.** The same reading at `ε = 1/10`: the exponent is `1/2 - 1/4 - 1/10 = 3/20`. -/
theorem quarter_eps_one_tenth (hν : ν = 1 / 4) (hk : k = 0) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (3 / 20 : ℝ) := by
  subst hν
  subst hk
  obtain ⟨C, hC⟩ :=
    (LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
        (1 / 4) 0 f hf hf' hfeq).2
      (1 / 10) (by norm_num)
  refine ⟨C, fun y hy hy1 => ?_⟩
  have h := hC y hy hy1
  rw [re_quarter] at h
  have hexp : (1 : ℝ) / 2 - |1 / 4| - 1 / 10 = 3 / 20 := by norm_num
  rwa [hexp] at h

include hf hf' hfeq in
/-- **Zone 2.** A2 at `ν = 1/4` supplies a `δ₂ > 0` together with its own constant. Zone 1 supplies
the exponent `1/20`. Since a bound at exponent `β` gives one at every `β' ≤ β` on `(0, 1]`, the two
are simultaneous up to `max δ₂ (1/20)`, which dominates both exponents. -/
theorem quarter_combined (hν : ν = 1 / 4) (hk : k = 0) :
    ∃ δ : ℝ, 0 < δ ∧ 1 / 20 ≤ δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by
  have hre : |ν.re| < 1 / 2 := by
    rw [hν, re_quarter]
    norm_num
  obtain ⟨δ₂, hδ₂, C₂, hC₂⟩ :=
    LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half ν hre k f hf hf' hfeq
  obtain ⟨C₁, hC₁⟩ := quarter_eps_one_fifth ν k f hf hf' hfeq hν hk
  refine ⟨max δ₂ (1 / 20), lt_of_lt_of_le hδ₂ (le_max_left _ _), le_max_right _ _, max C₁ C₂,
    fun y hy hy1 => ?_⟩
  rcases le_total δ₂ (1 / 20) with hle | hle
  · rw [max_eq_right hle]
    exact (hC₁ y hy hy1).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (Real.rpow_nonneg hy.le _))
  · rw [max_eq_left hle]
    exact (hC₂ y hy hy1).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (Real.rpow_nonneg hy.le _))

end quarter

end LanglandsTunnellSetAF41AConsumer
