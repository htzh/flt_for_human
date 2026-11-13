/-
  SET-AF59B consumer: the tower's near-zero `rpow` bound, spent.

  **The row.** `FLTForHuman/LanglandsTunnell/WhittakerODETowerBound.lean` (row Q):
  `LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth`.
  A solution `f` of the Whittaker ODE of spectral data `(k, ν)` that grows at most polynomially at
  infinity satisfies `‖f y‖ ≤ C * y ^ δ` near `0`, for some exponent `δ > 0`.

  **The readings.**  The row is read on the tower's own solution `TowerBound.F n m` — the twisted
  Laguerre solution built by the module — so the ODE hypothesis is not a hypothesis here but the
  module's `ode_F`, and the growth hypothesis is its `norm_F_le_at_infinity`:

  * Zone B1 — the *executed composition*.  Every hypothesis of the headline is discharged from the
    row's own prelude (`differentiableOn_F`, `differentiableOn_deriv_F`, `ode_F`,
    `norm_F_le_at_infinity`) and the conclusion is returned with a nonnegative constant.  The
    nonnegativity is itself read off the bound (at `y = 1/2`), not assumed: the headline only
    produces *some* `C : ℝ`, and the sign is what makes the bound usable.
  * Zone B2 — the *boundedness near zero*.  The exponent's positivity `δ > 0` is spent here: on
    `(0, 1]` one has `y ^ δ ≤ 1`, so the row's bound collapses to a uniform bound.  This is the
    reading the local theory needs — the solution is bounded at the cusp, with no constant
    depending on `y`.
  * Zone B3 — the *concrete tower index*.  The bound is executed at `n = m = 0`, where the tower's
    solution is the elementary `P = 1`, `s 0 = 1/2`.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.LanglandsTunnell.WhittakerODETowerBound

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped Real NNReal

namespace LanglandsTunnell.SetAF59BConsumer

/-- **Zone B1, the executed composition.**  The headline is applied to the tower's own solution
`F n m`, with `k = n + 1 + 2m` and `ν = n/2`: the ODE is `ode_F`, the growth hypothesis is
`norm_F_le_at_infinity`, and the differentiability hypotheses are `differentiableOn_F` and
`differentiableOn_deriv_F`.  The returned constant is nonnegative. -/
theorem consumer_bound_at_tower_index (n m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, 0 < y → y ≤ 1 → ‖TowerBound.F n m y‖ ≤ C * y ^ δ := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
      n m ((n + 1 + 2 * m : ℕ) : ℝ) ((n : ℂ) / 2) (by push_cast; ring) rfl (TowerBound.F n m)
      (TowerBound.differentiableOn_F n m) (TowerBound.differentiableOn_deriv_F n m)
      (fun y hy => TowerBound.ode_F n m _ _ (by push_cast; ring) rfl hy)
      ⟨TowerBound.A n m, TowerBound.s n + (TowerBound.P n m).natDegree,
        fun y hy => TowerBound.norm_F_le_at_infinity n m hy⟩
  have hhalf := hC (1 / 2) (by norm_num) (by norm_num)
  have hpos : 0 < (1 / 2 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
  exact ⟨δ, hδ, C, (mul_nonneg_iff_of_pos_right hpos).mp (le_trans (norm_nonneg _) hhalf), hC⟩

/-- **Zone B2, the boundedness near zero.**  Positivity of the exponent is what the bound buys: on
`(0, 1]` the factor `y ^ δ` is at most `1`, so the solution is uniformly bounded at the cusp. -/
theorem consumer_bounded_near_zero (n m : ℕ) :
    ∃ M : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖TowerBound.F n m y‖ ≤ M := by
  obtain ⟨δ, hδ, C, hC0, hC⟩ := consumer_bound_at_tower_index n m
  refine ⟨C, fun y hy hy1 => ?_⟩
  have hY : y ^ δ ≤ 1 := Real.rpow_le_one hy.le hy1 hδ.le
  calc ‖TowerBound.F n m y‖ ≤ C * y ^ δ := hC y hy hy1
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hY hC0
    _ = C := by ring

/-- **Zone B3, the concrete tower index.**  At `n = m = 0` the tower's solution is bounded at the
cusp, with no constant depending on `y`. -/
theorem consumer_concrete_index :
    ∃ M : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖TowerBound.F 0 0 y‖ ≤ M :=
  consumer_bounded_near_zero 0 0

end LanglandsTunnell.SetAF59BConsumer
