/-
  Consumer zone for `FLTForHuman/LanglandsTunnell/ODENearZeroBounds.lean` (order AF41B).

  A `spec/` probe, not a library module: it *consumes* the three headlines in composition, never by
  `#check`.

  The three headlines are the near-zero growth bounds for the three linear ODEs of the local
  Whittaker analysis, each saying that on `(0, 1]` a solution whose forcing is bounded by a power of
  `y` is bounded by a power of `y`, with the exponent the indicial data forces, up to an `ε`:

  * **B1** `norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing` for `y f' = b f + h`:
    `‖f y‖ ≤ C · y ^ (min (Re b) σ - ε)`.
  * **B2** `norm_le_mul_rpow_near_zero_of_first_order_system_of_diag` for the `m`-dimensional system
    `y F' = A F + B F` with `Re a i ≥ r₀`: `‖F i y‖ ≤ C · y ^ (r₀ - ε)`.
  * **B3** `norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori`: a conjunction, the
    two-term expression `y f' - (1/2 - ν) f` bounded by `C · y ^ (min (min (1/2 + Re ν) σ) (r + 2) - ε)`
    for every `ε > 0`, and — when `1/2 - Re ν < r` — both `f` and `y f'` bounded by
    `C · y ^ (min (1/2 + Re ν) σ - ε)`.

  The three zones below read one headline each, at data where the exponent is computable:

  * **Zone 1** feeds B1 the constant solution `f ≡ 1` of `y f' = b f - b` with `Re b ≤ 0`: the
    integrability `‖-b‖ ≤ 1 · y ^ (Re b)` holds on `(0, 1]` because a nonpositive exponent makes
    `y ^ (Re b) ≥ 1` there, and the conclusion's exponent `min (Re b) (Re b) - ε` collapses by
    `min_self` to the indicial exponent `Re b - ε`.

  * **Zone 2** feeds B2 the scalar case `m = 1`, `B = 0`, `a 0 = (r₀ : ℂ)`, at `r₀ = 1` and at the
    linear solution `F y = y` of `y F' = 1 · F`. The system bound `C · y ^ (r₀ - ε)` is exactly B1's
    `C · y ^ (min (Re b) σ - ε)` at `b = (r₀ : ℂ)`, `σ = r₀` — again by `min_self` on the real part —
    so the scalar system recovers the first-order Euler bound for the constant coefficient.

  * **Zone 3** feeds B3's bootstrap pieces at the a-priori exponent `ρ = r`: `Gap41.round` at `ρ = r`
    and `Gap41.twoTermAp` at `ρ = r` are the two halves of the same step, and both read off the
    improved exponent `min (min (1/2 + Re ν) σ) (r + 2) - ε` — the exponent of `r + 2` in place of the
    a-priori `r`, which is the pin's `k ↦ k + 1` step of the induction.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF41BConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.ODENearZeroBounds
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

open scoped Real

noncomputable section

namespace LanglandsTunnellSetAF41BConsumer

/-! ### Zone 1: the constant solution of the first-order Euler equation -/

section euler

/-- The constant solution `f ≡ 1` of `y f' = b f + h` has `h ≡ -b`, so with `Re b ≤ 0` the forcing
bound `‖h y‖ ≤ ‖b‖ · y ^ (Re b)` holds on `(0, 1]` (`y ^ (Re b) ≥ 1` there). B1 then bounds the
solution by `C · y ^ (min (Re b) (Re b) - ε)`, and `min_self` collapses the exponent to `Re b - ε`. -/
theorem euler_const_solution (b : ℂ) (hb : b.re ≤ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(fun _ : ℝ => (1 : ℂ)) y‖ ≤ C * y ^ (b.re - ε) := by
  have hf : DifferentiableOn ℝ (fun _ : ℝ => (1 : ℂ)) (Set.Ioi 0) := differentiableOn_const 1
  have hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖(fun _ : ℝ => -b) y‖ ≤ ‖b‖ * y ^ b.re := by
    intro y hy hy1
    have h1 : (1 : ℝ) ≤ y ^ b.re := by
      rw [← Real.rpow_zero y]
      exact Real.rpow_le_rpow_of_exponent_ge hy hy1 hb
    have h2 : ‖b‖ ≤ ‖b‖ * y ^ b.re := by
      simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg b)
    simpa using h2
  have hfeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) * deriv (fun _ : ℝ => (1 : ℂ)) y = b * (fun _ : ℝ => (1 : ℂ)) y + (fun _ : ℝ => -b) y := by
    intro y _
    simp [deriv_const]
  have h := LanglandsTunnell.OdeCAux.main b b.re ‖b‖ (fun _ : ℝ => (1 : ℂ)) (fun _ : ℝ => -b)
    hf hh hfeq ε hε
  simpa only [min_self] using h

end euler

/-! ### Zone 2: the scalar case of the diagonal system -/

section system

/-- The scalar case `m = 1`, `B = 0`, `a 0 = (r₀ : ℂ)` at `r₀ = 1`, at the linear solution
`F y = y` of `y F' = 1 · F`. The system bound `C · y ^ (r₀ - ε)` is written in B1's form
`C · y ^ (min (Re b) σ - ε)` at `b = (r₀ : ℂ)`, `σ = r₀`, the two agreeing by `min_self` on the real
part: the diagonal system with a constant scalar coefficient recovers the first-order Euler bound. -/
theorem system_scalar_linear (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i : Fin 1,
      ‖(fun (_ : Fin 1) (y : ℝ) => (y : ℂ)) i y‖ ≤ C * y ^ (min ((1 : ℂ)).re 1 - ε) := by
  have hre : ((1 : ℂ)).re = 1 := by norm_num
  have hderiv : ∀ y : ℝ, deriv (fun y : ℝ => (y : ℂ)) y = 1 :=
    fun y => (Complex.ofRealCLM.hasDerivAt (x := y)).deriv
  have hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j : Fin 1,
      ‖(fun _ _ _ => (0 : ℂ)) y i j‖ ≤ (0 : ℝ) * y ^ (1 : ℝ) := by
    intro y _ _ i j
    simp
  have hF : ∀ i : Fin 1, DifferentiableOn ℝ (fun y : ℝ => (y : ℂ)) (Set.Ioi 0) :=
    fun _ => Complex.ofRealCLM.differentiable.differentiableOn
  have hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i : Fin 1,
      (y : ℂ) * deriv (fun y : ℝ => (y : ℂ)) y
        = (1 : ℂ) * (fun y : ℝ => (y : ℂ)) y
          + ∑ j, (fun _ _ _ => (0 : ℂ)) y i j * (fun (_ : Fin 1) (y : ℝ) => (y : ℂ)) j y := by
    intro y _ _ i
    simp [hderiv y]
  have h := LanglandsTunnell.OdeEAux.main 1 (fun _ : Fin 1 => (1 : ℂ)) 1 0 1 (by norm_num)
    (fun _ => le_refl 1) (fun _ _ _ => (0 : ℂ)) hB (fun _ y => (y : ℂ)) hF hFeq ε hε
  simpa only [hre, min_self] using h

end system

/-! ### Zone 3: one bootstrap step of the Bessel analysis, at the a-priori exponent `ρ = r` -/

section bessel

/-- **Zone 3.** Feeding the a-priori bound `‖f y‖ ≤ B · y ^ r` to both halves of one bootstrap step
at `ρ = r` — `Gap41.round` (for `f` itself) and `Gap41.twoTermAp` (for `y f' - (1/2 - ν) f`) — reads
off the improved exponent `min (min (1/2 + Re ν) σ) (r + 2) - ε`: the a-priori `r` has become
`r + 2`, which is the pin's induction step in its `min M (r + 2 k)` sequence. -/
theorem bessel_one_step (ν : ℂ) (σ A r B : ℝ) (hr : 1 / 2 - ν.re < r) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (r + 2) - ε) ∧
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (r + 2) - ε) := by
  obtain ⟨C₁, hC₁⟩ :=
    LanglandsTunnell.Gap41.round ν σ A r B r B hr f h hf hf' hh hapriori hapriori hfeq ε hε
  obtain ⟨C₂, hC₂⟩ :=
    LanglandsTunnell.Gap41.twoTermAp ν σ A r B f h hf hf' hh hapriori hfeq ε hε
  refine ⟨max C₁ C₂, fun y hy hy1 => ⟨?_, ?_⟩⟩
  · exact (hC₁ y hy hy1).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (Real.rpow_nonneg hy.le _))
  · exact (hC₂ y hy hy1).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (Real.rpow_nonneg hy.le _))

end bessel

end LanglandsTunnellSetAF41BConsumer
