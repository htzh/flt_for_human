/-
  Consumer zone for `FLTForHuman/LanglandsTunnell/WhittakerODEGrowth.lean`.

  A `spec/` probe, not a library module: it *consumes* the headline (the near-zero growth bound for
  a solution of the forced Whittaker equation) in composition, never by `#check`.

  * **Zone 1 — the pure indicial exponent.** The headline's `σ`-slot is the growth exponent of the
    *forcing*; with no forcing (`h = 0`) it is free, and putting it at the indicial gain
    `1/2 − |Re ν|` makes the `min` collapse. What comes out is the pin's own conclusion without the
    forcing bookkeeping: every solution of the homogeneous Whittaker equation on `(0, 1]` grows like
    `y ^ (1/2 − |Re ν| − ε)`. This is the form the cusp analysis of the weight-one lifting consumes.

  * **Zone 2 — the estimate is a seminorm on solutions.** The operator is linear in `f` and in `h`,
    so the *difference* of two solutions solves the equation with forcing `h₁ − h₂`; bounding that by
    `(A₁ + A₂) · y ^ σ` (triangle inequality), the headline applies a second time. The estimate is
    therefore stable under subtraction — the property that lets a local functional be pinned by
    comparing two of its solutions rather than by bounding either one alone.

  * **Zone 3 — the two indicial roots.** The equation depends on `ν` only through `ν ^ 2`, so a
    solution at `ν` is one at `−ν`, and the exponent `min (1/2 − |Re ν|) σ − ε` only sees `|Re ν|`:
    the bound is the same at either root `1/2 ± ν`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF36BConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.WhittakerODEGrowth

set_option autoImplicit false

open scoped Real Topology

open Filter

noncomputable section

namespace LanglandsTunnellSetAF36BConsumer

open LanglandsTunnell

/-- The Whittaker operator of the headline, read as a function of `f`: the left-hand side of the
equation in `norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing`. -/
def W (ν : ℂ) (k : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ 2 * deriv (deriv f) y
    + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y

/-- **Zone 1.** With no forcing the solution grows at exactly the indicial gain: `σ` in the headline
is the forcing's exponent, and setting it to `1/2 − |Re ν|` collapses the `min`. -/
theorem norm_le_mul_rpow_homogeneous (ν : ℂ) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y → W ν k f y = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (1 / 2 - |ν.re| - ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ :=
    norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing ν k (1 / 2 - |ν.re|) 0 f 0 hf hf'
      (fun y _ _ => by simp) (fun y hy => by simpa [W] using hode y hy) ε hε
  exact ⟨C, fun y hy hy1 => by simpa [min_self] using hC y hy hy1⟩

/-- The equation depends on the spectral parameter through `ν ^ 2` only. -/
theorem W_neg (ν : ℂ) (k : ℝ) (f : ℝ → ℂ) (y : ℝ) : W (-ν) k f y = W ν k f y := by
  unfold W
  rw [neg_sq]

/-- The operator is linear in its argument: the difference of two solutions solves the equation
with the difference of the two forcings. -/
theorem W_sub {ν : ℂ} {k : ℝ} {f₁ f₂ h₁ h₂ : ℝ → ℂ}
    (hf₁ : DifferentiableOn ℝ f₁ (Set.Ioi 0)) (hf₂ : DifferentiableOn ℝ f₂ (Set.Ioi 0))
    (hf₁' : DifferentiableOn ℝ (deriv f₁) (Set.Ioi 0))
    (hf₂' : DifferentiableOn ℝ (deriv f₂) (Set.Ioi 0))
    (hode₁ : ∀ y : ℝ, 0 < y → W ν k f₁ y = h₁ y)
    (hode₂ : ∀ y : ℝ, 0 < y → W ν k f₂ y = h₂ y) :
    ∀ y : ℝ, 0 < y → W ν k (f₁ - f₂) y = (h₁ - h₂) y := by
  intro y hy
  have hd : (fun x : ℝ => deriv f₁ x - deriv f₂ x) =ᶠ[𝓝 y] deriv (f₁ - f₂) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact (deriv_sub (hf₁.differentiableAt (Ioi_mem_nhds hx))
      (hf₂.differentiableAt (Ioi_mem_nhds hx))).symm
  have h2 : HasDerivAt (fun x : ℝ => deriv f₁ x - deriv f₂ x)
      (deriv (deriv f₁) y - deriv (deriv f₂) y) y :=
    ((hf₁'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt).sub
      ((hf₂'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt)
  have hderiv : deriv (deriv (f₁ - f₂)) y = deriv (deriv f₁) y - deriv (deriv f₂) y :=
    (h2.congr_of_eventuallyEq hd.symm).deriv
  have h1 := hode₁ y hy
  have h2' := hode₂ y hy
  unfold W at h1 h2' ⊢
  rw [hderiv]
  simp only [Pi.sub_apply]
  linear_combination h1 - h2'

/-- **Zone 2.** The growth bound is a seminorm on solutions: the difference of two solutions, whose
forcings are bounded by `A₁ · y ^ σ` and `A₂ · y ^ σ`, obeys the same exponent with the forcing
constant `A₁ + A₂` — the headline spent twice, once on each solution. -/
theorem norm_le_mul_rpow_sub_of_two_solutions (ν : ℂ) (k σ A₁ A₂ : ℝ) (f₁ f₂ h₁ h₂ : ℝ → ℂ)
    (hf₁ : DifferentiableOn ℝ f₁ (Set.Ioi 0)) (hf₁' : DifferentiableOn ℝ (deriv f₁) (Set.Ioi 0))
    (hf₂ : DifferentiableOn ℝ f₂ (Set.Ioi 0)) (hf₂' : DifferentiableOn ℝ (deriv f₂) (Set.Ioi 0))
    (hh₁ : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h₁ y‖ ≤ A₁ * y ^ σ)
    (hh₂ : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h₂ y‖ ≤ A₂ * y ^ σ)
    (hode₁ : ∀ y : ℝ, 0 < y → W ν k f₁ y = h₁ y)
    (hode₂ : ∀ y : ℝ, 0 < y → W ν k f₂ y = h₂ y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(f₁ - f₂) y‖ ≤ C * y ^ (min (1 / 2 - |ν.re|) σ - ε) := by
  have hsub : DifferentiableOn ℝ (deriv (f₁ - f₂)) (Set.Ioi 0) := by
    intro x hx
    have hd : (fun z : ℝ => deriv f₁ z - deriv f₂ z) =ᶠ[𝓝 x] deriv (f₁ - f₂) := by
      filter_upwards [Ioi_mem_nhds hx] with z hz
      exact (deriv_sub (hf₁.differentiableAt (Ioi_mem_nhds hz))
        (hf₂.differentiableAt (Ioi_mem_nhds hz))).symm
    exact (hd.differentiableAt_iff.mp
      ((hf₁'.differentiableAt (Ioi_mem_nhds hx)).sub
        (hf₂'.differentiableAt (Ioi_mem_nhds hx)))).differentiableWithinAt
  have hhsub : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖(h₁ - h₂) y‖ ≤ (A₁ + A₂) * y ^ σ := by
    intro y hy hy1
    have hy0 : (0 : ℝ) ≤ y ^ σ := Real.rpow_nonneg hy.le σ
    have h1 := hh₁ y hy hy1
    have h2 := hh₂ y hy hy1
    have hsplit : (A₁ + A₂) * y ^ σ = A₁ * y ^ σ + A₂ * y ^ σ := by ring
    calc ‖(h₁ - h₂) y‖ = ‖h₁ y - h₂ y‖ := by rw [Pi.sub_apply]
      _ ≤ ‖h₁ y‖ + ‖h₂ y‖ := norm_sub_le _ _
      _ ≤ A₁ * y ^ σ + A₂ * y ^ σ := add_le_add h1 h2
      _ = (A₁ + A₂) * y ^ σ := hsplit.symm
  exact norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing ν k σ (A₁ + A₂) (f₁ - f₂) (h₁ - h₂)
    (hf₁.sub hf₂) hsub hhsub (W_sub hf₁ hf₂ hf₁' hf₂' hode₁ hode₂)

/-- **Zone 3.** The exponent does not distinguish the two indicial roots `1/2 ± ν`: a solution at
`ν` is one at `−ν`, and `|(-ν).re| = |ν.re|`, so the same bound holds at either root. -/
theorem norm_le_mul_rpow_neg_of_whittaker_ode_of_forcing (ν : ℂ) (k σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → W ν k f y = h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min (1 / 2 - |ν.re|) σ - ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ :=
    norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing (-ν) k σ A f h hf hf' hh
      (fun y hy => by
        have h := hfeq y hy
        rw [← W_neg] at h
        simpa [W] using h) ε hε
  exact ⟨C, fun y hy hy1 => by simpa [Complex.neg_re] using hC y hy hy1⟩

end LanglandsTunnellSetAF36BConsumer
