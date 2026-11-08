/-
  Consumer zone for `FLTForHuman/LanglandsTunnell/WhittakerODELinearDependence.lean`.

  A `spec/` probe, not a library module: it *consumes* both headlines (the general
  complex-parameter dependence theorem and its `(ν ^ 2).im = 0` companion) in composition,
  never by `#check`.

  * **Zone 1 — what the conclusion actually says.** Both headlines end with
  `∃ c₁ c₂, (c₁, c₂) ≠ 0 ∧ ∀ y, 0 < y → c₁ * f y + c₂ * g y = 0`. That is `LinearDependentOnIoi`
  below. Its content is the classical one: if the two solutions do not both vanish at some
  `y₀ > 0`, the relation cannot degenerate, so `f` is a *nonzero scalar multiple* of `g` on the
  whole half-line. This is the one-dimensionality of the moderate-growth solution space that the
  weight-one lifting needs; without it `∃ c₁ c₂` would be compatible with `f = g = 0` only.

  * **Zone 2 — the general headline, instantiated.** `exists_scalar_multiple_of_whittaker_ode_complexParam`
  is Zone 1 composed with the general headline: the dependence pair the theorem produces is
  normalised to a genuine `f = λ * g`, `λ ≠ 0`.

  * **Zone 3 — the two headlines agree at `(ν ^ 2).im = 0`.** The companion's conclusion is
  *derived*, not transcribed: its extra hypothesis `hν : (ν ^ 2).im = 0` is never used. Formally,
  `depends_of_moderateGrowth_via_complexParam` reaches the companion's exact conclusion through
  the general headline (so `hν` is redundant), and `exists_scalar_multiple_of_whittaker_ode` reaches
  the same normalised form through the companion. The two routes therefore conclude the same thing
  on the same data, which is what "the companion is the special case" means here.

  * **Zone 4 — the hypotheses are satisfiable.** At `ν = 1 / 2`, `k = 0` the equation reads
  `y ^ 2 * w'' - 4 * π ^ 2 * y ^ 2 * w = 0`, i.e. `w'' = 4 * π ^ 2 * w` on `y > 0`, with solutions
  `y ↦ exp (2 * π * y)` and `y ↦ exp (-(2 * π * y))`; neither has moderate growth (an exponential
  beats every `C * y ^ N`), so the instance available in this file is the zero solution, which does
  satisfy all eight hypotheses. That makes the headlines non-vacuous as *statements* — their
  hypotheses are inhabited — and it is the reason the substantive content sits in Zone 1's
  normalisation rather than in an explicit nonzero pair.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF36AConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.WhittakerODELinearDependence

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped Real NNReal

open LanglandsTunnell

namespace LanglandsTunnellSetAF36AConsumer

/-- The conclusion shared by both headlines: `f` and `g` are linearly dependent on `y > 0`. -/
def LinearDependentOnIoi (f g : ℝ → ℂ) : Prop :=
  ∃ c₁ c₂ : ℂ, (c₁, c₂) ≠ 0 ∧ ∀ y : ℝ, 0 < y → c₁ * f y + c₂ * g y = 0

/-- **Zone 1.** A dependence relation that is nondegenerate at one point `y₀ > 0` (neither
function vanishes there) forces `f = λ * g` with `λ ≠ 0`: the relation `c₁ f + c₂ g = 0` has both
`c₁ ≠ 0` (else `c₂ g y₀ = 0`) and `c₂ ≠ 0` (else `c₁ f y₀ = 0`). -/
theorem eq_smul_of_linearDependentOnIoi_of_ne_zero {f g : ℝ → ℂ} (h : LinearDependentOnIoi f g)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hf₀ : f y₀ ≠ 0) (hg₀ : g y₀ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ y : ℝ, 0 < y → f y = c * g y := by
  obtain ⟨c₁, c₂, hne, hzero⟩ := h
  have h1 : c₁ * f y₀ + c₂ * g y₀ = 0 := hzero y₀ hy₀
  have hc₁ : c₁ ≠ 0 := by
    intro hc
    rw [hc, zero_mul, zero_add] at h1
    exact hne (by simp [(mul_eq_zero.1 h1).resolve_right hg₀, hc])
  have hc₂ : c₂ ≠ 0 := by
    intro hc
    rw [hc, zero_mul, add_zero] at h1
    exact hf₀ ((mul_eq_zero.1 h1).resolve_left hc₁)
  refine ⟨-(c₂ / c₁), ?_, ?_⟩
  · simpa using neg_ne_zero.2 (div_ne_zero hc₂ hc₁)
  · intro y hy
    have h := hzero y hy
    have key : c₁ * f y = -(c₂ * g y) := by linear_combination h
    field_simp
    linear_combination key

/-- **Zone 2.** The general headline, composed with Zone 1: two complex-parameter Whittaker
solutions of moderate growth that are both nonzero at one point are nonzero scalar multiples of
each other on `y > 0`. -/
theorem exists_scalar_multiple_of_whittaker_ode_complexParam (ν : ℂ)
    (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hf₀ : f y₀ ≠ 0) (hg₀ : g y₀ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ y : ℝ, 0 < y → f y = c * g y :=
  eq_smul_of_linearDependentOnIoi_of_ne_zero
    (linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ν k f g
      hf hf' hfeq hfgr hg hg' hgeq hggr) hy₀ hf₀ hg₀

/-- **Zone 3a.** The companion's conclusion is reached through the *general* headline on the very
same data — `hν : (ν ^ 2).im = 0` is carried but never used. This is the formal content of "the
`(ν ^ 2).im = 0` statement is the special case of the complex-parameter one". -/
theorem depends_of_moderateGrowth_via_complexParam (ν : ℂ)
    (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N) :
    LinearDependentOnIoi f g :=
  linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ν k f g
    hf hf' hfeq hfgr hg hg' hgeq hggr

/-- **Zone 3b.** The same normalised conclusion through the derived companion. Together with Zone 3a
this is the agreement of the two headlines at `(ν ^ 2).im = 0`: the same data give the same
`λ`. -/
theorem exists_scalar_multiple_of_whittaker_ode (ν : ℂ)
    (hν : (ν ^ 2).im = 0) (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hf₀ : f y₀ ≠ 0) (hg₀ : g y₀ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ y : ℝ, 0 < y → f y = c * g y :=
  eq_smul_of_linearDependentOnIoi_of_ne_zero
    (linearDependent_of_whittaker_ode_of_moderateGrowth ν hν k f g
      hf hf' hfeq hfgr hg hg' hgeq hggr) hy₀ hf₀ hg₀

/-- **Zone 4.** At `ν = 1 / 2`, `k = 0` the equation is `y ^ 2 * w'' - 4 * π ^ 2 * y ^ 2 * w = 0`,
and the zero solution satisfies all of its hypotheses: `deriv 0 = 0` twice, and the growth bound
holds with `C = 1`, `N = 0`. So the general headline applies, and its conclusion is inhabited. -/
theorem zero_solution_dependent (k : ℝ) :
    LinearDependentOnIoi (fun _ : ℝ => (0 : ℂ)) (fun _ : ℝ => (0 : ℂ)) := by
  have hz : deriv (fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => (0 : ℂ) := by
    funext z
    simp
  have hdiff : DifferentiableOn ℝ (deriv (fun _ : ℝ => (0 : ℂ))) (Set.Ioi 0) := by
    rw [hz]
    exact (differentiable_const (0 : ℂ)).differentiableOn
  have hzero : DifferentiableOn ℝ (fun _ : ℝ => (0 : ℂ)) (Set.Ioi 0) :=
    (differentiable_const (0 : ℂ)).differentiableOn
  have heq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv (fun _ : ℝ => (0 : ℂ))) y
          + (1 / 4 - (1 / 2 : ℂ) ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ)
              - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * (fun _ : ℝ => (0 : ℂ)) y = 0 := by
    intro y hy
    simp
  have hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖(fun _ : ℝ => (0 : ℂ)) y‖ ≤ C * y ^ N :=
    ⟨1, 0, by intro y hy; simp⟩
  exact linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam (1 / 2) k _ _
    hzero hdiff heq hgr hzero hdiff heq hgr

end LanglandsTunnellSetAF36AConsumer
