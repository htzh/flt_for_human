/-
An honest line integral of a 1-form along a path on a complex 1-dimensional charted space, and the
primitive-difference theorem for it.

  **Reserve.** Kept out of the critical-path port, and this is a *holding* decision rather than a verdict:
  the layer is neither superseded nor dead, but whether the port retains it depends on a question that is
  still open — whether an honest charted integral can replace the pin's choice-based `pathIntegral`
  (`topics/aj/PLAN-W3-honest-integral.md` §4b prices the trade, §4c records why the answer is currently
  no). Nothing in `FLTForHuman` imports this module, and the merged A–B theory
  (`topics/aj/TOPIC-translation-a-b.md`) deliberately does not need it. It is shelved here so the tree
  can be checked in without the port carrying a speculation, and so that the mathematics is not lost
  while the decision is argued.

Mathlib `v4.34.0` has the honest curve integral of a 1-form `ω : E → E →L[𝕜] F` along a `Path a b`
(`Mathlib/MeasureTheory/Integral/CurveIntegral/{Basic,Poincare}.lean`, Kudryashov 2025):
`curveIntegral`, concatenation additivity `curveIntegral_trans`, the change-of-variables form
`curveIntegral_eq_intervalIntegral_deriv`, and the closed-form cancellation for a `C²` homotopy.  What
it does not have is the exact-form value theorem (`∫ᶜ ω = Φ b − Φ a` when `ω = dΦ`) and any statement
for a path on a *charted* space: `curveIntegral` takes the form and the path in the same space, so a
form read in a chart (a `ℂ`-valued function on `ℂ`) cannot be integrated along a path in the charted
space at all.  This module supplies both:

* `formOf f` — a `ℂ`-valued function as a mathlib 1-form `ℂ → ℂ →L[ℂ] ℂ`;
* `chartedPath` — the path pushed into `ℂ` through a chart, using `Path.map'`, which asks only for
  continuity of the chart *on the range of the path* (no global continuity);
* `chartedCurveIntegral` — the honest integral of a charted form along a path, per chart piece;
* `eventually_sub_eq_of_eventually_hasDerivAt` — two local primitives of one form differ by a constant
  near the point (the ball is convex);
* `chartedCurveIntegral_eq_sub` — the exact-form value theorem on a charted piece.

This is the definitional layer of `topics/aj/PLAN-W3-honest-integral.md`: the survivor of the
subject's path-integral duplication (parent note §10.2, §10.4 item 1).  Nothing here mentions a curve,
a place, a cusp form or a modular curve; it is a mathlib supplement and is upstreamable as written.


**No `spec-pin`.** The pin has no node for anything in this module: `pathIntegral` and
`IsPrimitiveAlong` are *definitions* there, and an honest charted integral does not exist in the
pin at all. These are port-side statements, so the wire is the wave's plan
(`topics/aj/PLAN-W3-honest-integral.md` §9) rather than a `Theorems/` wrapper.

The one non-mathematical hypothesis is `hcomp` in `chartedCurveIntegral_eq_sub`: the chain-rule
instance for a holomorphic `Ψ` composed with a real-differentiable charted path, which needs the
ℝ-Fréchet derivative of a ℂ-differentiable map.  It is stated rather than derived so that this
module needs no manifold differentiability API. It is the one item this module owes, and it is recorded
with the wave's other open items in `topics/aj/PLAN-W3-honest-integral.md` §3 and §10 — not in the
project's deferred-API register, since nothing outside the wave consumes it yet.
-/
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.Path

open scoped unitInterval Interval Topology Manifold
open MeasureTheory Set Filter

set_option autoImplicit false

namespace Complex

noncomputable section

/-- A `ℂ`-valued function as a mathlib 1-form: `formOf f = f dz`. -/
def formOf (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)

@[simp]
theorem formOf_apply (f : ℂ → ℂ) (z w : ℂ) : formOf f z w = w * f z := rfl

/-- The chart at a point, as a function to `ℂ`.  `extChartAt` is total, so this is a function on the
whole space; it is only continuous at (and near) points of its source. -/
def chartAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) : X → ℂ :=
  extChartAt 𝓘(ℂ, ℂ) x

/-- **The charted piece of a path.**  `Path.map'` needs only continuity of the chart on the *range* of
the path, which is exactly what a chart subdivision of a compact image provides. -/
def chartedPath {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) {P Q : X}
    (γ : Path P Q) (hγ : ContinuousOn (chartAt x) (range γ)) : Path (chartAt x P) (chartAt x Q) :=
  γ.map' hγ

/-- **The honest integral of a charted form along a path**, in one chart. -/
def chartedCurveIntegral {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X)
    (ω : ℂ → ℂ →L[ℂ] ℂ) {P Q : X} (γ : Path P Q) (hγ : ContinuousOn (chartAt x) (range γ)) : ℂ :=
  curveIntegral ω (chartedPath x γ hγ)

/-- Two functions that are primitives of the same `f` near `z₀` differ by a constant near `z₀`:
`Φ - Ψ` has vanishing derivative on a ball, and a ball is convex. -/
theorem eventually_sub_eq_of_eventually_hasDerivAt {f Φ Ψ : ℂ → ℂ} {z₀ : ℂ}
    (hΦ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ (f z) z)
    (hΨ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Ψ (f z) z) :
    ∀ᶠ z in 𝓝 z₀, Φ z - Ψ z = Φ z₀ - Ψ z₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hΦ.and hΨ)
  have hd : ∀ w ∈ Metric.ball z₀ ε, HasDerivAt (Φ - Ψ) 0 w := by
    intro w hw
    simpa using (hball w hw).1.sub (hball w hw).2
  have hconst : ∀ z ∈ Metric.ball z₀ ε, (Φ - Ψ) z = (Φ - Ψ) z₀ := by
    intro z hz
    refine Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (convex_ball z₀ ε) ?_ ?_ hz
      (Metric.mem_ball_self hε)
    · exact fun w hw => (hd w hw).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [fderivWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hw)]
      simpa using (hd w hw).hasFDerivAt.fderiv
  filter_upwards [Metric.ball_mem_nhds z₀ hε] with z hz
  simpa only [Pi.sub_apply] using hconst z hz

/-- **The exact-form value theorem on a charted piece**: if `Ψ` is a primitive of the charted form and
the charted path's own derivative is `γ'`, the honest integral is the primitive difference.

Mathlib has no exact-form value theorem for `curveIntegral` at all, and this is the charted-space
form of it: `curveIntegral`'s definition as an interval integral, then the fundamental theorem of
calculus on `t ↦ Ψ (γ.extend t)`.

`Ψ` is the primitive and `hcomp` is the chain-rule instance — `t ↦ Ψ (γ.extend t)` has derivative
`γ' * f ∘ γ` whenever `Ψ' = f` and the charted path is differentiable. That instance is the one piece
of glue stated as a hypothesis (it needs the ℝ-Fréchet derivative of a ℂ-differentiable map; see the
module header), and everything else here is proved. -/
theorem chartedCurveIntegral_eq_sub {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X)
    {f : ℂ → ℂ} {Ψ : ℂ → ℂ} {P Q : X} (γ : Path P Q)
    (hγ : ContinuousOn (chartAt x) (range γ))
    (hcomp : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => Ψ ((chartedPath x γ hγ).extend s))
        (deriv (chartedPath x γ hγ).extend t * f ((chartedPath x γ hγ).extend t)) t)
    (hint : IntervalIntegrable
      (fun t => deriv (chartedPath x γ hγ).extend t * f ((chartedPath x γ hγ).extend t))
      volume 0 1) :
    chartedCurveIntegral x (formOf f) γ hγ = Ψ (chartAt x Q) - Ψ (chartAt x P) := by
  rw [chartedCurveIntegral, curveIntegral_eq_intervalIntegral_deriv]
  have hcongr : ∀ t : ℝ,
      formOf f ((chartedPath x γ hγ).extend t) (deriv (chartedPath x γ hγ).extend t) =
        deriv (chartedPath x γ hγ).extend t * f ((chartedPath x γ hγ).extend t) :=
    fun _ => rfl
  simp only [hcongr]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp hint]
  simp only [chartedPath, Path.extend_one, Path.extend_zero]

end

end Complex
