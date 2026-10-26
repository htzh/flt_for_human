/-
The honest (charted) line integral of a differential on a curve, and the theorem that makes
`pathIntegral` computable.

  **Reserve.** Kept out of the critical-path port for the same holding reason as
  `Reserve/Analysis/Complex/ChartedCurveIntegral.lean`: whether an honest integral replaces the pin's
  choice-based `pathIntegral` is still open (`topics/aj/PLAN-W3-honest-integral.md` §4b–§4c), and nothing
  in `FLTForHuman` imports this module. `pathIntegral_eq_sub_of_isPrimitiveAlong` is worth keeping either
  way — it makes the pin's `Classical.choose` computable, and it is the fidelity lemma that would license
  the replacement if the decision ever flips.

The pin defines the path integral by choice over primitives:

  `pathIntegral ω γ = if ∃ g, IsPrimitiveAlong ω γ g then g.choose 1 - g.choose 0 else 0`

(`Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean`, ported verbatim in
`AlgebraicCurve/Defs/ComplexLineIntegral.lean`).  Two things follow that the pin never states:

* **the choice is not a choice**: every primitive along `γ` has the same endpoint difference
  (`endpoint_sub_eq_of_isPrimitiveAlong`), so `pathIntegral ω γ = g 1 - g 0` for *any* `g` with
  `IsPrimitiveAlong ω γ g` (`pathIntegral_eq_sub_of_isPrimitiveAlong`).  This is the lemma a consumer
  needs in order to compute a path integral, and it is what lets the primitive bookkeeping be replaced
  by honest integrals.
* **there is an honest integral to replace it with**: `placeCurveIntegral` is the honest integral of
  `readDifferential` along a path, in one chart, built on mathlib's `curveIntegral`
  (`Analysis/Complex/ChartedCurveIntegral.lean`, which supplies the charted piece, the per-chart
  integral and the exact-form value theorem).

Neither statement uses any differentiability of `γ`: the primitive-uniqueness argument is
"two local primitives of one form differ by a constant", transported along the chart and then
collapsed on the preconnected `unitInterval`.  The charted integral's value theorem
(`placeCurveIntegral_eq_sub`) does take the charted path's derivative, because that is what an
integral is.


**No `spec-pin`.** The pin has no node for anything in this module: `pathIntegral` and
`IsPrimitiveAlong` are *definitions* there, and an honest charted integral does not exist in the
pin at all. These are port-side statements, so the wire is the wave's plan
(`topics/aj/PLAN-W3-honest-integral.md` §9) rather than a `Theorems/` wrapper.

This is the curve-side seam of `topics/aj/PLAN-W3-honest-integral.md` §5: it is the only module of the
wave that mentions the pin's vocabulary (`Place`, `Ω[F⁄ℂ]`, `IsPrimitiveAlong`, `pathIntegral`).
-/
import FLTForHuman.AlgebraicCurve.Defs.ComplexLineIntegral
import Reserve.Analysis.Complex.ChartedCurveIntegral

open scoped unitInterval Interval Topology Manifold
open MeasureTheory Set Filter Complex

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

/-- The differential `ω` read in the chart at `v`, as a mathlib 1-form on `ℂ`. -/
def placeForm (v : Place ℂ F) (ω : Ω[F⁄ℂ]) : ℂ → ℂ →L[ℂ] ℂ :=
  Complex.formOf (v.readDifferential ω)

@[simp]
theorem placeForm_apply (v : Place ℂ F) (ω : Ω[F⁄ℂ]) (z w : ℂ) :
    placeForm v ω z w = w * v.readDifferential ω z := rfl

/-- **The honest integral of `ω` along `γ`, in the chart at `v`.** -/
def placeCurveIntegral (v : Place ℂ F) (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q)
    (hγ : ContinuousOn (Complex.chartAt v) (range γ)) : ℂ :=
  Complex.chartedCurveIntegral v (placeForm v ω) γ hγ

/-- **Two primitives along the same path have the same endpoint difference.** -/
theorem endpoint_sub_eq_of_isPrimitiveAlong {ω : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong ω γ g) (hg' : IsPrimitiveAlong ω γ g') :
    g 1 - g 0 = g' 1 - g' 0 := by
  have key : ∀ t₀ : unitInterval, ∀ᶠ t in 𝓝 t₀, g t - g' t = g t₀ - g' t₀ := by
    intro t₀
    obtain ⟨Φ, hΦ, hΦg⟩ := hg t₀
    obtain ⟨Ψ, hΨ, hΨg⟩ := hg' t₀
    -- both are primitives of `readDifferential (γ t₀) ω` near the charted point
    set z₀ : ℂ := (extChartAt 𝓘(ℂ, ℂ) (γ t₀)) (γ t₀) with hz₀
    have hchart : Tendsto (fun t : unitInterval => (extChartAt 𝓘(ℂ, ℂ) (γ t₀)) (γ t))
        (𝓝 t₀) (𝓝 z₀) :=
      (continuousAt_extChartAt (γ t₀)).tendsto.comp γ.continuous.continuousAt
    have hev := eventually_sub_eq_of_eventually_hasDerivAt hΦ hΨ
    have hg0 : g t₀ = Φ z₀ := by simpa [hz₀] using mem_of_mem_nhds hΦg
    have hg'0 : g' t₀ = Ψ z₀ := by simpa [hz₀] using mem_of_mem_nhds hΨg
    filter_upwards [hΦg, hΨg, hchart.eventually hev] with t h1 h2 h3
    rw [h1, h2, hg0, hg'0]
    exact h3
  have hloc : IsLocallyConstant (fun t : unitInterval => g t - g' t) :=
    (IsLocallyConstant.iff_eventually_eq _).mpr key
  have h1 : g 1 - g' 1 = g 0 - g' 0 :=
    hloc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ (1 : unitInterval))
      (mem_univ (0 : unitInterval))
  calc g 1 - g 0 = (g 1 - g' 1) + (g' 1 - g 0) := by ring
    _ = (g 0 - g' 0) + (g' 1 - g 0) := by rw [h1]
    _ = g' 1 - g' 0 := by ring

/-- **`pathIntegral` is any primitive's endpoint difference.**  The pin's `Classical.choose` is
irrelevant: `pathIntegral ω γ` is the endpoint difference of *every* primitive of `ω` along `γ`. -/
theorem pathIntegral_eq_sub_of_isPrimitiveAlong {ω : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong ω γ g) : pathIntegral ω γ = g 1 - g 0 := by
  classical
  have hex : ∃ h : unitInterval → ℂ, IsPrimitiveAlong ω γ h := ⟨g, hg⟩
  rw [pathIntegral_def, dite_eq_left hex]
  exact endpoint_sub_eq_of_isPrimitiveAlong (Classical.choose_spec hex) hg

/-- **The charted value theorem on a curve**: the honest integral of `ω` along `γ` in the chart at `v`
is the primitive difference, whenever `t ↦ Ψ (charted path)` has derivative
`(charted path)' * readDifferential ω` and that derivative is interval-integrable.  This is
`Complex.chartedCurveIntegral_eq_sub` specialised to the curve's charted forms. -/
theorem placeCurveIntegral_eq_sub (v : Place ℂ F) (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q)
    (hγ : ContinuousOn (Complex.chartAt v) (range γ)) {Ψ : ℂ → ℂ}
    (hcomp : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => Ψ (Complex.chartedPath v γ hγ |>.extend s))
        (deriv (Complex.chartedPath v γ hγ |>.extend) t *
          v.readDifferential ω (Complex.chartedPath v γ hγ |>.extend t)) t)
    (hint : IntervalIntegrable
      (fun t => deriv (Complex.chartedPath v γ hγ |>.extend) t *
        v.readDifferential ω (Complex.chartedPath v γ hγ |>.extend t)) volume 0 1) :
    placeCurveIntegral v ω γ hγ = Ψ (Complex.chartAt v Q) - Ψ (Complex.chartAt v P) := by
  simpa [placeCurveIntegral, placeForm] using
    Complex.chartedCurveIntegral_eq_sub (X := Place ℂ F) v (f := v.readDifferential ω)
      (Ψ := Ψ) γ hγ hcomp hint

end AlgebraicCurve
