/-
  The `∂̄` operator of one complex variable, and the small API around it.

  For `h : ℂ → ℂ` regarded as a function of two real variables,
  `dbar h z = (fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2`
  is the anti-holomorphic derivative: the density on the left of the Pompeiu identity
  `∫ z, G z * dbar h z = -π * ∑ a, c a * h a` and of its residue forms, ported in
  `Pompeiu.lean` and `MeromorphicResidue.lean` of this directory.

  The module holds the vocabulary the rest of the family shares: the operator itself, its
  continuity/compact-support transfer, the vanishing off the support, and the three integrability
  lemmas for the `1/(z-a)` kernel that the residue forms integrate against. All of it is stated for
  an arbitrary `h` / `u` with no curve, chart or place in sight, so it is a mathlib-shaped supplement
  rather than a piece of the FLT development.

  No `spec-pin:` wire: none of these is a pin node. The nine statements that *are* pinned spell `∂̄`
  out inline and are transcribed verbatim in the two modules above, which cite these lemmas from
  their proofs only (decision D1 of `topics/aj/PLAN-W1-stokes.md`).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology Real InnerProductSpace

namespace Complex

/-- The anti-holomorphic derivative `∂̄h = (∂ₓh + I ∂ᵧh) / 2`, written through the real
Fréchet derivative so that no choice of chart is needed. -/
def dbar (h : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2

@[simp]
theorem dbar_apply (h : ℂ → ℂ) (z : ℂ) :
    dbar h z = (fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2 := rfl
theorem continuous_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgV : tsupport g ⊆ V) :
    Continuous fun z => f z * g z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ V
  · exact (hf.continuousAt (hV.mem_nhds hz)).mul hg.continuousAt
  · have hz' : z ∉ tsupport g := fun h' => hz (hgV h')
    have h0 : g =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : (fun w => f w * g w) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [hw]
    exact (continuousAt_congr this).2 continuousAt_const


theorem integrable_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) : Integrable fun z => f z * g z :=
  (continuous_mul_of_tsupport_subset hV hf hg hgV).integrable_of_hasCompactSupport hgs.mul_left


theorem dbar_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dbar f) := by
  have hc : ∀ v : ℂ, Continuous fun z => fderiv ℝ f z v := fun v =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hc 1).add (continuous_const.mul (hc I))).div_const _


theorem dbar_eq_zero_of_notMem_tsupport {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport f) :
    dbar f z = 0 := by
  simp [dbar_apply, fderiv_of_notMem_tsupport ℝ hz]


theorem dbar_hasCompactSupport {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dbar f) :=
  HasCompactSupport.intro hf fun _ hz => dbar_eq_zero_of_notMem_tsupport hz


theorem integrableOn_inv (r : ℝ) : IntegrableOn (fun x : ℂ => x⁻¹) (ball 0 r) := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := 1) (α := 1) ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_inv, Real.rpow_neg_one, one_mul]
  · exact measurable_inv.aestronglyMeasurable


theorem integrableOn_inv_sub (a : ℂ) (r : ℝ) :
    IntegrableOn (fun z : ℂ => (z - a)⁻¹) (ball a r) := by
  have hT := (measurePreserving_add_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (measurableEmbedding_addRight a) (f := fun z : ℂ => (z - a)⁻¹) (s := ball a r)
  rw [← hT]
  have hpre : (fun x : ℂ => x + a) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, add_sub_cancel_right, sub_zero]
  rw [hpre]
  simp only [Function.comp_def, add_sub_cancel_right]
  exact integrableOn_inv r


theorem integrable_inv_sub_mul (a : ℂ) {u : ℂ → ℂ} (hu : Continuous u)
    (hus : HasCompactSupport u) : Integrable fun z => (z - a)⁻¹ * u z := by
  obtain ⟨R, hR⟩ := hus.isCompact.isBounded.subset_closedBall a
  have hq : IntegrableOn (fun z : ℂ => (z - a)⁻¹) (closedBall a (R + 1)) :=
    (integrableOn_inv_sub a (R + 2)).mono_set (closedBall_subset_ball (by linarith))
  have h1 : IntegrableOn (fun z => (z - a)⁻¹ * u z) (closedBall a (R + 1)) :=
    hq.mul_continuousOn hu.continuousOn (isCompact_closedBall _ _)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro z hz
  have huz : u z ≠ 0 := fun h0 => hz (by simp [h0])
  exact closedBall_subset_closedBall (by linarith) (hR (subset_tsupport _ huz))


end Complex
