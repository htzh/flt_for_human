/-
  The dead tail of `FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConv`, copied out of it on
  2026-11-02 — the declarations its headline does not reach, with the private premises they need.

  Five real statements about the port's own objects, dead **in the pin as well as in the port**
  (measured: one occurrence each in the pin's `S_` file, the declaration line only), kept here rather
  than deleted because they are mathematics: the linearity of `rightConv` in its test function
  (`l5_rightConv_add_right`, `l5_rightConv_smul_right`), the archimedean smoothness of `α ∘ (·)⁻¹`
  (`l5_isArchSmoothAt_comp_inv`) with its derivative bridge `l5_leftDeriv_inv`, and the `n = 0` case
  of the `TcFamily` integral engine (`tc_integrable_zero`).

  The one dead declaration that was **deleted**, not shelved, is `l5_continuous_rightConv`: it is the
  first conjunct of SET-AF5's public
  `AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn`, i.e. already in the port
  at a stronger statement, so keeping it anywhere would be a duplicate rather than dead content.

  Nothing in `FLTForHuman` imports this module and it declares no `spec-pin:` wire: it is a reading
  shelf in `Reserve`, built so it stays green and diffed by nothing. Its premises are copies — the
  live module keeps its own.
-/
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant

set_option autoImplicit false
-- the pin's `letI := glBorel` / `haveI := borelSpace_…` walls; the live module scopes the same
-- suppression per declaration, a shelf can take it once
set_option linter.style.haveILetI false

open NumberField AutomorphicForm NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal isometryEquivRealOfIsReal)
open scoped Topology

noncomputable section

namespace AutomorphicForm

open IsFactorizableTestFn

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

section TestData

open MeasureTheory
open scoped Pointwise

set_option linter.style.haveILetI false in
private theorem l5_integrable_conv_integrand {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hαc : Continuous α)
    (hαs : HasCompactSupport α) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  refine ((hφ.comp (continuous_const.mul continuous_id)).mul hαc).integrable_of_hasCompactSupport (hαs.mono ?_)
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by show φ (g * y) * α y = 0; rw [h0, mul_zero])

end TestData

section EngineBridge

open MeasureTheory Metric Set

section Engine

variable {X : Type} [MeasurableSpace X] (ν : Measure X)
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private structure TcFamily (F : X → ArchEntry → Y) : Prop where
  smooth : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (F x) nonsingEntries
  meas : ∀ m : ℕ, ∀ e ∈ nonsingEntries, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (F x) e) ν
  bound : ∀ e₀ ∈ nonsingEntries, ∀ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ball e₀ ρ ⊆ nonsingEntries ∧
    ∃ C : ℝ, ∀ᵐ x ∂ν, ∀ e ∈ ball e₀ ρ, ‖iteratedFDeriv ℝ m (F x) e‖ ≤ C

variable {ν}

private theorem tc_aesm_of_zero {g : X → ArchEntry → Y} {e : ArchEntry}
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 0 (g x) e) ν) :
    AEStronglyMeasurable (fun x => g x e) ν := by
  have hfun : (fun x => g x e) =
      fun x => (continuousMultilinearCurryFin0 ℝ ArchEntry Y) (iteratedFDeriv ℝ 0 (g x) e) := by
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryFin0 ℝ ArchEntry Y).continuous.comp_aestronglyMeasurable h

private theorem tc_integrable_zero [IsFiniteMeasure ν] {F : X → ArchEntry → Y} (hF : TcFamily ν F) {e₀ : ArchEntry}
    (he₀ : e₀ ∈ nonsingEntries) : Integrable (fun x => F x e₀) ν := by
  obtain ⟨ρ, hρ, -, C, hC⟩ := hF.bound e₀ he₀ 0
  refine Integrable.of_bound (tc_aesm_of_zero (hF.meas 0 e₀ he₀)) C (hC.mono fun x hx => ?_)
  have h0 := hx e₀ (mem_ball_self hρ)
  rwa [norm_iteratedFDeriv_zero] at h0

end Engine

end EngineBridge

section Conv

open MeasureTheory Metric Set
open scoped Classical
private theorem l5_rightConv_add_right {φ α₁ α₂ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hα₁c : Continuous α₁) (hα₁s : HasCompactSupport α₁) (hα₂c : Continuous α₂) (hα₂s : HasCompactSupport α₂) :
    rightConv K φ (α₁ + α₂) = rightConv K φ α₁ + rightConv K φ α₂ := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (α₁ + α₂) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    (∫ y, φ (g * y) * α₁ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) +
      ∫ y, φ (g * y) * α₂ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_add (l5_integrable_conv_integrand hφ hα₁c hα₁s g) (l5_integrable_conv_integrand hφ hα₂c hα₂s g)]
  congr 1
  funext y
  rw [Pi.add_apply, mul_add]

set_option linter.style.haveILetI false in
private theorem l5_rightConv_smul_right (φ α : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) :
    rightConv K φ (c • α) = c • rightConv K φ α := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (c • α) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    c * ∫ y, φ (g * y) * α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  ring

private theorem l5_leftDeriv_inv (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ)
    (y : AdelicGL2 (𝓞 K) K) :
    leftDerivFactor hw d α y⁻¹ = archDerivAt hw d (fun z => α z⁻¹) y := by
  show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y⁻¹)) 0 =
    deriv (fun t : ℝ => α (y * archFlowAt hw d t)⁻¹) 0
  congr 1
  funext t
  rw [mul_inv_rev, lift_archFlowAt_inv]

private theorem l5_isArchSmoothAt_comp_inv (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw fun z => α z⁻¹ := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, -, hαeq⟩ := hα
  intro g
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun e : ArchEntry => Φ (liftCD w g⁻¹ + liftLD hw g⁻¹ (invEntries e)) * ff (glFin (𝓞 K) K g⁻¹))
      nonsingEntries :=
    (hΦ.comp_contDiffOn
      (contDiffOn_const.add ((liftLD hw g⁻¹).contDiff.comp_contDiffOn chart_contDiffOn_invEntries))).mul
      contDiffOn_const
  refine hsm.congr fun e he => ?_
  show α (g * archRealLiftAt hw e)⁻¹ = _
  rw [mul_inv_rev, lift_lift_inv hw he, lift_factor_lift_mul hw hfa hαeq (chart_det_invEntries he)]
  rfl

end Conv

end AutomorphicForm

end
