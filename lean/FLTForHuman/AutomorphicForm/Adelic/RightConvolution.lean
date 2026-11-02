/-
  Right convolution by a test function.

  `rightConv φ f g = ∫ x, φ (g * x) * f x ∂μ` is the right-regular action of the
  test function `f` on `φ`, integrated against the Haar measure on `GL₂(𝔸_K)`. Its
  `rfl` unfolding and its zero/left-translation laws are what the smoothing and
  Hecke-eigenfunction statements consume.

  `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` is the Haar-invariance law
  that moves a right translation of the group variable into the test function:
  `rightConv φ f (g * t) = rightConv φ (f ∘ (t⁻¹ * ·)) g`. It is the algebraic input
  of the archimedean-derivative chain (`archDerivAt_rightConv_eq_rightConv_deriv_…`).

  `Definitions/Def_AutomorphicForm_RightConvolution.lean` verbatim (pinned
  `aa2d8b3`), plus the translation law from
  `P2M/Sol/S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.lean`;
  the pin's Haar vocabulary is the port's `AdelicHaar/GeneralLinear`.

  spec-pin: Definitions/Def_AutomorphicForm_RightConvolution.lean
  spec-pin: Theorems/Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.lean
-/
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

open NumberField MeasureTheory

namespace AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def rightConv (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun g =>
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
     ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))

theorem rightConv_apply (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f g =
      (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
       ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) :=
  rfl

theorem rightConv_zero_right (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K φ (fun _ => 0) = fun _ => 0 := by
  funext g
  simp [rightConv]

theorem rightConv_zero_left (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K (fun _ => 0) f = fun _ => 0 := by
  funext g
  simp [rightConv]

theorem rightConv_comp_mul_left (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (h g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K (fun x => φ (h * x)) f g = rightConv K φ f (h * g) := by
  simp only [rightConv, mul_assoc]

set_option linter.style.haveILetI false in
/-- A right translation of the group variable is absorbed by the test function: the
Haar measure is left-invariant, so `x ↦ g * t * x` is re-indexed to `x ↦ g * x`. -/
theorem rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply (K : Type) [Field K]
    [NumberField K] (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  show (∫ x, φ (g * t * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∫ x, φ (g * x) * f (t⁻¹ * x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  have h := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun x => φ (g * x) * f (t⁻¹ * x)) t
  simp only [inv_mul_cancel_left] at h
  simpa only [mul_assoc] using h

end AutomorphicForm
