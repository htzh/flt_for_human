/-
  The right action on automorphic functions: how convolution interacts with translation and with
  the archimedean Casimir.

  Right convolution and right translation are two halves of the same right `GL₂(𝔸)`-action, and
  this module records how they commute with each other and with the archimedean `𝔰𝔩₂(ℂ)` action:

  * `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj`: convolving a
    translate is translating a convolution with the conjugated kernel,
    `(φ · h) * f = h · (φ * (f ∘ (h · · h⁻¹)))` — a change of variables in the defining integral.
  * `rightTranslate_rightConv_of_isLevelSphericalOfType`: for a level-spherical `f` the row-isometry
    translate passes through the convolution, `k · (φ * f) = (k · φ) * f`.
  * `archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex`: for a
    continuous arch-smooth `x` whose first and second archimedean derivatives are continuous, both
    right actions are arch-smooth again and commute with the Casimir and its conjugate: with the
    row-isometry translate `k` on one side, and with right convolution by a factorisable
    arch-bi-finite `f` on the other.

  Transcribed from the pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj.lean`
  * `P2M/Sol/S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType.lean`
  * `P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex.lean`

  **Wiring.** `spec/check_port.py` owns the three public declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj.lean
  spec-pin: Theorems/Thm_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType.lean
  spec-pin: Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ArchSpherical
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConvComplex
import FLTForHuman.AutomorphicForm.Adelic.RightConvDerivatives
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace AutomorphicForm

theorem CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
    (F : Type) [Field F] [NumberField F]
    (h : AdelicGL2 (𝓞 F) F) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (rightTranslate F h φ) f =
      rightTranslate F h (rightConv F φ (fun y => f (h * y * h⁻¹))) := by
  let _measG : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have _borelG : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have _haar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have _mulRight : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  funext g
  show (∫ x, rightTranslate F h φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F))
      = ∫ x, φ (g * h * x) * f (h * x * h⁻¹) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  simp only [rightTranslate_apply]
  have h1 := MeasureTheory.integral_mul_left_eq_self
    (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * h * x) * f (h * x * h⁻¹)) h⁻¹
  simp only [← mul_assoc, mul_inv_cancel_right, mul_inv_cancel, one_mul] at h1
  have h2 := MeasureTheory.integral_mul_right_eq_self
    (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * x) * f (x * h⁻¹)) h
  simp only [mul_inv_cancel_right, ← mul_assoc] at h2
  rw [h2, h1]

theorem rightTranslate_rightConv_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys U f)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (rowIsometryInclAt₀ F w k) (rightConv F φ f) =
      rightConv F (rightTranslate F (rowIsometryInclAt₀ F w k) φ) f := by
  obtain ⟨fa, -, -, hconj, hfac⟩ := hf
  have hinv : (fun y => f (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹)) = f := by
    funext y
    rw [hfac (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹), hfac y]
    simp only [_root_.map_mul, _root_.map_inv, glArch_rowIsometryInclAt₀,
      glFin_rowIsometryInclAt₀, hconj, one_mul, inv_one, mul_one]
  rw [AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj,
    hinv]

theorem archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex,
          Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex,
          Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f) := by
  classical
  refine ⟨?_, archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    K w hw x hxc hxs hD1 hD2⟩
  intro w' k
  by_cases hw' : w' = w
  · subst hw'
    have hkm : rowIsometryInclAt₀ K w' k =
        archComplexGLAt hw (glEquivOfRingEquiv
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
          (k : GL (Fin 2) w'.Completion)) := by
      rw [rowIsometryInclAt₀_apply, archComplexGLAt_glEquivOfRingEquiv]
    rw [hkm]
    exact archCasimirAtComplex_rightTranslate_archComplexGLAt K w' hw x hxc hxs hD1 hD2 _
  · exact archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne K w hw x hxc hxs hD1 hD2 w' hw' k

end AutomorphicForm
