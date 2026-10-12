/-
  The measure assembly: the archimedean projection measure `archNu` and the kernel
  reduction of the right-convolution headline.

  `archNu F U` is the push-forward of adèlic Haar measure along the archimedean
  projection of the `ProjectedHaar` slab of `U`; the engine proves it Haar,
  right-invariant, inversion-invariant and `thetaArch`-invariant under the compactness
  and openness of the level image, and `adelicKernel` is the reduced kernel. The
  `TestFunctions` block supplies the continuity/compact-support facts for archimedean
  test factors and factorisable test functions, and `levelSpherical_eq_cut` rewrites a
  level-spherical `f` as a cut function on the frame.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:1028–1119`
  and `:1298–1380`, with the engine written at the compact silo's general-`U` spelling
  (`P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean:999–1085`
  and `:1270–1334`), pinned `aa2d8b3`. The level-`N` specializations are the plain
  silo's (`levelSubgroup`, `isCompact_level_image'`, `isOpen_level_image`,
  `isClosed_level_image`), one public copy each at the pin's names; the two-bodied names
  the engine needs (`archNu`, `isCompact_level_image`, `isOpen_level_slab`,
  `archNu_is*`, `levelSpherical_*`) keep the general-`U` body per work order §1.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Frame
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant
import FLTForHuman.RepTheory.AntiInvolutionHaar
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.ArchSpherical
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls feed instance search.
set_option linter.style.haveILetI false

open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain MeasureTheory AutomorphicForm

open scoped RestrictedProduct

-- Activate the `scoped` instances of `SecondCountableAdelic` (the pin's
-- `p2m_reactivate "…SecondCountableAdelic"`).
open scoped SecondCountableAdelic

noncomputable section

namespace MeasureAssembly

section Kernels

variable {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (P Q : H → ℂ) (x : H)

theorem projected_convKer_eq_antiInvolution_convKer :
    ProjectedHaar.convKer m P Q x = AntiInvolutionHaar.convKer m P Q x := rfl

theorem projected_convKer_eq_reduction_convKer :
    ProjectedHaar.convKer m P Q x = KernelReduction.convKer m P Q x := rfl

end Kernels

@[reducible] def archBorel (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F)) := borel _

attribute [local instance] NumberField.AdelicHaar.glBorel archBorel

variable (F : Type) [Field F] [NumberField F]

private scoped instance borelSpace_adelic : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F

private scoped instance borelSpace_arch : BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩

private scoped instance isHaarMeasure_adelic : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

private scoped instance isMulRightInvariant_adelic : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
  isMulRightInvariant_adelicGLHaar F

def archNu (U : Subgroup (AdelicGL2 (𝓞 F) F)) : Measure (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F)) :=
  ProjectedHaar.nu (ProjectedHaar.adelicFrame F) (adelicGLHaar (Fin 2) (𝓞 F) F)
    (U.map (AdelicLevel.glFin (𝓞 F) F))

variable (U : Subgroup (AdelicGL2 (𝓞 F) F))

theorem isCompact_level_image (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    IsCompact ((U.map (AdelicLevel.glFin (𝓞 F) F) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :
        Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) := by
  rw [Subgroup.coe_map]
  exact hUc

theorem isOpen_level_slab (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    IsOpen (ProjectedHaar.slab (ProjectedHaar.adelicFrame F)
      (U.map (AdelicLevel.glFin (𝓞 F) F))) := by
  unfold ProjectedHaar.slab
  rw [Subgroup.coe_map]
  exact MeasureGlue.isOpen_glFin_preimage_image_level F U hUo

theorem archNu_isHaarMeasure (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) : (archNu F U).IsHaarMeasure :=
  ProjectedHaar.nu_isHaarMeasure (ProjectedHaar.adelicFrame F) (adelicGLHaar (Fin 2) (𝓞 F) F) _
    (ProjectedHaar.continuous_adelicFrame_π F) (ProjectedHaar.continuous_adelicFrame_ι F)
    (ProjectedHaar.continuous_adelicFrame_ιf F) (isCompact_level_image F U hUc) (isOpen_level_slab F U hUo)

theorem archNu_isMulRightInvariant (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    (archNu F U).IsMulRightInvariant :=
  ProjectedHaar.nu_isMulRightInvariant (ProjectedHaar.adelicFrame F) (adelicGLHaar (Fin 2) (𝓞 F) F) _
    (ProjectedHaar.continuous_adelicFrame_π F) (isOpen_level_slab F U hUo).measurableSet

theorem archNu_isInvInvariant (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) : (archNu F U).IsInvInvariant :=
  haveI := archNu_isHaarMeasure F U hUc hUo
  haveI := archNu_isMulRightInvariant F U hUo
  AntiInvolutionHaar.isInvInvariant (archNu F U)

theorem archNu_map_eq_self (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (Θ : AntiInvolutionHaar.AntiInvolution (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F))) :
    (archNu F U).map Θ.θ = archNu F U :=
  haveI := archNu_isHaarMeasure F U hUc hUo
  haveI := archNu_isMulRightInvariant F U hUo
  AntiInvolutionHaar.map_θ_eq_self (archNu F U) Θ

def adelicKernel (h f : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  KernelReduction.convKer (adelicGLHaar (Fin 2) (𝓞 F) F) h f

theorem rightConv_rightConv (φ f h : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hh : Continuous h) (hhc : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (adelicKernel F h f) := by

  funext g
  exact KernelReduction.rc_rc (adelicGLHaar (Fin 2) (𝓞 F) F) φ f h hφ hf hfc hh hhc g

/-! ### The level-`N` side facts (plain silo) -/

def levelSubgroup (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

variable (N : Ideal (𝓞 F))

theorem isCompact_level_image' :
    IsCompact (AdelicLevel.glFin (𝓞 F) F '' ((levelSubgroup F N : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F))) :=
  MeasureGlue.isCompact_glFin_image_level F N

theorem isOpen_level_image (hN : N ≠ ⊥) :
    IsOpen (AdelicLevel.glFin (𝓞 F) F '' ((levelSubgroup F N : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F))) := by
  show IsOpen (AdelicLevel.glFin (𝓞 F) F '' ((AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
    Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)))
  rw [MeasureGlue.glFin_image_level F N]
  exact AdelicLevel.isOpen_finiteLevelOne (𝓞 F) F hN

theorem isClosed_level_image (hN : N ≠ ⊥) :
    IsClosed (AdelicLevel.glFin (𝓞 F) F '' ((levelSubgroup F N : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F))) := by
  show IsClosed (AdelicLevel.glFin (𝓞 F) F '' ((AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
    Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)))
  rw [MeasureGlue.glFin_image_level F N]
  exact (AdelicLevel.finiteLevelOne (𝓞 F) F N).isClosed_of_isOpen (AdelicLevel.isOpen_finiteLevelOne (𝓞 F) F hN)

end MeasureAssembly

end

section TestFunctions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm

noncomputable section

namespace MeasureAssembly

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in
theorem testFactor_continuous {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩ := hfa
  have h : fa = fun g => Φ (archEntries F g) := funext hfaΦ
  rw [h]
  refine hΦ.continuous.comp (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [archEntries_apply]
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

theorem testFactor_hasCompactSupport {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) : HasCompactSupport fa := hfa.2

theorem factorizable_continuous {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : IsFactorizableTestFn F h) :
    Continuous h := by
  obtain ⟨fa, ff, hfa, hff, hfact⟩ := hh
  exact KernelSides.continuous_of_factors (ProjectedHaar.adelicFrame F) (ProjectedHaar.continuous_adelicFrame_π F)
    (ProjectedHaar.continuous_adelicFrame_πf F) (testFactor_continuous F hfa) hff.1.continuous hfact

theorem factorizable_hasCompactSupport {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : IsFactorizableTestFn F h) :
    HasCompactSupport h := by
  obtain ⟨fa, ff, hfa, hff, hfact⟩ := hh
  exact KernelSides.hasCompactSupport_of_factors (ProjectedHaar.adelicFrame F)
    (ProjectedHaar.continuous_adelicFrame_ι F) (ProjectedHaar.continuous_adelicFrame_ιf F) hfa.2 hff.2 hfact

variable (U : Subgroup (AdelicGL2 (𝓞 F) F))

theorem levelSpherical_continuous (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUcl : IsClosed (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsLevelSphericalOfType F tys U f) : Continuous f := by
  obtain ⟨fa, hfa, -, -, hfact⟩ := hf
  exact KernelSides.continuous_of_factors (ProjectedHaar.adelicFrame F) (ProjectedHaar.continuous_adelicFrame_π F)
    (ProjectedHaar.continuous_adelicFrame_πf F) (testFactor_continuous F hfa)
    (KernelSides.continuous_indicator_of_isOpen_of_isClosed hUo hUcl)
    hfact

theorem levelSpherical_hasCompactSupport (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsLevelSphericalOfType F tys U f) : HasCompactSupport f := by
  obtain ⟨fa, hfa, -, -, hfact⟩ := hf
  exact KernelSides.hasCompactSupport_of_factors (ProjectedHaar.adelicFrame F)
    (ProjectedHaar.continuous_adelicFrame_ι F) (ProjectedHaar.continuous_adelicFrame_ιf F) hfa.2
    (KernelSides.hasCompactSupport_indicator hUc) hfact

theorem levelSpherical_eq_cut {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsLevelSphericalOfType F tys U f) :
    ∃ fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchSphericalOfType F tys fa ∧
      f = ProjectedHaar.cut (ProjectedHaar.adelicFrame F)
        (U.map (ProjectedHaar.adelicFrame F).πf) fa := by
  obtain ⟨fa, h1, h2, h3, hfact⟩ := hf
  exact ⟨fa, ⟨h1, h2, h3⟩, funext fun g =>
    (hfact g).trans (ProjectedHaar.cut_map_apply (ProjectedHaar.adelicFrame F) U fa g).symm⟩

end MeasureAssembly

end

end TestFunctions
