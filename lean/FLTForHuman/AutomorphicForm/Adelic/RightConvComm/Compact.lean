/-
  The compact right-convolution commutation headline.

  For a compact subgroup `U = O ⊓ finiteAdelicGL2Subgroup F` with `O` open, a
  `U`-level-spherical `f`, an archimedean bi-finite factorisable test function `h`
  invariant under `U` on both sides, and a continuous `φ`, the two right convolutions
  commute. The proof is the compact silo's `solution`: the level image `glFin '' U` is
  compact and open, `MeasureAssembly.levelSpherical_*` supplies the continuity and
  compact support of `f` and `SliceCentrality.adelicKernel_comm` the reduced kernel
  identity, which `MeasureAssembly.rightConv_rightConv` reassociates into the headline.

  Statement verbatim from
  `Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean`;
  proof from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean:3377–3425`
  (pinned `aa2d8b3`). The wrapper's `attribute [-simp]`/`[-instance]` prelude is not
  transcribed.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.SliceCentrality
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.MeasureAssembly
import Mathlib.Tactic

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

noncomputable section

namespace AutomorphicForm

theorem rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by

  have hUK : U ≤ finiteAdelicGL2Subgroup F := hUO ▸ inf_le_right
  have hcontFE : Continuous (AdelicDock.finEmbed (𝓞 F) F) := ProjectedHaar.continuous_adelicFrame_ιf F
  have himg : AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)) = AdelicDock.finEmbed (𝓞 F) F ⁻¹' (O : Set (AdelicGL2 (𝓞 F) F)) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' := hUO ▸ hu
      obtain ⟨huO, huK⟩ := Subgroup.mem_inf.mp hu'
      have hfe : AdelicDock.finEmbed (𝓞 F) F (AdelicLevel.glFin (𝓞 F) F u) = u := by
        refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
        · have h1 := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
            ((AdelicDock.glArch_finEmbed (𝓞 F) F (AdelicLevel.glFin (𝓞 F) F u)).trans ((mem_finiteAdelicGL2Subgroup_iff F _).mp huK).symm)
          simpa only [AdelicLevel.glArch_apply] using h1
        · have h2 := congrArg (fun m : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j)
            (AdelicDock.glFin_finEmbed (𝓞 F) F (AdelicLevel.glFin (𝓞 F) F u))
          simpa only [AdelicLevel.glFin_apply] using h2
      rw [hfe]; exact huO
    · intro hy
      refine ⟨AdelicDock.finEmbed (𝓞 F) F y, ?_, AdelicDock.glFin_finEmbed (𝓞 F) F y⟩
      rw [hUO]
      exact Subgroup.mem_inf.mpr ⟨hy, (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F y)⟩
  have hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) := hU.image (AdelicLevel.continuous_glFin (𝓞 F) F)
  have hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) := himg ▸ hO.preimage hcontFE
  have hUcl : IsClosed (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) := himg ▸ (O.isClosed_of_isOpen hO).preimage hcontFE
  have hfc := MeasureAssembly.levelSpherical_continuous F U hUo hUcl hf
  have hfs := MeasureAssembly.levelSpherical_hasCompactSupport F U hUc hf
  have hhc := MeasureAssembly.factorizable_continuous F hh
  have hhs := MeasureAssembly.factorizable_hasCompactSupport F hh
  rw [MeasureAssembly.rightConv_rightConv F φ f h hφ hfc hfs hhc hhs,
    MeasureAssembly.rightConv_rightConv F φ h f hφ hhc hhs hfc hfs,
    SliceCentrality.adelicKernel_comm F U hUK hUc hUo τ hirr hf hhc hht hhU]

end AutomorphicForm
