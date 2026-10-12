/-
  The `principalLevel` right-convolution commutation headline.

  The `principalLevel` sibling of `Level.lean`: the same compact-headline application
  with `principalLevel N` in place of `levelOne N`. The level-`N` side facts come from
  the landed `AutomorphicForm.TestFnPrincipalLevel` vocabulary
  (`mem_principalLevel_iff_glFin`, `isOpen_finitePrincipalLevel`,
  `isCompact_finitePrincipalLevel`); `U = finEmbed '' finitePrincipalLevel F N` is again
  the frame separation plus the compact finite principal lattice.

  Statement verbatim from
  `Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_principal.lean`
  (pinned `aa2d8b3`); `hf` keeps the wrapper's `(productionPinsOf …).U N` spelling.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Compact
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.MeasureAssembly
import FLTForHuman.AutomorphicForm.Adelic.RightConvNeZeroPrincipal
import FLTForHuman.NumberTheory.AdelicLevel.PrincipalLevel
import Mathlib.Tactic

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

noncomputable section

namespace AutomorphicForm

theorem rightConv_rightConv_comm_of_isLevelSphericalOfType_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by
  have hpins : (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N
      = AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl
  have hU : IsCompact (((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [hpins]
    have himg : ((AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
            Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))
        = AdelicDock.finEmbed (𝓞 F) F '' (TestFnPrincipalLevel.finitePrincipalLevel F N :
            Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      ext u
      constructor
      · intro hu
        obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
        refine ⟨AdelicLevel.glFin (𝓞 F) F u,
          (TestFnPrincipalLevel.mem_principalLevel_iff_glFin (F := F) (N := N) u).mp hu1, ?_⟩
        apply ProjectedHaar.eq_of_glArch_eq_of_glFin_eq F
        · rw [AdelicDock.glArch_finEmbed]
          exact ((mem_finiteAdelicGL2Subgroup_iff F u).mp hu2).symm
        · exact AdelicDock.glFin_finEmbed (𝓞 F) F (AdelicLevel.glFin (𝓞 F) F u)
      · rintro ⟨b, hb, rfl⟩
        exact ⟨(TestFnPrincipalLevel.mem_principalLevel_iff_glFin (F := F) (N := N)
            (AdelicDock.finEmbed (𝓞 F) F b)).mpr (by rwa [AdelicDock.glFin_finEmbed]),
          (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F b)⟩
    rw [himg]
    exact (TestFnPrincipalLevel.isCompact_finitePrincipalLevel F N).image
      (ProjectedHaar.continuous_adelicFrame_ιf F)
  have hO : IsOpen ((AdelicLevel.principalLevel (𝓞 F) F N : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
    have hset : (AdelicLevel.principalLevel (𝓞 F) F N : Set (AdelicGL2 (𝓞 F) F))
        = AdelicLevel.glFin (𝓞 F) F ⁻¹' (TestFnPrincipalLevel.finitePrincipalLevel F N :
            Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      ext g
      rw [Set.mem_preimage]
      exact TestFnPrincipalLevel.mem_principalLevel_iff_glFin (F := F) (N := N) g
    rw [hset]
    exact (TestFnPrincipalLevel.isOpen_finitePrincipalLevel F hN).preimage
      (AdelicLevel.continuous_glFin (𝓞 F) F)
  exact rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact F
    ((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) hU
    (AdelicLevel.principalLevel (𝓞 F) F N) hO hpins
    τ hirr f hf h hh hht hhU φ hφ

end AutomorphicForm
