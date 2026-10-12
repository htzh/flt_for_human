/-
  The level-`N` right-convolution commutation headline.

  The level-`N` specialization of the compact headline: with the level subgroup
  `U := (productionPinsOf …).U N = levelOne N ⊓ finiteAdelicGL2Subgroup F` (by `rfl`),
  `O := levelOne N`, `hO` from `AdelicLevel.isOpen_levelOne`, and `hU` from
  `U = finEmbed '' finiteLevelOne N` (the finite lattice is compact, and `finEmbed` is
  continuous) together with the frame separation
  `ProjectedHaar.eq_of_glArch_eq_of_glFin_eq`, the compact headline applies directly.
  This is the P0 scout's route (`lean/tmp/P-scout.lean`), not a transcription of the
  plain silo's `solution`.

  Statement verbatim from
  `Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean`
  (pinned `aa2d8b3`); `hf` keeps the wrapper's `(productionPinsOf …).U N` spelling.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Compact
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

theorem rightConv_rightConv_comm_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by
  have hpins : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N
      = AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl
  have hU : IsCompact (((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [hpins]
    have himg : ((AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
            Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))
        = AdelicDock.finEmbed (𝓞 F) F '' (AdelicLevel.finiteLevelOne (𝓞 F) F N :
            Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      ext u
      constructor
      · intro hu
        obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
        refine ⟨AdelicLevel.glFin (𝓞 F) F u, AdelicLevel.mem_levelOne_iff.mp hu1, ?_⟩
        apply ProjectedHaar.eq_of_glArch_eq_of_glFin_eq F
        · rw [AdelicDock.glArch_finEmbed]
          exact ((mem_finiteAdelicGL2Subgroup_iff F u).mp hu2).symm
        · exact AdelicDock.glFin_finEmbed (𝓞 F) F (AdelicLevel.glFin (𝓞 F) F u)
      · rintro ⟨b, hb, rfl⟩
        exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F b).mpr hb,
          (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F b)⟩
    rw [himg]
    exact (AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N).image (ProjectedHaar.continuous_adelicFrame_ιf F)
  exact rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact F
    ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) hU
    (AdelicLevel.levelOne (𝓞 F) F N) (AdelicLevel.isOpen_levelOne (𝓞 F) F hN) hpins
    τ hirr f hf h hh hht hhU φ hφ

end AutomorphicForm
