/-
  The weighted-Petersson pairing headline.

  The public statement of the pin ready node
  `AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain`,
  taken verbatim from its `Theorems/` wrapper and proved by the tier-3
  `AutomorphicForm.PeterssonSlabPairing.main` engine of `PeterssonSlabPairing.lean`, to which the
  SC1 covering (`AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre`,
  `Siegel/SlabCoveringTheorems.lean`) is supplied — exactly as the pin's `solution` does. This thin
  façade is the checker's wire; the engine stays tier 3 and is recorded in `spec/UNWIRED-PUBLIC.md`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrapper is
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSlabPairing
import FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabCoveringTheorems

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm

theorem exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (π π' : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π.toRawCentral)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral R')
    (s : ℝ)
    (hs : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      ‖((R'.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F x ^ s)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
          peterssonIntegral F s S x y) ∧
    peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 ∧
    (R.centralChar = R'.centralChar →
      (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
            Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
            peterssonIntegral F s S x y) ∧
      ∃ P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          P (fun z => x (z * g)) (fun z => y (z * g)) =
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y) ∧
        (∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
          P y y ≠ 0) ∧
        ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          P x y = peterssonIntegral F s S x y) := by
  have := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  exact PeterssonSlabPairing.main c u d₁ d₂ T π π' R R' hR' s hs α β hα hαβ S hSs hS
    fun a b ha =>
      exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov a b ha

end AutomorphicForm

end
