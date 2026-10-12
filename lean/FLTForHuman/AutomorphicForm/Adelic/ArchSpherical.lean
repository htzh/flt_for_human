/-
  The archimedean spherical predicate.

  `IsArchSphericalOfType` is the archimedean factor of a level-spherical test
  function: an archimedean test factor, arch-bi-finite for the type family `tys`, and
  invariant under conjugation by the row-isometry subgroup at every infinite place.
  `IsLevelSphericalOfType` is the level-`N` spherical predicate: such an archimedean
  factor times the indicator of the level subgroup's finite image.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_ArchSpherical.lean`
  (pinned `aa2d8b3`, 66 lines / 7 declarations). The pin's stub imports are replaced
  by the port modules below; the pin namespace `AutomorphicForm` is kept. mathlib
  `v4.34.0` has no counterpart.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsArchSphericalOfType (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x

theorem isArchSphericalOfType_iff (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    IsArchSphericalOfType F tys fa ↔
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x := Iff.rfl

theorem isArchSphericalOfType_zero (tys : ArchTypeFamily F) : IsArchSphericalOfType F tys (fun _ => 0) :=
  ⟨isArchTestFactor_zero F, isArchFactorBiFinite_zero F tys, fun _ _ _ => rfl⟩

def IsLevelSphericalOfType (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
    IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
      Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
        (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)

theorem isLevelSphericalOfType_iff (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g) := Iff.rfl

theorem isLevelSphericalOfType_iff' (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchSphericalOfType F tys fa ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g) :=
  ⟨fun ⟨fa, h1, h2, h3, h4⟩ => ⟨fa, ⟨h1, h2, h3⟩, h4⟩, fun ⟨fa, ⟨h1, h2, h3⟩, h4⟩ => ⟨fa, h1, h2, h3, h4⟩⟩

theorem isLevelSphericalOfType_zero (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)) :
    IsLevelSphericalOfType F tys U (fun _ => 0) :=
  ⟨fun _ => 0, isArchTestFactor_zero F, isArchFactorBiFinite_zero F tys, fun _ _ _ => rfl,
    fun _ => (zero_mul _).symm⟩

end AutomorphicForm

end
