/-
  Unit-factorizable test functions of a prescribed archimedean type.

  This is the whole pin node `Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean`
  (pinned `aa2d8b3`, 77 lines / 9 declarations), transcribed at the pin's names in
  namespace `AutomorphicForm`: `IsUnitFactorizableOfTypeAt` is
  `IsUnitFactorizableAt` plus `IsArchBiFinite`, with its projections, monotonicity in
  the subgroup and in the archimedean type family, and the zero/indicator instances.
  It is the base layer that `TwistedOrbital`'s `IsUnitFactorizableAboveOfType`
  (the trio's gate) refines.

  ## Substitutions against mathlib `v4.34.0`

  * No declaration of this pin node is replaced by a mathlib declaration: mathlib has
    no counterpart of `IsUnitFactorizableOfTypeAt`.
  * The supporting declarations are imported, not re-declared: `IsUnitFactorizableAt`,
    `IsUnitFactorizableAt.mono`, `IsUnitFactorizableAt.isFactorizableTestFn`,
    `isUnitFactorizableAt_zero` and `isUnitFactorizableAt_mul_indicator_unitFinSet`
    from `AutomorphicForm/Adelic/LocalOrbitalBase.lean`; `IsArchBiFinite`,
    `ArchTypeFamily`, `ArchTypeFamily.IsContainedIn`, `IsArchBiFinite.mono`,
    `IsArchBiFinite.of_factorization`, `IsArchFactorBiFinite` and
    `isArchBiFinite_zero` from `AutomorphicForm/Adelic/IsotypicCuspSpace.lean`.
  * the pin's bare `import Mathlib` is replaced by the explicit imports below.
-/
import FLTForHuman.AutomorphicForm.Adelic.LocalOrbitalBase
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace

set_option autoImplicit false


open NumberField IsDedekindDomain

namespace AutomorphicForm

section TierRefined

variable (K : Type) [Field K] [NumberField K]

-- pin: IsUnitFactorizableOfTypeAt (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:14)
def IsUnitFactorizableOfTypeAt (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsUnitFactorizableAt K U S f ∧ IsArchBiFinite K tys f

variable {K}

-- pin: IsUnitFactorizableOfTypeAt.isUnitFactorizableAt (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:21)
theorem IsUnitFactorizableOfTypeAt.isUnitFactorizableAt {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsUnitFactorizableAt K U S f :=
  hf.1

-- pin: IsUnitFactorizableOfTypeAt.isArchBiFinite (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:27)
theorem IsUnitFactorizableOfTypeAt.isArchBiFinite {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsArchBiFinite K tys f :=
  hf.2

-- pin: IsUnitFactorizableOfTypeAt.isFactorizableTestFn (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:33)
theorem IsUnitFactorizableOfTypeAt.isFactorizableTestFn {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsFactorizableTestFn K f :=
  hf.1.isFactorizableTestFn K

-- pin: IsUnitFactorizableOfTypeAt.mono (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:39)
theorem IsUnitFactorizableOfTypeAt.mono {tys : ArchTypeFamily K}
    {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys V S f) : IsUnitFactorizableOfTypeAt K tys U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩

-- pin: IsUnitFactorizableOfTypeAt.mono_type (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:45)
theorem IsUnitFactorizableOfTypeAt.mono_type {tys tys' : ArchTypeFamily K}
    (h : tys.IsContainedIn K tys') {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys U S f) : IsUnitFactorizableOfTypeAt K tys' U S f :=
  ⟨hf.1, hf.2.mono K h⟩

-- pin: IsUnitFactorizableAt.isUnitFactorizableOfTypeAt_of_factorization (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:51)
theorem IsUnitFactorizableAt.isUnitFactorizableOfTypeAt_of_factorization {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableAt K U S f)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hfac : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
    (hfa : IsArchFactorBiFinite K tys fa) : IsUnitFactorizableOfTypeAt K tys U S f :=
  ⟨hf, IsArchBiFinite.of_factorization K hfac hfa⟩

variable (K)

-- pin: isUnitFactorizableOfTypeAt_zero (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:61)
theorem isUnitFactorizableOfTypeAt_zero (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableOfTypeAt K tys U S fun _ => 0 :=
  ⟨isUnitFactorizableAt_zero K U S, isArchBiFinite_zero K tys⟩

-- pin: isUnitFactorizableOfTypeAt_mul_indicator_unitFinSet (Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean:66)
theorem isUnitFactorizableOfTypeAt_mul_indicator_unitFinSet (tys : ArchTypeFamily K)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (hfa' : IsArchFactorBiFinite K tys fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableOfTypeAt K tys U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) :=
  (isUnitFactorizableAt_mul_indicator_unitFinSet K hfa hU S).isUnitFactorizableOfTypeAt_of_factorization
    (fun _ => rfl) hfa'

end TierRefined

end AutomorphicForm
