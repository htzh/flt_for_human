/-
  Consumer specification for the T-side definition layer (TOPIC-t11, SET E).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the twelve definition modules of the T side. Each zone
  below is a real proof term that composes at least two of the new modules, so an
  unwired module fails to elaborate here — the deliverable measure is the error
  count. It is deliberately **not part of any library** (nothing globs `spec/`),
  so it can never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideConsumer.lean 2>&1 | grep -c error

  ZONES
  -----
  * `[residual]`   — `residualGaloisRepOf` (`Residual`) with `Equiv`/`IsEquiv`/
                     `baseChangeAlong` (`ResidualEquiv`), over the Weierstrass
                     vocabulary (`Modularity`, `FreyPackage`, `Ramification`,
                     `GaloisAction`, `FrobeniusTrace`).
  * `[adic]`       — an adic representation, its `residual` (`Adic`), the
                     residual `IsAbsolutelyIrreducible` (`Residual`) and
                     `Equiv.residual` (`Adic`) read through `IsEquiv`.
  * `[deformation]`— a `GaloisRep.DeformationRingData` and its `universal` field
                     at a test algebra, composed with the residual vocabulary.
  * `[hecke]`      — `HeckeGaloisRepDatum` over `CuspForm.heckeLocal` exposing
                     `charpoly_frob`, the three algebra facts (`FiniteAlgebraComplete`)
                     and an `Algebra.PatchingLevel` instantiation.
-/
import FLTForHuman.Patching.Defs.PatchingDatum
import FLTForHuman.WeierstrassCurve.Defs.Modularity
import FLTForHuman.WeierstrassCurve.Defs.FreyPackage
import FLTForHuman.GaloisRep.Defs.GaloisAction
import FLTForHuman.GaloisRep.Defs.Ramification
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import FLTForHuman.GaloisRep.Defs.Residual
import FLTForHuman.GaloisRep.Defs.ResidualEquiv
import FLTForHuman.GaloisRep.Defs.Adic
import FLTForHuman.GaloisRep.Defs.DeformationRingData
import FLTForHuman.Algebra.FiniteAlgebraComplete
import FLTForHuman.HeckeGalois.Defs.HeckeGaloisRepDatum
import FLTForHuman.HeckeGalois.Defs.HeckeLocal

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine TensorProduct

/-! ## Zone `[residual]` — the `p`-torsion representation and its isomorphisms -/

namespace TsideResidual

open WeierstrassCurve

variable (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
  (hker : GaloisFactorsThroughFiniteLevel
    (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p))

-- The a priori residual representation of `E[p]` (Residual), and its `IsEquiv`
-- reflexivity (ResidualEquiv).
example : ResidualGaloisRep.IsEquiv
    (WeierstrassCurve.residualGaloisRepOf W p hcard hker)
    (WeierstrassCurve.residualGaloisRepOf W p hcard hker) :=
  ⟨ResidualGaloisRep.Equiv.refl _⟩

-- Base change along a residue-field endomorphism (ResidualEquiv), applied to the
-- representation built by `residualGaloisRepOf` (Residual), then inverted and
-- recomposed: the groupoid laws run on a concrete object of the new modules.
example (φ : ZMod p →+* ZMod p) : ResidualGaloisRep.IsEquiv
    ((WeierstrassCurve.residualGaloisRepOf W p hcard hker).baseChangeAlong φ)
    ((WeierstrassCurve.residualGaloisRepOf W p hcard hker).baseChangeAlong φ) :=
  ⟨((ResidualGaloisRep.Equiv.refl _).baseChangeAlong φ).symm.trans
    ((ResidualGaloisRep.Equiv.refl _).baseChangeAlong φ)⟩

-- The Weierstrass point-action layer (GaloisAction) feeding the representation:
-- a Galois translate of an `n`-torsion point is again `n`-torsion.
example {R S K : Type} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (W' : WeierstrassCurve.Affine R) {n : ℕ} (σ : K ≃ₐ[S] K) {P : (W'⁄K).Point}
    (hP : P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n) :
    σ • P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n :=
  WeierstrassCurve.Affine.Point.smul_mem_torsionBy σ hP

-- The trace of Frobenius on torsion (FrobeniusTrace) unfolds to the linear trace
-- of the representation (GaloisAction).
example {R S K : Type} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (W' : WeierstrassCurve.Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) :
    WeierstrassCurve.Affine.Point.galoisTrace S W' n σ =
      LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (WeierstrassCurve.Affine.Point.galoisRepModuleEnd S W' n σ) :=
  WeierstrassCurve.Affine.Point.galoisTrace_def (S := S) W' n σ

-- `IsFrobeniusAt` (FrobeniusTrace) gives back the decomposition-group membership
-- it was built from.
example {K L : Type} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (σ : L ≃ₐ[K] L) (q : ℕ) (h : A.IsFrobeniusAt σ q) :
    σ ∈ A.decompositionSubgroup K :=
  h.mem_decompositionSubgroup

-- The modularity predicates (Modularity) are definitions over a normalized
-- eigenform (the already-ported `Defs/Eigenform`), not new data.
example (W : WeierstrassCurve ℤ) (h : W.IsModularModel) :
    ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N :=
  h

-- The Frey package (FreyPackage) and its unramified predicate (Ramification)
-- are the same statement for the package and for its Frey curve.
example (P : FreyPackage) (h : FreyPackage.GaloisRepUnramifiedAt P P.p) :
    WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
      P.freyCurve P.p P.p :=
  h

end TsideResidual

/-! ## Zone `[adic]` — adic representations, their reductions and irreducibility -/

namespace TsideAdic

variable (A : Type) [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)

-- The residual representation `ρ mod 𝔪` (Adic) is absolutely irreducible
-- (Residual) exactly when its base change to the algebraic closure is
-- irreducible; the proof is the definition's unfolding.
example (h : ρ.residual.IsAbsolutelyIrreducible) :
    (ρ.residual.baseChange (AlgebraicClosure (IsLocalRing.ResidueField A))).IsIrreducible :=
  h

-- An adic isomorphism (Adic) yields, through `Equiv.residual`, an isomorphism of
-- the reductions, which `ResidualGaloisRep.IsEquiv` (ResidualEquiv) reads.
example (ρ₁ ρ₂ : GaloisRepAdic A) (e : GaloisRepAdic.Equiv ρ₁ ρ₂) :
    ResidualGaloisRep.IsEquiv ρ₁.residual ρ₂.residual :=
  ⟨e.residual⟩

end TsideAdic

/-! ## Zone `[deformation]` — the universal deformation ring and its property -/

namespace TsideDeformation

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

-- The universal property of `R` (DeformationRingData), projected at a test
-- algebra `A`: this mentions the residual isomorphisms of `Residual`/
-- `ResidualEquiv` and the adic representations of `Adic`.
example (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (h𝒟 : 𝒟 ρA)
    (hρ : ρA.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A)))) :
    ∃! φ : D.R →ₐ[𝒪] A, ∃ hφ : IsLocalHom (φ : D.R →+* A),
      (D.ρ.baseChangeAlong (φ : D.R →+* A) hφ).IsEquiv ρA :=
  D.universal A hres ρA h𝒟 hρ

end TsideDeformation

/-! ## Zone `[hecke]` — the T package over the local Hecke algebra, and patching -/

namespace TsideHecke

open Polynomial

variable (N : ℕ) [NeZero N] (S : Set ℕ)
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
  [Fact (CuspForm.HasIntegralStructure N 2)]

-- The T package (HeckeGaloisRepDatum) instantiated over the local Hecke algebra
-- `T_θ` (HeckeLocal): `charpoly_frob` is exposed at `π (T_ℓ)`.
example (D : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ (CuspForm.heckeLocal N S 𝒪 θ))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.charpoly (D.ρ.ρ σ) =
      Polynomial.X ^ 2 - Polynomial.C (D.π (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * Polynomial.X
        + Polynomial.C ((ℓ : CuspForm.heckeLocal N S 𝒪 θ)) :=
  D.charpoly_frob ℓ hℓ hℓN hℓS A hA σ hσ

-- The local Hecke algebra's own instances: local, complete and local-hom, all
-- requiring `HasIntegralStructure` (HeckeLocal) and resting on the algebra
-- cluster (FiniteAlgebraComplete) for adic completeness.
example : IsLocalRing (CuspForm.heckeLocal N S 𝒪 θ) := inferInstance

example : IsLocalHom (algebraMap 𝒪 (CuspForm.heckeLocal N S 𝒪 θ)) := inferInstance

example : IsAdicComplete (IsLocalRing.maximalIdeal (CuspForm.heckeLocal N S 𝒪 θ))
    (CuspForm.heckeLocal N S 𝒪 θ) := inferInstance

-- The datum's residue compatibility (`D.π` reduces to `θ`) is the other face of
-- the same `T_θ` the previous example lives over.
example (D : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ (CuspForm.heckeLocal N S 𝒪 θ))
    (t : CuspForm.heckeAlgebra N 2 S) :
    IsLocalRing.residue (CuspForm.heckeLocal N S 𝒪 θ) (D.π t) =
      IsLocalRing.ResidueField.map
        (algebraMap 𝒪 (CuspForm.heckeLocal N S 𝒪 θ)) (θ t) :=
  D.residue_π t

-- The three algebra facts (FiniteAlgebraComplete) at a test module: the first is
-- the input the `heckeLocal` completeness instance consumes.
example (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M :=
  IsAdicComplete.of_module_finite I M

end TsideHecke

namespace TsidePatching

-- A patching level (PatchingDatum) at `r = 0`: the power-series ring on no
-- variables is the base ring itself, so the presentation is trivial, but every
-- field is discharged and the structure is genuinely instantiated.
example (𝒪 : Type) [CommRing 𝒪] :
    Algebra.PatchingLevel 𝒪 0 (MvPowerSeries (Fin 0) 𝒪) (MvPowerSeries (Fin 0) 𝒪)
      (⊥ : Ideal (MvPowerSeries (Fin 0) 𝒪)) :=
  { N := MvPowerSeries (Fin 0) 𝒪
    φ := AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)
    ψ := AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)
    ψ_surjective := Function.surjective_id
    ψ_φ_X := fun i => i.elim0
    π := AddMonoidHom.id (MvPowerSeries (Fin 0) 𝒪)
    π_smul := fun f x => rfl
    π_surjective := Function.surjective_id
    ker_π := fun x => by simp
    d := 1
    b := fun _ => 1
    b_span := fun x => ⟨fun _ => x, by simp⟩
    b_rel := fun c => by simp }

end TsidePatching

end
