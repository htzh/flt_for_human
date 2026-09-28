/-
  Hecke–Galois data: the T package `CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T`.

  It equips a candidate `T` with the structure map `π : 𝕋 → T` reducing to `θ`,
  generation of `T` over `𝒪` by the Hecke operators, the localisation property
  `exists_point`, a Galois representation `ρ : GaloisRepAdic T`, the
  Eichler–Shimura characteristic-polynomial identity `charpoly_frob`
  (`charpoly(ρ(Frob_ℓ)) = X² − π(T_ℓ) X + ℓ`), and absolute irreducibility of the
  residual representation. It is deliberately stated without mentioning `R`, so
  it can instantiate both `T = T_θ` and the abstract case of the universal
  property.

  Transcribed verbatim from `Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean`
  (pinned `aa2d8b3`, 38 lines). The Hecke algebra it consumes is the already
  ported `CuspForm.heckeAlgebra` (`ModularForms/HeckeAlgebra.lean`). The
  mathematics is math/018 §4.
-/
import FLTForHuman.GaloisRep.Defs.Adic
import FLTForHuman.ModularForms.HeckeAlgebra

set_option autoImplicit false

open Polynomial

namespace CuspForm

structure HeckeGaloisRepDatum (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T] : Type 1 where

  π : heckeAlgebra N 2 S →+* T

  residue_π : ∀ t : heckeAlgebra N 2 S,
    IsLocalRing.residue T (π t) = IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)

  adjoin_range_π : Algebra.adjoin 𝒪 (Set.range π) = ⊤

  exists_point : ∀ χ : heckeAlgebra N 2 S →+* 𝒪,
    (∀ t : heckeAlgebra N 2 S, IsLocalRing.residue 𝒪 (χ t) = θ t) →
      ∃ ψ : T →ₐ[𝒪] 𝒪, ∀ t : heckeAlgebra N 2 S, ψ (π t) = χ t

  residue_surjective : Function.Surjective (IsLocalRing.residue T ∘ algebraMap 𝒪 T)

  ρ : GaloisRepAdic T

  charpoly_frob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (π (heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : T))

  residual_absIrr : ρ.residual.IsAbsolutelyIrreducible

end CuspForm
