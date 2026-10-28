/-
The residual-realization predicate and the cyclotomic-determinant predicate, the
definition layer of the `ModularCurve` residual-realization row (MC-5 / story M7):
`ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite`.

Transcribed verbatim from FLT's `Definitions/Def_ModularCurve_ResidualRealization.lean`
(pinned `aa2d8b3`, 54 lines), whole: the two declarations the pin has.
`IsResidualRealization` is the pin's `structure … : Prop` carrier of a
two-dimensional residual representation read off a `HeckeAlg`-module `J` of a
`K`-Galois extension `L`; `CyclotomicDeterminant` is the cyclotomic-determinant
condition on a Galois representation.

The pin's imports map to the port as: `Def_HeckeGalois_EichlerShimura` →
`ModularCurve/Defs/HeckeModule.lean` (`HeckeAlg`), `Def_FLTPrelim_Ramification` →
`GaloisRep/Defs/Ramification.lean` (`ValuationSubring.LiesOverPrime`),
`Def_EllipticCurve_FrobeniusTrace` → `GaloisRep/Defs/FrobeniusTrace.lean`
(`ValuationSubring.IsFrobeniusAt`).

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ResidualRealization.lean

spec-pin: Definitions/Def_ModularCurve_ResidualRealization.lean
-/
import FLTForHuman.ModularCurve.Defs.HeckeModule
import FLTForHuman.GaloisRep.Defs.Ramification
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ResidualRealization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

/-- A residual realization of the mod-`p` Hecke module `J` in the two-dimensional
`k`-vector space `V`: the `p`-torsion of `J` maps `k`-linearly onto `V`, the map
intertwines the Galois action through `ρ` and the Hecke action through `φ`. -/
structure IsResidualRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, p • x = 0 → p • y = 0 → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), p • x = 0 → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), p • x = 0 → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | p • x = 0}) = ⊤

end ResidualRealization

section Determinant

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The cyclotomic-determinant condition: at every unramified prime `ℓ ∤ N p`, the
determinant of the Frobenius at `ℓ` is `ℓ`. -/
def CyclotomicDeterminant (N p : ℕ) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V)) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        LinearMap.det (ρ σ).toLinearMap = (ℓ : k)

end Determinant

end ModularCurve

end
