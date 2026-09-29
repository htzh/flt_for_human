/-
  The characteristic polynomial of an adic Galois representation interacts with
  the coefficients: base change along a local homomorphism `φ` maps the charpoly
  (`charpoly_baseChangeAlong`), and `IsEquiv`-isomorphic representations have
  equal charpolys at every Frobenius (`charpoly_eq_of_isEquiv`). These are the two
  bridges the surjection half of `R = T` consumes.

  Transcribed verbatim from `P2M/Sol/S_GaloisRepAdic_charpoly_baseChangeAlong.lean`
  and `P2M/Sol/S_GaloisRepAdic_charpoly_eq_of_isEquiv.lean` (pinned `aa2d8b3`,
  9 + 13 lines); the statements are the pin's `Theorems/` wrappers. The proofs are
  one-liners over mathlib's `LinearMap.charpoly_baseChange` and
  `LinearEquiv.charpoly_conj`. The mathematics is math/018 §1.5.
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import FLTForHuman.GaloisRep.Defs.Adic

set_option autoImplicit false

open Polynomial

theorem GaloisRepAdic.charpoly_baseChangeAlong {A : Type} [CommRing A] [IsLocalRing A]
    {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ := by
  let : Algebra A B := φ.toAlgebra
  exact LinearMap.charpoly_baseChange (ρ.ρ σ) B

theorem GaloisRepAdic.charpoly_eq_of_isEquiv {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by
  obtain ⟨e⟩ := h
  have hconj : ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.map_apply,
      LinearEquiv.apply_symm_apply]
  rw [hconj]
  exact (LinearEquiv.charpoly_conj e.toLinearEquiv (ρ₁.ρ σ)).symm
