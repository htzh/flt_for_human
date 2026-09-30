/-
  The property that the Frobenius powers at primes outside a finite set `S`
  meet every coset of a subgroup `H` of `Gal(ℚ̄/ℚ)`, formulated with the
  valuation-theoretic Frobenius `A.IsFrobeniusAt`.

  Transcribed verbatim from `Definitions/Def_GaloisRep_FrobeniusPowerDense.lean`
  (pinned `aa2d8b3`, 13 lines). The mathematics is math/018 §6.
-/
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import FLTForHuman.GaloisRep.Defs.Ramification
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

def FrobeniusPowerDense (S : Finset ℕ)
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H
