/-
  Frobenius power density from a kernel containment
  (`FrobeniusDensity.frobeniusPowerDense_of_le_ker`): if an open subgroup `H` of
  `Gal(ℚ̄/ℚ)` contains the restriction kernel of a finite Galois number field
  `F`, then the conjugates of Frobenius powers at primes outside `S` meet every
  coset of `H`.

  The proof applies `exists_frobenius_conj_pow_of_statement` to the image `L` of
  `F` in `ℚ̄` and converts the "fixed on `L`" conclusion into membership in the
  restriction kernel.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_frobeniusPowerDense_of_le_ker.lean`, 47 lines). The
  mathematics is math/019 §4.
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.Statement
import FLTForHuman.NumberTheory.FrobeniusDensity.ExistsFrobeniusConjPow
import FLTForHuman.NumberTheory.FrobeniusDensity.TaylorWilesPrimes
import FLTForHuman.GaloisRep.Defs.FrobeniusPowerDense
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.Galois.Basic

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped NumberField Pointwise

namespace FrobeniusDensity

theorem frobeniusPowerDense_of_le_ker (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) : FrobeniusPowerDense S H := by
  intro σ
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsScalarTower.toAlgHom ℚ F (AlgebraicClosure ℚ)
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := ι.fieldRange
  haveI : FiniteDimensional ℚ L := Module.Finite.equiv
    (((IntermediateField.topEquiv (F := ℚ) (E := F)).symm.trans (IntermediateField.equivMap ⊤ ι)).trans
      (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm)).toLinearEquiv
  have hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M :=
    fun M _ _ _ => FrobeniusDensity.statement M
  obtain ⟨ℓ, hℓ, hℓS, A, τ, γ, j, hA, hτ, hLfix⟩ :=
    FrobeniusDensity.exists_frobenius_conj_pow_of_statement hFD L σ S
  have hmemL : ∀ y : F, algebraMap F (AlgebraicClosure ℚ) y ∈ L := fun y =>
    AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩
  have hfixF : ∀ y : F, (γ * τ ^ j * γ⁻¹ * σ⁻¹) (algebraMap F (AlgebraicClosure ℚ) y)
      = algebraMap F (AlgebraicClosure ℚ) y := by
    intro y
    have hy' : σ⁻¹ (algebraMap F (AlgebraicClosure ℚ) y) ∈ L := by
      have := AlgEquiv.restrictNormal_commutes σ⁻¹ F y
      rw [← this]
      exact hmemL _
    have h := hLfix _ hy'
    rw [AlgEquiv.mul_apply, ← h, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  refine ⟨ℓ, A, τ, γ, j, hℓ, hℓS, hA, hτ, hker ?_⟩
  rw [MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro y
  apply (algebraMap F (AlgebraicClosure ℚ)).injective
  have hc := AlgEquiv.restrictNormal_commutes (γ * τ ^ j * γ⁻¹ * σ⁻¹) F y
  change algebraMap F (AlgebraicClosure ℚ) (((γ * τ ^ j * γ⁻¹ * σ⁻¹).restrictNormal F) y)
    = algebraMap F (AlgebraicClosure ℚ) ((1 : F ≃ₐ[ℚ] F) y)
  rw [AlgEquiv.one_apply, hc]
  exact hfixF y

end FrobeniusDensity
