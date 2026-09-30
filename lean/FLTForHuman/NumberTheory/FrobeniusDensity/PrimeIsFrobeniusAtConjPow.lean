/-
  Frobenius elements in an open subgroup
  (`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`): for every open
  subgroup `H` of `Gal(ℚ̄/ℚ)`, every `σ` and every `M > 0`, there is a place `A`
  over a prime `ℓ ∤ M` whose Frobenius `τ` satisfies
  `g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H`.

  The proof picks the finite Galois number field `F` whose restriction kernel
  lies in `H` (`IsOpen.exists_numberField_ker_restrictNormalHom_le`) and applies
  `FrobeniusDensity.frobeniusPowerDense_of_le_ker` with the finite set
  `M.primeFactors`.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen.lean`,
  28 lines). The mathematics is math/020 §4.
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.KerRestrictNormalHom
import FLTForHuman.NumberTheory.FrobeniusDensity.FrobeniusPowerDense
import FLTForHuman.NumberTheory.FrobeniusDensity.TaylorWilesPrimes
import Mathlib.Data.Nat.PrimeFin

set_option autoImplicit false

-- The pin's proofs introduce instances with `letI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped NumberField Pointwise

namespace Subgroup

theorem exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H := by

  obtain ⟨F, hF, hNF, hGal, hAlg, hST, hker⟩ :=
    hH.exists_numberField_ker_restrictNormalHom_le
  letI := hF; letI := hNF; letI := hGal; letI := hAlg; letI := hST

  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS, hA, hτ, hmem⟩ :=
    FrobeniusDensity.frobeniusPowerDense_of_le_ker F hker M.primeFactors σ

  exact ⟨ℓ, A, τ, g, n, hℓ,
    fun hdvd => hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hM.ne'⟩),
    hA, hτ, hmem⟩

end Subgroup
