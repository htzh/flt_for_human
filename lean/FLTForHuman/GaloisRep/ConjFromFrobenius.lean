/-
  Equal Frobenius characteristic polynomials imply global conjugacy
  (Deligne–Serre S6c).

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean`,
  171 lines); its public target is the `Theorems/` wrapper
  `Thm_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean`.
  The mathematics is math/019 §4.

  The route: the kernel of a finite-level representation is open, so S7's
  `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` produces a prime
  `ℓ ∤ M` and a Frobenius `τ` with `g τ ^ n g⁻¹ = σ` modulo that kernel. Equal
  characteristic polynomials at Frobenius elements therefore give equal
  characteristic polynomials at *all* `σ` (a two-by-two Cayley–Hamilton power
  induction), and module 1
  (`Representation.exists_conj_eq_of_charpoly_eq_of_finite_range`) turns that into
  conjugacy.

  Imports module 1 (`RepConj.lean`), H1's `finite_range_of_factorsThroughFiniteLevel`
  (`GaloisRep/Prelude.lean`), the S7 density/dichotomy chain (`FrobeniusDensity.statement`,
  `statement_of_degOneAsymptotic`, `frobeniusPowerDense_of_le_ker`,
  `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`), and the ported
  `ValuationSubring.{LiesOverPrime,IsFrobeniusAt}` vocabulary. Helpers stay
  `private`; the only public declaration is the pin's target theorem.
-/
import FLTForHuman.GaloisRep.RepConj
import FLTForHuman.GaloisRep.Prelude
import FLTForHuman.GaloisRep.Defs.Ramification
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import FLTForHuman.NumberTheory.ValuationAtPlace
import FLTForHuman.NumberTheory.FrobeniusAtPlace
import FLTForHuman.NumberTheory.FrobeniusDensity.StatementOfDegOneAsymptotic
import FLTForHuman.NumberTheory.FrobeniusDensity.Statement
import FLTForHuman.NumberTheory.FrobeniusDensity.FrobeniusPowerDense
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeIsFrobeniusAtConjPow
import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's proof block introduces instances with `haveI` in `Prop` goals; it is
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/-- The kernel of a finite-level Galois representation is open. -/
private theorem isOpen_ker {M : Type} [Group M] (ρ : Γℚ →* M)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    IsOpen (ρ.ker : Set Γℚ) := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  have hle : L.fixingSubgroup ≤ ρ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact hker σ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x hx
  exact Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen L)

section powers

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Cayley–Hamilton for `2 × 2` matrices. -/
private theorem sq_eq_trace_smul_sub (A : Matrix (Fin 2) (Fin 2) R) :
    A ^ 2 = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have h := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two] at h
  simp only [map_add, map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h

  rw [← sub_eq_zero, ← h]
  abel

/-- The trace of the `n`-th power is determined by the trace and determinant. -/
private theorem trace_pow_eq_of_trace_eq_of_det_eq {A B : Matrix (Fin 2) (Fin 2) R}
    (htr : A.trace = B.trace) (hdet : A.det = B.det) : ∀ n : ℕ, (A ^ n).trace = (B ^ n).trace := by

  have hrec : ∀ (C : Matrix (Fin 2) (Fin 2) R) (n : ℕ),
      (C ^ (n + 2)).trace = C.trace * (C ^ (n + 1)).trace - C.det * (C ^ n).trace := by
    intro C n
    have : C ^ (n + 2) = C.trace • C ^ (n + 1) - C.det • C ^ n := by
      rw [pow_add, sq_eq_trace_smul_sub, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one,
        ← pow_succ]
    rw [this, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simpa using htr
    | (k + 2), ih =>
      rw [hrec A k, hrec B k, htr, hdet, ih (k + 1) (by omega), ih k (by omega)]

/-- Equal characteristic polynomials of `2 × 2` matrices give equal
characteristic polynomials of all powers. -/
private theorem charpoly_pow_eq_of_charpoly_eq {A B : Matrix (Fin 2) (Fin 2) R}
    (h : A.charpoly = B.charpoly) (n : ℕ) : (A ^ n).charpoly = (B ^ n).charpoly := by
  have htr : A.trace = B.trace := by
    have := congrArg (fun p : Polynomial R => p.coeff 1) h
    simp only [Matrix.charpoly_fin_two, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      Polynomial.coeff_C, ite_eq_right (show (1 : ℕ) ≠ 2 by decide),
      ite_eq_right (show (1 : ℕ) ≠ 0 by decide)] at this
    simpa using this
  have hdet : A.det = B.det := by
    have := congrArg (fun p : Polynomial R => p.coeff 0) h
    simp only [Matrix.charpoly_fin_two, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, ite_eq_right (show (0 : ℕ) ≠ 2 by decide)] at this
    simpa using this
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, trace_pow_eq_of_trace_eq_of_det_eq htr hdet n,
    Matrix.det_pow, Matrix.det_pow, hdet]

end powers

/-- The equality of characteristic polynomials extends from Frobenius elements to
all of `Γℚ`. -/
private theorem charpoly_eq_of_frobenius (ρ ρ' : Γℚ →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
            ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly)
    (σ : Γℚ) :
    ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly := by

  let H : Subgroup Γℚ := ρ.ker ⊓ ρ'.ker
  have hH : IsOpen (H : Set Γℚ) := (isOpen_ker ρ hρ).inter (isOpen_ker ρ' hρ')

  set M : ℕ := (S.sup id + 1).factorial with hM
  have hM0 : 0 < M := Nat.factorial_pos _
  have hSM : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S := by
    intro ℓ hℓ hℓM hℓS
    apply hℓM
    refine Nat.dvd_factorial hℓ.pos ?_
    exact (Finset.le_sup (f := id) hℓS).trans (Nat.le_succ _)
  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓM, hA, hτ, hmem⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen H hH σ hM0
  have hcp := h ℓ hℓ (hSM ℓ hℓ hℓM) A hA τ hτ

  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hmem
  rw [MonoidHom.mem_ker] at h1 h2
  have e1 : ρ σ = ρ g * ρ τ ^ n * (ρ g)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, mul_inv_eq_one] at h1
    exact h1.symm
  have e2 : ρ' σ = ρ' g * ρ' τ ^ n * (ρ' g)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, mul_inv_eq_one] at h2
    exact h2.symm
  have c1 : ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      (((ρ τ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ^ n).charpoly := by
    rw [e1, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Units.val_pow_eq_pow_val,
      Matrix.charpoly_units_conj]
  have c2 : ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      (((ρ' τ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ^ n).charpoly := by
    rw [e2, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Units.val_pow_eq_pow_val,
      Matrix.charpoly_units_conj]
  rw [c1, c2]
  exact charpoly_pow_eq_of_charpoly_eq hcp n

namespace GaloisRep

/-- Two complex `GL₂` Galois representations factoring through a finite level are
conjugate as soon as their characteristic polynomials agree at almost all
Frobenius elements. -/
theorem exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
    (ρ ρ' : Γℚ →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
            ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ σ : Γℚ, ρ' σ = P * ρ σ * P⁻¹ :=
  Representation.exists_conj_eq_of_charpoly_eq_of_finite_range ρ ρ'
    (finite_range_of_factorsThroughFiniteLevel ρ hρ)
    (finite_range_of_factorsThroughFiniteLevel ρ' hρ')
    (charpoly_eq_of_frobenius ρ ρ' hρ hρ' S h)

end GaloisRep
