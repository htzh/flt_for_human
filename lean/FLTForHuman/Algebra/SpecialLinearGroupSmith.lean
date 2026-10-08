/-
  Smith-style diagonalisation of `!![a, b; 0, d]` over `SL₂(ℤ)`.

  This is the `Matrix.SpecialLinearGroup` leaf of row S: given `a * d = N` and
  `Nat.gcd a (Nat.gcd b d) = 1`, the upper-triangular matrix `!![a, b; 0, d]` is
  sandwiched between the diagonal Hecke matrix `!![N, 0; 0, 1]` and two explicit
  `SL₂(ℤ)` matrices.  Mathlib has no Smith normal form for `SL₂(ℤ)`, so the
  construction is the pin's.

  Pin source, `anthropics/fermats-last-theorem@aa2d8b3`:

    `P2M/Sol/S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean`
    (`Theorems/Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean`)

  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean>

  Mathlib supplies `IsCoprime`, `Nat.Coprime`, `Nat.Coprime.isCoprime`,
  `Matrix.SpecialLinearGroup`, `Matrix.det_fin_two_of` and `Matrix.mul_fin_two`;
  the three declarations below are transcribed from the pin.  This module is
  mathlib-only: it imports no `FLTForHuman` module.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

set_option autoImplicit false

open scoped Matrix

namespace Matrix.SpecialLinearGroup.PrimitiveSmith

/-- From `gcd a (gcd b d) = 1` with `d ≠ 0`, produce `p` with `a * p + b` coprime
to `d`: multiply `a` by the product of the primes dividing `d` but not `b`. -/
theorem exists_coprime_mul_add {a b d : ℕ} (hd : d ≠ 0) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ p : ℕ, Nat.Coprime (a * p + b) d := by
  classical
  refine ⟨∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ b), q, ?_⟩
  set P := ∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ b), q with hP
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro q hq hqd hqab
  have hqP : q ∣ P ↔ ¬ q ∣ b := by
    rw [hP]
    rw [Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq)]
    constructor
    · rintro ⟨q', hq', hqq'⟩
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq'
      obtain ⟨⟨hq'p, -, -⟩, hq'b⟩ := hq'
      rwa [(Nat.prime_dvd_prime_iff_eq hq hq'p).mp hqq']
    · intro hqb
      exact ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqd, hd⟩, hqb⟩, dvd_rfl⟩
  by_cases hqb : q ∣ b
  · have hqa : ¬ q ∣ a := by
      intro hqa
      have : q ∣ Nat.gcd a (Nat.gcd b d) := Nat.dvd_gcd hqa (Nat.dvd_gcd hqb hqd)
      rw [hgcd] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)
    have hqaP : q ∣ a * P := (Nat.dvd_add_right hqb).mp (by rwa [add_comm] at hqab)
    rcases (Nat.Prime.dvd_mul hq).mp hqaP with h | h
    · exact hqa h
    · exact (hqP.mp h) hqb
  · have hqP' : q ∣ a * P := Dvd.dvd.mul_left (hqP.mpr hqb) a
    exact hqb ((Nat.dvd_add_right hqP').mp hqab)

/-- The sandwich `!![a, b; 0, d] = γ₁ · !![N, 0; 0, 1] · γ₂` for two explicit
`SL₂(ℤ)` matrices, from a solution `(s, t)` of Bézout for `(a * p + b, d)`. -/
theorem main {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1]
        * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hd : d ≠ 0 := fun h0 => hN (by rw [← had, h0, mul_zero])
  obtain ⟨p, hp⟩ := exists_coprime_mul_add hd hgcd
  set u : ℤ := (a : ℤ) * p + b with hu
  have hcop : IsCoprime u (d : ℤ) := by
    rw [hu]
    have : ((a * p + b : ℕ) : ℤ) = (a : ℤ) * p + b := by push_cast; ring
    rw [← this, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hp
  obtain ⟨s, t, hst⟩ := hcop
  have hN' : (N : ℤ) = a * d := by exact_mod_cast had.symm
  refine ⟨⟨!![-t, -u; s, -(d : ℤ)], ?_⟩, ⟨!![-1, (p : ℤ); -s * a, (p : ℤ) * s * a - 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hst
  · rw [Matrix.det_fin_two_of]
    ring
  · rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hN']
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      linear_combination (-(a : ℤ)) * hst + ((a : ℤ) * s) * hu
    · simp
      linear_combination ((a : ℤ) * p) * hst - ((a : ℤ) * p * s) * hu
    · simp
      ring
    · simp
      ring

end Matrix.SpecialLinearGroup.PrimitiveSmith

namespace Matrix.SpecialLinearGroup

/-- Pin `Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one`. -/
theorem exists_eq_mul_diagonal_mul_of_gcd_eq_one
    {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) :=
  PrimitiveSmith.main hN had hgcd

end Matrix.SpecialLinearGroup
