/-
The complement multiplication property of the normalised EDS.

FLT proves `W m * compl W₁ compl₂ m n = W (n * m)` generically for its own
`compl`/`compl'` (`Def_WeierstrassCurve_EDSEngine.lean:799`), but mathlib's
`complEDS` is specialised to `normEDS`, so there is no generic complement to
state it against. Rather than re-introduce a duplicate complement sequence, this
module proves the specialised statement directly:

  `normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m)`

The induction is carried out for the universal EDS over `ℤ[B, C, D]`, where
`universalNormEDS m` is a non-zero-divisor for `m ≠ 0` and the cancellation in
the odd step is legitimate; the general statement follows by applying `aeval`.
-/
import FLTForHuman.Elliptic.EllSequence

open scoped Polynomial Polynomial.Bivariate
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve MvPolynomial

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R]

open MvPolynomial in
private lemma universalNormEDS_mul_complEDS {m : ℤ} (hm : m ≠ 0) (n : ℤ) :
    universalNormEDS m * complEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C)
        (X (R := ℤ) Param.D) m n = universalNormEDS (n * m) := by
  have hell : IsEllipticSequence (universalNormEDS : ℤ → MvPolynomial Param ℤ) :=
    normEDS_isEllipticSequence _ _ _
  have hnz : universalNormEDS m ≠ 0 := universalNormEDS_ne_zero hm
  have hu1 : universalNormEDS (1 : ℤ) = 1 := normEDS_one _ _ _
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _ | _ | j := n
    · simp [complEDS_zero, universalNormEDS, normEDS_zero]
    · simp [complEDS_one]
    obtain ⟨k, rfl | rfl⟩ := j.even_or_odd'
    · -- j = 2k, index 2*(k+1)
      rw [show ((2 * k + 2 : ℕ) : ℤ) = 2 * ((k + 1 : ℕ) : ℤ) by push_cast; ring]
      calc universalNormEDS m
            * complEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
              m (2 * ((k + 1 : ℕ) : ℤ))
          = universalNormEDS m
              * (complEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
                  m ((k + 1 : ℕ) : ℤ)
                * complEDS₂ (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
                    (((k + 1 : ℕ) : ℤ) * m)) := by rw [complEDS_even]
        _ = (universalNormEDS m
              * complEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
                  m ((k + 1 : ℕ) : ℤ))
            * complEDS₂ (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
                (((k + 1 : ℕ) : ℤ) * m) := by ring
        _ = universalNormEDS (((k + 1 : ℕ) : ℤ) * m)
            * complEDS₂ (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
                (((k + 1 : ℕ) : ℤ) * m) := by rw [ih (k + 1) (by omega)]
        _ = universalNormEDS (2 * (((k + 1 : ℕ) : ℤ) * m)) :=
              normEDS_mul_complEDS₂ _ _ _ _
        _ = universalNormEDS ((2 * ((k + 1 : ℕ) : ℤ)) * m) := by congr 1; ring
    · -- j = 2k+1, index 2*(k+1)+1
      rw [show ((2 * k + 1 + 2 : ℕ) : ℤ) = 2 * ((k : ℤ) + 1) + 1 by push_cast; ring]
      have h1 := ih (k + 1) (by omega)
      have h2 := ih (k + 2) (by omega)
      push_cast at h1 h2
      have hEDS'' : universalNormEDS m * universalNormEDS ((2 * ((k : ℤ) + 1) + 1) * m)
          = (universalNormEDS m) ^ 2
            * complEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)
              m (2 * ((k : ℤ) + 1) + 1) := by
        have hEDS := rel₃_of_isEllipticSequence hell (((k : ℤ) + 2) * m) (((k : ℤ) + 1) * m) 1
        simp only [Rel₃] at hEDS
        rw [show ((k : ℤ) + 2) * m + ((k : ℤ) + 1) * m = (2 * ((k : ℤ) + 1) + 1) * m by ring,
          show ((k : ℤ) + 2) * m - ((k : ℤ) + 1) * m = m by ring, hu1, one_pow,
          mul_one] at hEDS
        rw [← h1, ← h2] at hEDS
        rw [complEDS_odd]
        simp only [universalNormEDS, show ((k : ℤ) + 1 + 1) = (k : ℤ) + 2 by ring] at hEDS ⊢
        linear_combination hEDS
      refine mul_left_cancel₀ hnz ?_
      rw [← mul_assoc, ← sq]
      exact hEDS''.symm
  | neg ih n =>
    rw [neg_mul, complEDS_neg, mul_neg,
      show universalNormEDS (-(↑n * m)) = -universalNormEDS (↑n * m) from normEDS_neg _ _ _ _,
      ih n]

open MvPolynomial in
/-- The complement `complEDS` witnesses `normEDS m ∣ normEDS (n * m)`. -/
theorem normEDS_mul_complEDS (b c d : R) (m n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  obtain rfl | hm := eq_or_ne m 0
  · simp
  · rw [normEDS_eq_aeval (b := b) (c := c) (d := d),
      complEDS_eq_aeval (b := b) (c := c) (d := d), ← map_mul]
    congr 1
    exact universalNormEDS_mul_complEDS hm n

lemma normEDS_mul_complEDS_div (b c d : R) (m : ℤ) (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n := by
  obtain ⟨n, rfl⟩ := dvd
  rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]

end FLTForHuman.Elliptic
