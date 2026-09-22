/-
The full net property for `normEDS` and the invariant identities that follow.

`net_normEDS` upgrades round 5's `IsEllipticSequence (normEDS b c d)` (the
`s = 0` slice) to mathlib's `IsEllipticNet`. `invar_normEDS` and
`invar₂_normEDS` are FLT's `invar_normEDS` / `invar₂_normEDS`, the latter proved
by specialising to the universal EDS where `b` is a non-zero-divisor.
-/
import FLTForHuman.Elliptic.RedInvar

open scoped Polynomial Polynomial.Bivariate
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R]

open MvPolynomial in
/-- `normEDS` satisfies the full net property `rel = 0`. -/
lemma net_normEDS (b c d : R) (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 := by
  rw [normEDS_eq_aeval]
  change IsEllipticNet.rel
    ((MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d)) ∘ universalNormEDS)
    p q r s = 0
  rw [← IsEllipticNet.map_rel]
  rw [show IsEllipticNet.rel (universalNormEDS) p q r s = 0 from
    net_of_isEllipticSequence (normEDS_isEllipticSequence
        (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D))
      (mem_nonZeroDivisors_of_ne_zero (by
        rw [normEDS_one (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)]
        exact one_ne_zero))
      (mem_nonZeroDivisors_of_ne_zero (by
        rw [normEDS_two (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)]
        exact MvPolynomial.X_ne_zero _)) p q r s,
    map_zero]

/-- FLT's `invar_normEDS`. -/
lemma invar_normEDS (b c d : R) (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net (fun p q r s => net_normEDS b c d p q r s) s m n

private lemma invar₂_normEDS_of_mem_nonZeroDivisors {b : R} (hb : b ∈ R⁰) (c d : R) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc,
    mul_comm (invarDenom _ _ _)]
  convert invar_normEDS b c d 1 m 2 <;>
    simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

open MvPolynomial Param in
/-- FLT's `invar₂_normEDS`. -/
lemma invar₂_normEDS (b c d : R) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have h := invar₂_normEDS_of_mem_nonZeroDivisors
    (c := X (R := ℤ) Param.C) (d := X (R := ℤ) Param.D)
    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.B)) m
  have key : ∀ x : ℤ, (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (universalNormEDS x) = normEDS b c d x := by
    intro x
    show (fun y : ℤ => (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (universalNormEDS y)) x = normEDS b c d x
    rw [← normEDS_eq_aeval]
  have hnum : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (invarNum (normEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)) 1 m)
      = invarNum (normEDS b c d) 1 m := by
    change (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (invarNum universalNormEDS 1 m) = invarNum (normEDS b c d) 1 m
    simp only [invarNum, map_add, map_mul, map_pow, key]
  have hden : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (invarDenom (normEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)) 1 m)
      = invarDenom (normEDS b c d) 1 m := by
    change (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (invarDenom universalNormEDS 1 m) = invarDenom (normEDS b c d) 1 m
    simp only [invarDenom, map_mul, key]
  have := congr(MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d) $h)
  simp only [map_mul, map_add, map_pow, MvPolynomial.aeval_X] at this
  rw [hnum, hden] at this
  exact this

open MvPolynomial Param in
lemma aeval_universal_X (b c d : R) (s : Param) :
    ((MvPolynomial.aeval (R := ℤ) (Param.rec (motive := fun _ => R) b c d) :
        MvPolynomial Param ℤ →+* R)) (MvPolynomial.X (R := ℤ) s)
      = Param.rec (motive := fun _ => R) b c d s :=
  MvPolynomial.aeval_X _ _

private lemma redInvar_normEDS_of_mem_nonZeroDivisors {b : R} (hb : b ∈ R⁰) {c : R} (hc : c ∈ R⁰)
    (d : R) (m : ℤ) : redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
  ring

open MvPolynomial Param in
/-- FLT's `redInvar_normEDS`. -/
lemma redInvar_normEDS (b c d : R) (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have h := redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) Param.B) (c := X (R := ℤ) Param.C) (d := X (R := ℤ) Param.D)
    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.B))
    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.C)) m
  have hnum : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (redInvarNum (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m)
      = redInvarNum b c d m := by
    have h' := map_redInvarNum (R := MvPolynomial Param ℤ) (S := R)
      ((MvPolynomial.aeval (R := ℤ) (Param.rec (motive := fun _ => R) b c d) :
        MvPolynomial Param ℤ →+* R))
      (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m
    simpa only [AlgHom.coe_toRingHom, aeval_universal_X] using h'
  have hden : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (redInvarDenom (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m)
      = redInvarDenom b c d m := by
    have h' := map_redInvarDenom (R := MvPolynomial Param ℤ) (S := R)
      ((MvPolynomial.aeval (R := ℤ) (Param.rec (motive := fun _ => R) b c d) :
        MvPolynomial Param ℤ →+* R))
      (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m
    simpa only [AlgHom.coe_toRingHom, aeval_universal_X] using h'
  have hpow : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))
      (X (R := ℤ) Param.D + (X (R := ℤ) Param.B) ^ 4) = d + b ^ 4 := by
    simp only [map_add, map_pow, MvPolynomial.aeval_X]
  have := congr(MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d) $h)
  simp only [map_mul] at this
  rw [hnum, hden, hpow] at this
  exact this

end FLTForHuman.Elliptic
