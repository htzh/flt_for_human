/-
The reduced denominator `redInvarDenom` of the `ω` invariant.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3` (the `EllSequence` namespace inside `PortEllSequenceCore`). See
`logs/card-torsion-port.md`.

`redInvarDenom` is the denominator of the `y`-coordinate of `n • P` after
clearing the powers of the parameter `b = ψ₂` that `complEDS` leaves in
numerators; the identity `invarDenom (normEDS) 1 m = redInvarDenom m * b * c`
relates it to the naive invariant denominator.
-/
import FLTForHuman.Elliptic.Complement

open scoped Polynomial Polynomial.Bivariate
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R]

/-- `normEDS 6` in terms of `normEDS 5` and the parameter `d`. -/
lemma normEDS_six_eq_mul (b c d : R) :
    normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂_three,
    show normEDS b c d 5 = preNormEDS (b ^ 4) c d 5 by
      rw [normEDS, ite_eq_right (by decide), mul_one],
    normEDS_three]
  ring

/-- The `2`-complement of the identity EDS is constantly `2`. -/
lemma complEDS₂_two_three_two (n : ℤ) : complEDS₂ (2 : ℤ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact complEDS₂_zero ..
  · have h := normEDS_mul_complEDS₂ (2 : ℤ) 3 2 n
    rwa [normEDS_two_three_two, id_eq, id_eq, mul_comm,
      mul_cancel_right_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn)] at h

/-- FLT's `redInvarDenom`. -/
noncomputable def redInvarDenom (b c d : R) (m : ℤ) : R :=
  if m % 6 = 0 then (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (m / 6)
      * normEDS b c d (m + 1) * normEDS b c d (m - 1) else
  if m % 6 = 1 then (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m - 1) / 6)
      * normEDS b c d (m + 1) * normEDS b c d m else
  if m % 6 = 5 then (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m + 1) / 6)
      * normEDS b c d m * normEDS b c d (m - 1) else
  if m % 6 = 2 then complEDS b c d 3 ((m + 1) / 3) * complEDS b c d 2 (m / 2)
      * normEDS b c d (m - 1) else
  if m % 6 = 4 then complEDS b c d 3 ((m - 1) / 3) * complEDS b c d 2 (m / 2)
      * normEDS b c d (m + 1) else
  if m % 6 = 3 then complEDS b c d 3 (m / 3) * complEDS b c d 2 ((m - 1) / 2)
      * normEDS b c d (m + 1) else 0

lemma invarDenom_eq_redInvarDenom_mul (b c d : R) (m : ℤ) :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd (k m : ℤ) (dvd : k ∣ 6) (eq : m % 6 % k = 0) : k ∣ m :=
    Int.dvd_iff_emod_eq_zero.mpr ((Int.emod_emod_of_dvd m dvd).symm.trans eq)
  have hd2 {m : ℤ} := hd 2 m ⟨3, rfl⟩
  have hd3 {m : ℤ} := hd 3 m ⟨2, rfl⟩
  have dvd_sub {a b c : ℤ} (h : a % b = c) : b ∣ a - c := by
    rw [← h, Int.emod_def, sub_sub_cancel]
    exact dvd_mul_right _ _
  rw [invarDenom, redInvarDenom]; split_ifs with h h h h h h
  · rw [← normEDS_mul_complEDS_div b c d 6 h6 _ (Int.dvd_of_emod_eq_zero h),
      normEDS_six_eq_mul]; ring
  · rw [← normEDS_mul_complEDS_div b c d 6 h6 _ (dvd_sub h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel, ← normEDS_mul_complEDS_div b c d 6 h6,
      normEDS_six_eq_mul]; ring
    exact dvd_sub (show (m + 6) % 6 = 5 by omega)
  on_goal 1 => rw [← normEDS_mul_complEDS_div b c d 3 h3 _ (hd3 <| by simp [h, Int.add_emod]),
    ← normEDS_mul_complEDS_div b c d 2 two_ne_zero m (hd2 <| by simp [h])]
  on_goal 2 => rw [← normEDS_mul_complEDS_div b c d 3 h3 (m - 1) (hd3 <| by simp [h, Int.sub_emod]),
    ← normEDS_mul_complEDS_div b c d 2 two_ne_zero m (hd2 <| by simp [h])]
  on_goal 3 => rw [← normEDS_mul_complEDS_div b c d 3 h3 m (hd3 <| by simp [h]),
    ← normEDS_mul_complEDS_div b c d 2 two_ne_zero (m - 1) (hd2 <| by simp [h, Int.sub_emod])]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] lemma redInvarDenom_zero (b c d : R) : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom, complEDS_zero]

@[simp] lemma redInvarDenom_one (b c d : R) : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom, complEDS_zero]

@[simp] lemma redInvarDenom_two (b c d : R) : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom, complEDS_one, normEDS_one]

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_redInvarDenom (b c d : R) (m : ℤ) :
    f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n => map_normEDS f b c d n
  simp only [redInvarDenom, apply_ite f, mn, map_complEDS, map_sub, map_pow, map_mul, map_zero]

end Map

end FLTForHuman.Elliptic
