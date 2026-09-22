/-
Extras on top of mathlib's division polynomials that the FLT development needs
for the multiplication formula.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3`: the `ω`-specific parts of `PortEllSequenceCore` and the section
`PortEllSequenceDivisionPolys`. Ground rules and the dependency trace are in
`logs/card-torsion-port.md`.

mathlib v4.34.0 already ships the EDS core this rests on — `normEDS`,
`preNormEDS`, `complEDS`, `complEDS₂`, `atom`, `atomRel`, `rel` — and FLT's old
names map onto it one-for-one (`compl₂EDS` is *definitionally* `complEDS₂`, so
`ψc` below is just an alias). What mathlib dropped after v4.30 is the `ω`
division polynomial and its `redInvar`/`complEDSAux` scaffolding, and that is
what this module rebuilds.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence

open scoped Polynomial Polynomial.Bivariate
open Polynomial
open WeierstrassCurve

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable section

/-- `6X² + b₂X + b₄`. The identity `preΨ₄ + Ψ₂Sq² = invar * Ψ₃` is what makes the
`ω` construction go through. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The `2`-complement of the division polynomials, characterised by
`ψ n * ψc n = ψ (2n)`. This is FLT's `compl₂EDS`, which is definitionally
mathlib's `complEDS₂`. -/
def ψc (n : ℤ) : R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

/-- The defining property of the `2`-complement. In FLT this is
`ψc_spec`/`normEDS_mul_compl₂EDS`; here it is mathlib's
`normEDS_mul_complEDS₂` read through `WeierstrassCurve.ψ`. -/
lemma ψc_spec (n : ℤ) : W.ψ n * ψc W n = W.ψ (2 * n) :=
  normEDS_mul_complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

end

/-! ### The `ω` scaffolding

The `y`-coordinate of `n • P` needs an "invariant" `ω` whose denominator is
`redInvarDenom`. mathlib v4.34.0 has none of this; FLT builds it on the EDS
core (`normEDS`, `preNormEDS`, `complEDS₂`), which mathlib does have, so the
definitions port over directly. -/

section Sequence

variable (b c d : R)

/-- The numerator invariant of a sequence `u`, `invarNum u s n`. -/
def invarNum (u : ℤ → R) (s n : ℤ) : R :=
  (u (n + 2 * s) * u (n - s) ^ 2 + u (n + s) ^ 2 * u (n - 2 * s)) * u s ^ 2
    + u n ^ 3 * u (2 * s) ^ 2

/-- The denominator invariant of a sequence `u`, `invarDenom u s n`. -/
def invarDenom (u : ℤ → R) (s n : ℤ) : R := u (n + s) * u n * u (n - s)

lemma invarNum_normEDS (n : ℤ) :
    invarNum (normEDS b c d) 1 n =
      normEDS b c d (n + 2) * normEDS b c d (n - 1) ^ 2
        + normEDS b c d (n + 1) ^ 2 * normEDS b c d (n - 2)
        + normEDS b c d n ^ 3 * b ^ 2 := by
  simp [invarNum, normEDS_one, normEDS_two]

lemma invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]

lemma invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by
  simp [invarDenom]

/-- FLT's `compl₂EDSAux`: the `2`-complement auxiliary sequence. -/
def complEDSAux (m : ℤ) : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2
    * if Even m then 1 else b

@[simp] lemma complEDSAux_zero : complEDSAux b c d 0 = -1 := by simp [complEDSAux]
@[simp] lemma complEDSAux_one : complEDSAux b c d 1 = -b := by simp [complEDSAux]
@[simp] lemma complEDSAux_neg_one : complEDSAux b c d (-1) = 0 := by simp [complEDSAux]
@[simp] lemma complEDSAux_two : complEDSAux b c d 2 = 0 := by simp [complEDSAux]
@[simp] lemma complEDSAux_neg_two : complEDSAux b c d (-2) = -d := by simp [complEDSAux]

lemma complEDSAux_mul_b (m : ℤ) :
    complEDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [complEDSAux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]
  split_ifs <;> ring

/-- FLT's `redInvarNum`, written with mathlib's `complEDS₂` in place of
`compl₂EDS` (they are definitionally equal). -/
def redInvarNum (m : ℤ) : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDSAux b c d m

lemma complEDS₂_eq_redInvarNum_sub (m : ℤ) :
    complEDS₂ b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDSAux b c d m := by
  rw [redInvarNum]; ring

lemma invarNum_eq_redInvarNum_mul (m : ℤ) :
    invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b, complEDSAux_mul_b,
    invarNum_normEDS]
  ring

end Sequence

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_complEDSAux (b c d : R) (m : ℤ) :
    f (complEDSAux b c d m) = complEDSAux (f b) (f c) (f d) m := by
  have mp : ∀ n : ℤ, f (preNormEDS (b ^ 4) c d n) = preNormEDS (f b ^ 4) (f c) (f d) n :=
    fun n => by
      rw [show f b ^ 4 = f (b ^ 4) from (map_pow f b 4).symm]
      exact map_preNormEDS f (b ^ 4) c d n
  simp only [complEDSAux, map_mul, map_pow, map_one, apply_ite f, mp]

lemma map_redInvarNum (b c d : R) (m : ℤ) :
    f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n => map_normEDS f b c d n
  simp only [redInvarNum, map_add, map_mul, map_pow, map_ofNat, map_complEDS₂, mn,
    map_complEDSAux]

end Map

end FLTForHuman.Elliptic
