/-
The `y`-coordinate invariant `ωe` of the multiplication formula.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3` (section `PortEllSequenceDivisionPolys`). See `logs/card-torsion-port.md`.

`ωe n` is the numerator of the `y`-coordinate of `n • P`: `y(nP) = ω_n / ψ_n³`.
Its definition is arranged so that `2 * ωe n + a₁ φ n ψ n + a₃ ψ n³ = ψc n`
holds in every characteristic, which is why it is built from `redInvarDenom` and
`complEDSAux` rather than by dividing by `2`.
-/
import FLTForHuman.Elliptic.Net

open scoped Polynomial Polynomial.Bivariate
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine (polynomial polynomialY polynomialX negPolynomial)

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

noncomputable section

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]
  C_simp; ring

lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = invar W * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (invar W * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]
  C_simp; ring

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, invarDenom]; ring

/-- FLT's `WeierstrassCurve.ωe`: the `y`-coordinate numerator of `n • P`. -/
def ωe (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - complEDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

lemma ωe_spec (n : ℤ) :
    2 * ωe W n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = ψc W n := by
  have hψ : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
  rw [ψc, complEDS₂_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four,
    mul_assoc (C _), φ_mul_ψ, hψ, invarDenom_eq_redInvarDenom_mul, ωe, ← hψ,
    invar, b₂, b₄, ψ₂, polynomialY, polynomialX, negPolynomial]
  C_simp; ring

lemma two_mul_ωe (n : ℤ) :
    2 * ωe W n = ψc W n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ωe_spec W n]; abel

@[simp] lemma ωe_zero : ωe W 0 = 1 := by simp [ωe]

@[simp] lemma ωe_one : ωe W 1 = Y := by simp [ωe, ψ₂, ← WeierstrassCurve.Affine.Y_sub_polynomialY]

@[simp] lemma ψc_neg (n : ℤ) : ψc W (-n) = ψc W n := by simp [ψc]

end

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_ωe (n : ℤ) : ωe (W.map f) n = (ωe W n).map (mapRingHom f) := by
  simp_rw [ωe, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom,
    map_complEDSAux, Affine.map_polynomial, Affine.map_polynomialX, Affine.map_polynomialY,
    Affine.map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]
  simp

end Map

end FLTForHuman.Elliptic
