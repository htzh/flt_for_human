/-
The order-two Vélu quotient: vocabulary, identities, nonvanishing corollaries,
and the enumeration of the three 2-torsion quotients (V1-SET-1, `OrderTwo.lean`).

Statements are transcribed from the pinned FLT `aa2d8b3` sources — the
`Theorems/` wrappers are the statement authority for the twelve headline nodes,
and the two `Definitions/` files for the vocabulary they declare:

* `Theorems/Thm_WeierstrassCurve_veluQuotient2_cFour.lean`
* `Theorems/Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc.lean`
* `Theorems/Thm_WeierstrassCurve_veluQuotient2_Delta_eq.lean`
* `Theorems/Thm_WeierstrassCurve_velu2_tangent_addX_cleared_identity.lean`
* `Theorems/Thm_WeierstrassCurve_velu2_secant_negAddY_cleared_identity.lean`
* `Theorems/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`
* `Theorems/Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion.lean`
* `Theorems/Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion.lean`
* `Theorems/Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero.lean`
* `Theorems/Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic.lean`
* `Theorems/Thm_WeierstrassCurve_veluQuotient2_j.lean`
* `Theorems/Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero.lean`

plus `Definitions/Def_WeierstrassCurve_VeluOrderTwo.lean` (49 lines),
`Definitions/Def_WeierstrassCurve_VeluPointMap2.lean` (117 lines), and
`Definitions/Def_WeierstrassCurve_VeluQuotientJInvariant.lean:17-18` (`Δ_mul_j`
only — the one declaration the order-two `S_` files reference).

Proof bodies come from the corresponding `P2M/Sol/S_*.lean` files, adapted to
mathlib `v4.34.0` and to the port's `Velu/Defs.lean` vocabulary. The pin's
`set_option maxHeartbeats 16000000` bumps are dropped: the port's global cap is
4,000,000 and the identities were scouted to close under it. The pin's
`maxRecDepth 8000` on `velu2_tangent_negAddY_cleared_identity` is kept (the
default 1000 is reached inside `field_simp`; `maxRecDepth` is not the frozen
knob). Proof-local helpers are `private`, so the checker diffs only the pin's
public surface.

The order-two quotient is the kernel `{0, (x₀, y₀)}` with `veluGy x₀ y₀ = 0`;
the pin writes its formulas in the form `(x - x₀)⁻¹` rather than `(x - x₀)⁻²`
because `-Q = Q`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluOrderTwo.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluPointMap2.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

noncomputable section

open Polynomial Finset

namespace WeierstrassCurve

open WeierstrassCurve.Affine

/-! ### Vocabulary: the order-two quotient and its quadratic discriminant

Transcribed verbatim from `Definitions/Def_WeierstrassCurve_VeluOrderTwo.lean`. -/

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluQuotient2 (x₀ y₀ : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluGx x₀ y₀
  a₆ := W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀)

variable (x₀ y₀ : R)

@[simp] lemma veluQuotient2_a₁ : (W.veluQuotient2 x₀ y₀).a₁ = W.a₁ := rfl
@[simp] lemma veluQuotient2_a₂ : (W.veluQuotient2 x₀ y₀).a₂ = W.a₂ := rfl
@[simp] lemma veluQuotient2_a₃ : (W.veluQuotient2 x₀ y₀).a₃ = W.a₃ := rfl
lemma veluQuotient2_a₄ : (W.veluQuotient2 x₀ y₀).a₄ = W.a₄ - 5 * W.veluGx x₀ y₀ := rfl
lemma veluQuotient2_a₆ :
    (W.veluQuotient2 x₀ y₀).a₆ = W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀) :=
  rfl

lemma veluQuotient2_b₂ : (W.veluQuotient2 x₀ y₀).b₂ = W.b₂ := by
  simp [b₂]

def velu2QuadDisc (x₀ : R) : R :=
  W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄

lemma velu2QuadDisc_def (x₀ : R) :
    W.velu2QuadDisc x₀ = W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄ := rfl

lemma velu2QuadDisc_eq_disc_cofactor (x₀ : R) :
    W.velu2QuadDisc x₀
      = (W.b₂ + 4 * x₀) ^ 2 - 16 * (4 * x₀ ^ 2 + W.b₂ * x₀ + 2 * W.b₄) := by
  simp only [velu2QuadDisc]; ring

lemma map_velu2QuadDisc {S : Type*} [CommRing S] (f : R →+* S) (x₀ : R) :
    (W.map f).velu2QuadDisc (f x₀) = f (W.velu2QuadDisc x₀) := by
  simp only [velu2QuadDisc, map_b₂, map_b₄, map_sub, map_mul, map_pow, map_ofNat]


/-! ### `Δ * j = c₄ ^ 3`

Transcribed from `Definitions/Def_WeierstrassCurve_VeluQuotientJInvariant.lean:17-18`
(the only declaration of that file the order-two `S_` files reference). The pin
states it unconditionally on `V.IsElliptic`; mathlib's `j = Δ'⁻¹ * c₄ ^ 3`
supplies it by `Units` cancellation. -/

theorem Δ_mul_j (V : WeierstrassCurve R) [V.IsElliptic] : V.Δ * V.j = V.c₄ ^ 3 := by
  rw [j, ← coe_Δ', ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end CommRing

/-! ### Vocabulary: the order-two point map

Transcribed verbatim from `Definitions/Def_WeierstrassCurve_VeluPointMap2.lean`. -/

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R)

def velu2XNum (x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluGx x₀ y₀ * (x - x₀)

def velu2YNum (x y : R) : R :=
  y * (x - x₀) ^ 3 - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)

lemma velu2XNum_eq_mul (x : R) :
    W.velu2XNum x₀ y₀ x = (x - x₀) * (x * (x - x₀) + W.veluGx x₀ y₀) := by
  simp only [velu2XNum]; ring

theorem velu2_equation_cleared_four {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    4 * (W.velu2YNum x₀ y₀ x y ^ 2
        + W.a₁ * W.velu2XNum x₀ y₀ x * W.velu2YNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.velu2YNum x₀ y₀ x y * (x - x₀) ^ 3)
      = 4 * (W.velu2XNum x₀ y₀ x ^ 3 + W.a₂ * W.velu2XNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluGx x₀ y₀) * W.velu2XNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀)) * (x - x₀) ^ 6) := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluGy] at hgy
  simp only [velu2XNum, velu2YNum, veluGx, b₂]
  linear_combination
    (4*W.a₁^2*x^2*y₀^2 - 8*W.a₁^2*x*x₀*y₀^2 + 4*W.a₁^2*x₀^2*y₀^2 - 16*W.a₁*W.a₂*x^2*x₀*y₀ + 32*W.a₁*W.a₂*x*x₀^2*y₀ - 16*W.a₁*W.a₂*x₀^3*y₀ - 8*W.a₁*W.a₄*x^2*y₀ + 16*W.a₁*W.a₄*x*x₀*y₀ - 8*W.a₁*W.a₄*x₀^2*y₀ + 8*W.a₁*x^4*y₀ - 32*W.a₁*x^3*x₀*y₀ + 24*W.a₁*x^2*x₀^2*y₀ + 16*W.a₁*x*x₀^3*y₀ - 16*W.a₁*x₀^4*y₀ + 16*W.a₂^2*x^2*x₀^2 - 32*W.a₂^2*x*x₀^3 + 16*W.a₂^2*x₀^4 + 16*W.a₂*W.a₄*x^2*x₀ - 32*W.a₂*W.a₄*x*x₀^2 + 16*W.a₂*W.a₄*x₀^3 - 16*W.a₂*x^4*x₀ + 64*W.a₂*x^3*x₀^2 - 48*W.a₂*x^2*x₀^3 - 32*W.a₂*x*x₀^4 + 32*W.a₂*x₀^5 + 4*W.a₄^2*x^2 - 8*W.a₄^2*x*x₀ + 4*W.a₄^2*x₀^2 - 8*W.a₄*x^4 + 32*W.a₄*x^3*x₀ - 24*W.a₄*x^2*x₀^2 - 16*W.a₄*x*x₀^3 + 16*W.a₄*x₀^4 + 4*x^6 - 24*x^5*x₀ + 36*x^4*x₀^2 + 16*x^3*x₀^3 - 48*x^2*x₀^4 + 16*x₀^6) * hP
    + (-W.a₁^4*x^2*x₀^2 + 2*W.a₁^4*x*x₀^3 - W.a₁^4*x₀^4 - 2*W.a₁^3*W.a₃*x^2*x₀ + 4*W.a₁^3*W.a₃*x*x₀^2 - 2*W.a₁^3*W.a₃*x₀^3 - 8*W.a₁^2*W.a₂*x^2*x₀^2 + 16*W.a₁^2*W.a₂*x*x₀^3 - 8*W.a₁^2*W.a₂*x₀^4 - W.a₁^2*W.a₃^2*x^2 + 2*W.a₁^2*W.a₃^2*x*x₀ - W.a₁^2*W.a₃^2*x₀^2 - 4*W.a₁^2*W.a₄*x^2*x₀ + 8*W.a₁^2*W.a₄*x*x₀^2 - 4*W.a₁^2*W.a₄*x₀^3 + 4*W.a₁^2*x^4*x₀ - 16*W.a₁^2*x^3*x₀^2 + 12*W.a₁^2*x^2*x₀^3 + 8*W.a₁^2*x*x₀^4 - 8*W.a₁^2*x₀^5 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2 - 8*W.a₁*W.a₂*W.a₃*x₀^3 - 4*W.a₁*W.a₃*W.a₄*x^2 + 8*W.a₁*W.a₃*W.a₄*x*x₀ - 4*W.a₁*W.a₃*W.a₄*x₀^2 + 4*W.a₁*W.a₃*x^4 - 16*W.a₁*W.a₃*x^3*x₀ + 12*W.a₁*W.a₃*x^2*x₀^2 + 8*W.a₁*W.a₃*x*x₀^3 - 8*W.a₁*W.a₃*x₀^4 - 16*W.a₂^2*x^2*x₀^2 + 32*W.a₂^2*x*x₀^3 - 16*W.a₂^2*x₀^4 - 16*W.a₂*W.a₄*x^2*x₀ + 32*W.a₂*W.a₄*x*x₀^2 - 16*W.a₂*W.a₄*x₀^3 + 16*W.a₂*x^4*x₀ - 64*W.a₂*x^3*x₀^2 + 48*W.a₂*x^2*x₀^3 + 32*W.a₂*x*x₀^4 - 32*W.a₂*x₀^5 - 4*W.a₄^2*x^2 + 8*W.a₄^2*x*x₀ - 4*W.a₄^2*x₀^2 + 8*W.a₄*x^4 - 32*W.a₄*x^3*x₀ + 24*W.a₄*x^2*x₀^2 + 16*W.a₄*x*x₀^3 - 16*W.a₄*x₀^4 + 24*x^4*x₀^2 - 96*x^3*x₀^3 + 108*x^2*x₀^4 - 24*x*x₀^5 - 12*x₀^6) * hQ
    + (-W.a₁^4*x^2*x₀^2*y₀ + 2*W.a₁^4*x*x₀^3*y₀ - W.a₁^4*x₀^4*y₀ + W.a₁^3*W.a₂*x^2*x₀^3 - 2*W.a₁^3*W.a₂*x*x₀^4 + W.a₁^3*W.a₂*x₀^5 - 2*W.a₁^3*W.a₃*x^2*x₀*y₀ + 4*W.a₁^3*W.a₃*x*x₀^2*y₀ - 2*W.a₁^3*W.a₃*x₀^3*y₀ + W.a₁^3*W.a₄*x^2*x₀^2 - 2*W.a₁^3*W.a₄*x*x₀^3 + W.a₁^3*W.a₄*x₀^4 + W.a₁^3*W.a₆*x^2*x₀ - 2*W.a₁^3*W.a₆*x*x₀^2 + W.a₁^3*W.a₆*x₀^3 + W.a₁^3*x^2*x₀^4 + W.a₁^3*x^2*x₀*y₀^2 - 2*W.a₁^3*x*x₀^5 - 2*W.a₁^3*x*x₀^2*y₀^2 + W.a₁^3*x₀^6 + W.a₁^3*x₀^3*y₀^2 + W.a₁^2*W.a₂*W.a₃*x^2*x₀^2 - 2*W.a₁^2*W.a₂*W.a₃*x*x₀^3 + W.a₁^2*W.a₂*W.a₃*x₀^4 - 10*W.a₁^2*W.a₂*x^2*x₀^2*y₀ + 20*W.a₁^2*W.a₂*x*x₀^3*y₀ - 10*W.a₁^2*W.a₂*x₀^4*y₀ - W.a₁^2*W.a₃^2*x^2*y₀ + 2*W.a₁^2*W.a₃^2*x*x₀*y₀ - W.a₁^2*W.a₃^2*x₀^2*y₀ + W.a₁^2*W.a₃*W.a₄*x^2*x₀ - 2*W.a₁^2*W.a₃*W.a₄*x*x₀^2 + W.a₁^2*W.a₃*W.a₄*x₀^3 + W.a₁^2*W.a₃*W.a₆*x^2 - 2*W.a₁^2*W.a₃*W.a₆*x*x₀ + W.a₁^2*W.a₃*W.a₆*x₀^2 + W.a₁^2*W.a₃*x^2*x₀^3 + W.a₁^2*W.a₃*x^2*y₀^2 - 2*W.a₁^2*W.a₃*x*x₀^4 - 2*W.a₁^2*W.a₃*x*x₀*y₀^2 + W.a₁^2*W.a₃*x₀^5 + W.a₁^2*W.a₃*x₀^2*y₀^2 - 6*W.a₁^2*W.a₄*x^2*x₀*y₀ + 12*W.a₁^2*W.a₄*x*x₀^2*y₀ - 6*W.a₁^2*W.a₄*x₀^3*y₀ - 2*W.a₁^2*W.a₆*x^2*y₀ + 4*W.a₁^2*W.a₆*x*x₀*y₀ - 2*W.a₁^2*W.a₆*x₀^2*y₀ - 4*W.a₁^2*x^5*y₀ + 24*W.a₁^2*x^4*x₀*y₀ - 56*W.a₁^2*x^3*x₀^2*y₀ + 50*W.a₁^2*x^2*x₀^3*y₀ + 4*W.a₁^2*x^2*y*y₀^2 - 2*W.a₁^2*x^2*y₀^3 - 8*W.a₁^2*x*x₀^4*y₀ - 8*W.a₁^2*x*x₀*y*y₀^2 + 4*W.a₁^2*x*x₀*y₀^3 - 6*W.a₁^2*x₀^5*y₀ + 4*W.a₁^2*x₀^2*y*y₀^2 - 2*W.a₁^2*x₀^2*y₀^3 + 8*W.a₁*W.a₂^2*x^2*x₀^3 - 16*W.a₁*W.a₂^2*x*x₀^4 + 8*W.a₁*W.a₂^2*x₀^5 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀*y₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2*y₀ - 8*W.a₁*W.a₂*W.a₃*x₀^3*y₀ + 12*W.a₁*W.a₂*W.a₄*x^2*x₀^2 - 24*W.a₁*W.a₂*W.a₄*x*x₀^3 + 12*W.a₁*W.a₂*W.a₄*x₀^4 + 8*W.a₁*W.a₂*W.a₆*x^2*x₀ - 16*W.a₁*W.a₂*W.a₆*x*x₀^2 + 8*W.a₁*W.a₂*W.a₆*x₀^3 + 8*W.a₁*W.a₂*x^5*x₀ - 44*W.a₁*W.a₂*x^4*x₀^2 + 96*W.a₁*W.a₂*x^3*x₀^3 - 84*W.a₁*W.a₂*x^2*x₀^4 - 16*W.a₁*W.a₂*x^2*x₀*y*y₀ + 8*W.a₁*W.a₂*x^2*x₀*y₀^2 + 16*W.a₁*W.a₂*x*x₀^5 + 32*W.a₁*W.a₂*x*x₀^2*y*y₀ - 16*W.a₁*W.a₂*x*x₀^2*y₀^2 + 8*W.a₁*W.a₂*x₀^6 - 16*W.a₁*W.a₂*x₀^3*y*y₀ + 8*W.a₁*W.a₂*x₀^3*y₀^2 - 4*W.a₁*W.a₃*W.a₄*x^2*y₀ + 8*W.a₁*W.a₃*W.a₄*x*x₀*y₀ - 4*W.a₁*W.a₃*W.a₄*x₀^2*y₀ + 4*W.a₁*W.a₃*x^4*y₀ - 16*W.a₁*W.a₃*x^3*x₀*y₀ + 12*W.a₁*W.a₃*x^2*x₀^2*y₀ + 8*W.a₁*W.a₃*x*x₀^3*y₀ - 8*W.a₁*W.a₃*x₀^4*y₀ + 4*W.a₁*W.a₄^2*x^2*x₀ - 8*W.a₁*W.a₄^2*x*x₀^2 + 4*W.a₁*W.a₄^2*x₀^3 + 4*W.a₁*W.a₄*W.a₆*x^2 - 8*W.a₁*W.a₄*W.a₆*x*x₀ + 4*W.a₁*W.a₄*W.a₆*x₀^2 + 4*W.a₁*W.a₄*x^5 - 24*W.a₁*W.a₄*x^4*x₀ + 56*W.a₁*W.a₄*x^3*x₀^2 - 48*W.a₁*W.a₄*x^2*x₀^3 - 8*W.a₁*W.a₄*x^2*y*y₀ + 4*W.a₁*W.a₄*x^2*y₀^2 + 4*W.a₁*W.a₄*x*x₀^4 + 16*W.a₁*W.a₄*x*x₀*y*y₀ - 8*W.a₁*W.a₄*x*x₀*y₀^2 + 8*W.a₁*W.a₄*x₀^5 - 8*W.a₁*W.a₄*x₀^2*y*y₀ + 4*W.a₁*W.a₄*x₀^2*y₀^2 - 4*W.a₁*W.a₆*x^4 + 16*W.a₁*W.a₆*x^3*x₀ - 12*W.a₁*W.a₆*x^2*x₀^2 - 8*W.a₁*W.a₆*x*x₀^3 + 8*W.a₁*W.a₆*x₀^4 + 12*W.a₁*x^5*x₀^2 - 64*W.a₁*x^4*x₀^3 + 4*W.a₁*x^4*y*y₀ + 136*W.a₁*x^3*x₀^4 - 16*W.a₁*x^3*x₀*y*y₀ - 132*W.a₁*x^2*x₀^5 + 12*W.a₁*x^2*x₀^2*y₀^2 + 52*W.a₁*x*x₀^6 + 32*W.a₁*x*x₀^3*y*y₀ - 24*W.a₁*x*x₀^3*y₀^2 - 4*W.a₁*x₀^7 - 20*W.a₁*x₀^4*y*y₀ + 12*W.a₁*x₀^4*y₀^2 + 16*W.a₂^2*x^2*x₀^2*y - 16*W.a₂^2*x^2*x₀^2*y₀ - 32*W.a₂^2*x*x₀^3*y + 32*W.a₂^2*x*x₀^3*y₀ + 16*W.a₂^2*x₀^4*y - 16*W.a₂^2*x₀^4*y₀ + 16*W.a₂*W.a₄*x^2*x₀*y - 16*W.a₂*W.a₄*x^2*x₀*y₀ - 32*W.a₂*W.a₄*x*x₀^2*y + 32*W.a₂*W.a₄*x*x₀^2*y₀ + 16*W.a₂*W.a₄*x₀^3*y - 16*W.a₂*W.a₄*x₀^3*y₀ - 8*W.a₂*x^4*x₀*y + 8*W.a₂*x^4*x₀*y₀ + 32*W.a₂*x^3*x₀^2*y - 32*W.a₂*x^3*x₀^2*y₀ - 64*W.a₂*x*x₀^4*y + 64*W.a₂*x*x₀^4*y₀ + 40*W.a₂*x₀^5*y - 40*W.a₂*x₀^5*y₀ + 4*W.a₄^2*x^2*y - 4*W.a₄^2*x^2*y₀ - 8*W.a₄^2*x*x₀*y + 8*W.a₄^2*x*x₀*y₀ + 4*W.a₄^2*x₀^2*y - 4*W.a₄^2*x₀^2*y₀ - 4*W.a₄*x^4*y + 4*W.a₄*x^4*y₀ + 16*W.a₄*x^3*x₀*y - 16*W.a₄*x^3*x₀*y₀ - 32*W.a₄*x*x₀^3*y + 32*W.a₄*x*x₀^3*y₀ + 20*W.a₄*x₀^4*y - 20*W.a₄*x₀^4*y₀ - 12*x^4*x₀^2*y + 12*x^4*x₀^2*y₀ + 48*x^3*x₀^3*y - 48*x^3*x₀^3*y₀ - 36*x^2*x₀^4*y + 36*x^2*x₀^4*y₀ - 24*x*x₀^5*y + 24*x*x₀^5*y₀ + 24*x₀^6*y - 24*x₀^6*y₀) * hgy

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def velu2X (x₀ y₀ x : F) : F :=
  x + W.veluGx x₀ y₀ / (x - x₀)

noncomputable def velu2Y (x₀ y₀ x y : F) : F :=
  y - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2

lemma velu2X_eq_div (x₀ y₀ : F) {x : F} (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ x = W.velu2XNum x₀ y₀ x / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2X, velu2XNum]
  field_simp

lemma velu2Y_eq_div (x₀ y₀ : F) {x : F} (y : F) (hx : x ≠ x₀) :
    W.velu2Y x₀ y₀ x y = W.velu2YNum x₀ y₀ x y / (x - x₀) ^ 3 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2Y, velu2YNum]
  field_simp

theorem velu2_map_equation (hchar : (2 : F) ≠ 0) {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    (W.veluQuotient2 x₀ y₀).toAffine.Equation
      (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have h4 : (4 : F) ≠ 0 := fun hcon =>
    hchar (mul_self_eq_zero.mp (by rw [show ((2 : F) * 2) = 4 from by norm_num, hcon]))
  have key := mul_left_cancel₀ h4 (W.velu2_equation_cleared_four hP hQ hgy)
  rw [Affine.equation_iff, W.velu2X_eq_div x₀ y₀ hx, W.velu2Y_eq_div x₀ y₀ y hx]
  simp only [veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃, veluQuotient2_a₄,
    veluQuotient2_a₆]
  field_simp
  linear_combination key

variable {W} in

theorem velu2_map_nonsingular (hchar : (2 : F) ≠ 0) {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    (W.veluQuotient2 x₀ y₀).toAffine.Nonsingular
      (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) :=
  ((W.veluQuotient2 x₀ y₀).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    (W.velu2_map_equation hchar hP hQ hgy hx)

variable {W}
variable (hchar : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
  (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

open scoped Classical in
set_option linter.unusedVariables false in

noncomputable def veluPointMap2 :
    W.toAffine.Point → (W.veluQuotient2 x₀ y₀).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x = x₀ then .zero
    else .some _ _ (velu2_map_nonsingular hchar h.1 hQ hgy hx hΔ)

@[simp] lemma veluPointMap2_zero : veluPointMap2 hchar hQ hgy hΔ .zero = .zero := rfl

lemma veluPointMap2_some_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    veluPointMap2 hchar hQ hgy hΔ (.some x y h) = .zero := by
  simp only [veluPointMap2]
  exact dif_pos hx

lemma veluPointMap2_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ (.some x y h)
      = .some _ _ (velu2_map_nonsingular hchar h.1 hQ hgy hx hΔ) := by
  simp only [veluPointMap2]
  exact dif_neg hx

end Field

/-! ### `veluQuotient2_cFour` — The `c₄` of the order-two quotient. -/

section

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R)
theorem veluQuotient2_cFour :
    (W.veluQuotient2 x₀ y₀).c₄ = W.c₄ + 240 * W.veluGx x₀ y₀  :=  by
  have hb₄ : (W.veluQuotient2 x₀ y₀).b₄ = W.b₄ - 10 * W.veluGx x₀ y₀ := by
    simp only [b₄, veluQuotient2_a₁, veluQuotient2_a₃, veluQuotient2_a₄]; ring
  simp only [c₄, veluQuotient2_b₂, hb₄]; ring

end

/-! ### `Delta_eq_veluGx_sq_mul_velu2QuadDisc` — The discriminant factorization behind the quotient discriminant. -/

section

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem Delta_eq_veluGx_sq_mul_velu2QuadDisc {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.Δ = W.veluGx x₀ y₀ ^ 2 * W.velu2QuadDisc x₀  :=  by
  rw [Affine.equation_iff] at hQ
  simp only [veluGy] at hgy
  simp only [Δ, b₂, b₄, b₆, b₈, veluGx, velu2QuadDisc]
  linear_combination
    (W.a₁^6 + 12*W.a₁^4*W.a₂ - 36*W.a₁^3*W.a₃ + 48*W.a₁^2*W.a₂^2 - 72*W.a₁^2*W.a₄ - 144*W.a₁*W.a₂*W.a₃ + 432*W.a₁*x₀*y₀ + 64*W.a₂^3 - 288*W.a₂*W.a₄ - 432*W.a₂*x₀^2 + 216*W.a₃^2 + 432*W.a₃*y₀ - 432*W.a₄*x₀ + 432*W.a₆ - 432*x₀^3 + 432*y₀^2) * hQ
    + (W.a₁^6*y₀ - W.a₁^5*W.a₂*x₀ - W.a₁^5*W.a₄ - W.a₁^5*x₀^2 + W.a₁^4*W.a₂*W.a₃ + 10*W.a₁^4*W.a₂*y₀ + W.a₁^4*W.a₃*x₀ - 4*W.a₁^4*x₀*y₀ - 8*W.a₁^3*W.a₂^2*x₀ - 8*W.a₁^3*W.a₂*W.a₄ - W.a₁^3*W.a₃^2 - 34*W.a₁^3*W.a₃*y₀ + 6*W.a₁^3*W.a₄*x₀ + 9*W.a₁^3*x₀^3 + 8*W.a₁^2*W.a₂^2*W.a₃ + 32*W.a₁^2*W.a₂^2*y₀ + 36*W.a₁^2*W.a₂*W.a₃*x₀ - 16*W.a₁^2*W.a₂*x₀*y₀ + 30*W.a₁^2*W.a₃*W.a₄ + 27*W.a₁^2*W.a₃*x₀^2 - 68*W.a₁^2*W.a₄*y₀ + 30*W.a₁^2*x₀^2*y₀ - 16*W.a₁*W.a₂^3*x₀ - 16*W.a₁*W.a₂^2*W.a₄ + 16*W.a₁*W.a₂^2*x₀^2 - 36*W.a₁*W.a₂*W.a₃^2 - 72*W.a₁*W.a₂*W.a₃*y₀ + 88*W.a₁*W.a₂*W.a₄*x₀ - 24*W.a₁*W.a₂*x₀^3 - 27*W.a₁*W.a₃^2*x₀ + 108*W.a₁*W.a₃*x₀*y₀ + 64*W.a₁*W.a₄^2 + 24*W.a₁*W.a₄*x₀^2 - 72*W.a₁*x₀^4 + 324*W.a₁*x₀*y₀^2 + 16*W.a₂^3*W.a₃ + 32*W.a₂^3*y₀ - 72*W.a₂*W.a₃*W.a₄ - 216*W.a₂*W.a₃*x₀^2 - 144*W.a₂*W.a₄*y₀ - 432*W.a₂*x₀^2*y₀ + 27*W.a₃^3 + 162*W.a₃^2*y₀ - 216*W.a₃*W.a₄*x₀ - 216*W.a₃*x₀^3 + 324*W.a₃*y₀^2 - 432*W.a₄*x₀*y₀ - 432*x₀^3*y₀ + 216*y₀^3) * hgy

end

/-! ### `veluQuotient2_Delta_eq` — The quotient discriminant, `Gx · H²`. -/

section

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem veluQuotient2_Delta_eq {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ = W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2  :=  by
  rw [Affine.equation_iff] at hQ
  simp only [veluGy] at hgy
  simp only [Δ, b₂, b₄, b₆, b₈, veluQuotient2, veluGx, velu2QuadDisc]
  linear_combination
    (W.a₁^6 + 12*W.a₁^4*W.a₂ - 36*W.a₁^3*W.a₃ + 504*W.a₁^3*y₀ + 48*W.a₁^2*W.a₂^2 - 1008*W.a₁^2*W.a₂*x₀ - 576*W.a₁^2*W.a₄ - 1512*W.a₁^2*x₀^2 - 144*W.a₁*W.a₂*W.a₃ + 2016*W.a₁*W.a₂*y₀ + 6480*W.a₁*x₀*y₀ + 64*W.a₂^3 - 4032*W.a₂^2*x₀ - 2304*W.a₂*W.a₄ - 18576*W.a₂*x₀^2 + 216*W.a₃^2 + 432*W.a₃*y₀ - 6480*W.a₄*x₀ + 432*W.a₆ - 18576*x₀^3 + 432*y₀^2) * hQ
    + (24*W.a₁^6*y₀ - 47*W.a₁^5*W.a₂*x₀ - 24*W.a₁^5*W.a₄ - 70*W.a₁^5*x₀^2 + W.a₁^4*W.a₂*W.a₃ + 194*W.a₁^4*W.a₂*y₀ + W.a₁^4*W.a₃*x₀ - 110*W.a₁^4*x₀*y₀ - 376*W.a₁^3*W.a₂^2*x₀ - 192*W.a₁^3*W.a₂*W.a₄ - 340*W.a₁^3*W.a₂*x₀^2 - W.a₁^3*W.a₃^2 - 692*W.a₁^3*W.a₃*y₀ + 112*W.a₁^3*W.a₄*x₀ + 327*W.a₁^3*x₀^3 + 4252*W.a₁^3*y₀^2 + 8*W.a₁^2*W.a₂^2*W.a₃ + 400*W.a₁^2*W.a₂^2*y₀ + 1352*W.a₁^2*W.a₂*W.a₃*x₀ - 16944*W.a₁^2*W.a₂*x₀*y₀ + 688*W.a₁^2*W.a₃*W.a₄ + 2001*W.a₁^2*W.a₃*x₀^2 - 9888*W.a₁^2*W.a₄*y₀ - 24606*W.a₁^2*x₀^2*y₀ - 752*W.a₁*W.a₂^3*x₀ - 384*W.a₁*W.a₂^2*W.a₄ + 15760*W.a₁*W.a₂^2*x₀^2 - 36*W.a₁*W.a₂*W.a₃^2 + 432*W.a₁*W.a₂*W.a₃*y₀ + 19648*W.a₁*W.a₂*W.a₄*x₀ + 49008*W.a₁*W.a₂*x₀^3 + 1008*W.a₁*W.a₂*y₀^2 - 27*W.a₁*W.a₃^2*x₀ + 1620*W.a₁*W.a₃*x₀*y₀ + 5632*W.a₁*W.a₄^2 + 28608*W.a₁*W.a₄*x₀^2 + 35568*W.a₁*x₀^4 + 3348*W.a₁*x₀*y₀^2 + 16*W.a₂^3*W.a₃ + 32*W.a₂^3*y₀ - 1008*W.a₂^2*W.a₃*x₀ - 2016*W.a₂^2*x₀*y₀ - 576*W.a₂*W.a₃*W.a₄ - 4752*W.a₂*W.a₃*x₀^2 - 1152*W.a₂*W.a₄*y₀ - 9504*W.a₂*x₀^2*y₀ + 27*W.a₃^3 + 162*W.a₃^2*y₀ - 1728*W.a₃*W.a₄*x₀ - 4752*W.a₃*x₀^3 + 324*W.a₃*y₀^2 - 3456*W.a₄*x₀*y₀ - 9504*x₀^3*y₀ + 216*y₀^3) * hgy

end

/-! ### `velu2_tangent_addX_cleared_identity` — The tangent `addX` cleared identity (order two). -/

private theorem velu2TangentAddX_assemble {R : Type*} [CommRing R] {A M C D t u : R}
    (h1 : A * u = t ^ 2) (h2 : C = D ^ 2) (h3 : M = t ^ 2 * u + 2 * D ^ 2) :
    A * M * u * C = (t * D) ^ 2 * (t ^ 2 * u + 2 * C) := by
  linear_combination (M * C) * h1 + (t ^ 4 * u) * h2 + (t ^ 2 * C) * h3

theorem velu2_tangent_addX_cleared_identity
    {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (W.a₁ ^ 2 * (x - x₀)
            + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (((x - x₀) ^ 2 - W.veluGx x₀ y₀)
                * (6 * x ^ 2 + (4 * W.a₂ + W.a₁ ^ 2) * x + 2 * W.a₄ + W.a₁ * W.a₃)
              + W.veluGx x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (x - x₀)
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
      = ((2 * y + W.a₁ * x + W.a₃) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)) ^ 2
        * ((2 * y + W.a₁ * x + W.a₃) ^ 2 * (x - x₀)
            + 2
              * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
                  + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
                    * (2 * y + W.a₁ * x + W.a₃)
                  - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)) := by
  rw [Affine.equation_iff] at hP hQ
  refine velu2TangentAddX_assemble ?_ ?_ ?_
  ·
    linear_combination (-4) * hP + 4 * hQ
      + (-2 * W.a₁ * x + W.a₁ * x₀ - W.a₃ - 2 * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x - 4 * x₀) * hP
      + (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * x₀) * hQ
      + (-W.a₁ ^ 2 * y₀ + W.a₁ * W.a₂ * x₀ + W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x₀ ^ 2
          - W.a₂ * W.a₃ - 2 * W.a₂ * y₀ - 2 * W.a₃ * x - W.a₃ * x₀ - 4 * x * y₀
          - 2 * x₀ * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-4 * x + 4 * x₀) * hP + (4 * x - 4 * x₀) * hQ
      + (W.a₁ ^ 2 * y₀ - 2 * W.a₁ * W.a₂ * x₀ - W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x * x₀
          - 3 * W.a₁ * x₀ ^ 2 - W.a₃ * x + W.a₃ * x₀ - 2 * x * y₀ + 2 * x₀ * y₀) * hord

/-! ### `velu2_secant_negAddY_cleared_identity` — The secant `negAddY` cleared identity. -/

theorem velu2_secant_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x₁ y₁ x₂ y₂ : F}
    (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) :
    (x₂ - x₀)
          * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
          * (x₂ - W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          * (y₁ - y₀)
        - (x₁ - x₀)
          * ((W.a₁ * (x₂ - x₀) + y₂ - y₀)
                * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
                    + W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀)
                * (x₂ - x₀) ^ 2)
        + W.veluGx x₀ y₀
          * ((W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) * (y₂ - y₀)
              - (x₂ - x₀)
                * (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀))
      = 0 := by
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  rw [Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [Affine.slope_of_X_ne hx12, Affine.addX, Affine.negAddY, veluGx]
  field_simp
  linear_combination
    (W.a₁^2*x₀^3*y₂ - W.a₁^2*x₀^2*x₁*y₂ - 2*W.a₁^2*x₀^2*x₂*y₂ + W.a₁^2*x₀*x₁^2*y₁ - 2*W.a₁^2*x₀*x₁^2*y₂ - 2*W.a₁^2*x₀*x₁*x₂*y₁ + 6*W.a₁^2*x₀*x₁*x₂*y₂ + W.a₁^2*x₀*x₂^2*y₁ - W.a₁^2*x₀*x₂^2*y₂ - W.a₁^2*x₁^2*x₂*y₁ + 2*W.a₁^2*x₁^2*x₂*y₂ + 2*W.a₁^2*x₁*x₂^2*y₁ - 5*W.a₁^2*x₁*x₂^2*y₂ - W.a₁^2*x₂^3*y₁ + 2*W.a₁^2*x₂^3*y₂ + 2*W.a₁*W.a₂*x₀^3*x₁ - 2*W.a₁*W.a₂*x₀^3*x₂ + W.a₁*W.a₂*x₀^2*x₁^2 - 4*W.a₁*W.a₂*x₀^2*x₁*x₂ + 4*W.a₁*W.a₂*x₀^2*x₂^2 - W.a₁*W.a₂*x₀*x₁^3 + 3*W.a₁*W.a₂*x₀*x₁^2*x₂ - 4*W.a₁*W.a₂*x₀*x₁*x₂^2 + W.a₁*W.a₂*x₁^3*x₂ - 4*W.a₁*W.a₂*x₁^2*x₂^2 + 6*W.a₁*W.a₂*x₁*x₂^3 - 2*W.a₁*W.a₂*x₂^4 + 2*W.a₁*W.a₄*x₀^2*x₁ - W.a₁*W.a₄*x₀^2*x₂ + W.a₁*W.a₄*x₀*x₁^2 - 5*W.a₁*W.a₄*x₀*x₁*x₂ + 2*W.a₁*W.a₄*x₀*x₂^2 - W.a₁*W.a₄*x₁^2*x₂ + 3*W.a₁*W.a₄*x₁*x₂^2 - W.a₁*W.a₄*x₂^3 + W.a₁*W.a₆*x₀^2 + W.a₁*W.a₆*x₀*x₁ - 3*W.a₁*W.a₆*x₀*x₂ - W.a₁*W.a₆*x₁*x₂ + 2*W.a₁*W.a₆*x₂^2 + 2*W.a₁*x₀^4*x₁ - 2*W.a₁*x₀^4*x₂ + W.a₁*x₀^3*x₁^2 - 4*W.a₁*x₀^3*x₁*x₂ + 3*W.a₁*x₀^3*x₂^2 + W.a₁*x₀^2*x₂^3 + 4*W.a₁*x₀^2*y₀*y₂ + W.a₁*x₀^2*y₁*y₂ - 4*W.a₁*x₀^2*y₂^2 - W.a₁*x₀*x₁^4 + W.a₁*x₀*x₁^3*x₂ + 3*W.a₁*x₀*x₁^2*x₂^2 - 6*W.a₁*x₀*x₁*x₂^3 + 2*W.a₁*x₀*x₁*y₀^2 - 5*W.a₁*x₀*x₁*y₀*y₂ + 2*W.a₁*x₀*x₁*y₁^2 - 6*W.a₁*x₀*x₁*y₁*y₂ + 8*W.a₁*x₀*x₁*y₂^2 + W.a₁*x₀*x₂^4 - 2*W.a₁*x₀*x₂*y₀^2 - 3*W.a₁*x₀*x₂*y₀*y₂ - 2*W.a₁*x₀*x₂*y₁^2 + 4*W.a₁*x₀*x₂*y₁*y₂ + W.a₁*x₁^4*x₂ - W.a₁*x₁^3*x₂^2 - 4*W.a₁*x₁^2*x₂^3 + W.a₁*x₁^2*y₀^2 + W.a₁*x₁^2*y₀*y₁ - 3*W.a₁*x₁^2*y₀*y₂ - W.a₁*x₁^2*y₁*y₂ + 2*W.a₁*x₁^2*y₂^2 + 8*W.a₁*x₁*x₂^4 - 4*W.a₁*x₁*x₂*y₀^2 - 2*W.a₁*x₁*x₂*y₀*y₁ + 11*W.a₁*x₁*x₂*y₀*y₂ - 2*W.a₁*x₁*x₂*y₁^2 + 8*W.a₁*x₁*x₂*y₁*y₂ - 12*W.a₁*x₁*x₂*y₂^2 - 3*W.a₁*x₂^5 + 3*W.a₁*x₂^2*y₀^2 + W.a₁*x₂^2*y₀*y₁ - 4*W.a₁*x₂^2*y₀*y₂ + 2*W.a₁*x₂^2*y₁^2 - 6*W.a₁*x₂^2*y₁*y₂ + 6*W.a₁*x₂^2*y₂^2 + 4*W.a₂*x₀^2*x₁*y₀ + 2*W.a₂*x₀^2*x₁*y₁ - 6*W.a₂*x₀^2*x₁*y₂ - 4*W.a₂*x₀^2*x₂*y₀ - 2*W.a₂*x₀^2*x₂*y₁ + 6*W.a₂*x₀^2*x₂*y₂ - W.a₂*x₀*x₁^2*y₁ + W.a₂*x₀*x₁^2*y₂ + 2*W.a₂*x₀*x₁*x₂*y₁ - 2*W.a₂*x₀*x₁*x₂*y₂ + 2*W.a₂*x₀*x₂^2*y₀ - 2*W.a₂*x₀*x₂^2*y₂ - W.a₂*x₁^3*y₀ + W.a₂*x₁^3*y₂ + 3*W.a₂*x₁^2*x₂*y₀ + W.a₂*x₁^2*x₂*y₁ - 4*W.a₂*x₁^2*x₂*y₂ - 6*W.a₂*x₁*x₂^2*y₀ - 4*W.a₂*x₁*x₂^2*y₁ + 10*W.a₂*x₁*x₂^2*y₂ + 2*W.a₂*x₂^3*y₀ + 2*W.a₂*x₂^3*y₁ - 4*W.a₂*x₂^3*y₂ + 4*W.a₄*x₀*x₁*y₀ + 2*W.a₄*x₀*x₁*y₁ - 6*W.a₄*x₀*x₁*y₂ - 2*W.a₄*x₀*x₂*y₀ - W.a₄*x₀*x₂*y₁ + 3*W.a₄*x₀*x₂*y₂ - 3*W.a₄*x₁*x₂*y₀ - 2*W.a₄*x₁*x₂*y₁ + 5*W.a₄*x₁*x₂*y₂ + W.a₄*x₂^2*y₀ + W.a₄*x₂^2*y₁ - 2*W.a₄*x₂^2*y₂ + 2*W.a₆*x₀*y₀ + W.a₆*x₀*y₁ - 3*W.a₆*x₀*y₂ + W.a₆*x₁*y₀ - W.a₆*x₁*y₂ - 3*W.a₆*x₂*y₀ - W.a₆*x₂*y₁ + 4*W.a₆*x₂*y₂ + 4*x₀^3*x₁*y₀ + 2*x₀^3*x₁*y₁ - 6*x₀^3*x₁*y₂ - 4*x₀^3*x₂*y₀ - 2*x₀^3*x₂*y₁ + 6*x₀^3*x₂*y₂ - x₀*x₁^3*y₁ + x₀*x₁^3*y₂ + 3*x₀*x₁*x₂^2*y₁ - 3*x₀*x₁*x₂^2*y₂ + 2*x₀*x₂^3*y₀ - x₀*x₂^3*y₁ - x₀*x₂^3*y₂ + 4*x₀*y₀^2*y₂ + 2*x₀*y₀*y₁*y₂ - 8*x₀*y₀*y₂^2 + x₀*y₁^3 - 3*x₀*y₁^2*y₂ + 2*x₀*y₁*y₂^2 + 2*x₀*y₂^3 - x₁^4*y₀ + x₁^4*y₂ + x₁^3*x₂*y₀ + x₁^3*x₂*y₁ - 2*x₁^3*x₂*y₂ + 3*x₁^2*x₂^2*y₀ - 3*x₁^2*x₂^2*y₂ - 8*x₁*x₂^3*y₀ - 5*x₁*x₂^3*y₁ + 13*x₁*x₂^3*y₂ + 4*x₁*y₀^3 + 2*x₁*y₀^2*y₁ - 12*x₁*y₀^2*y₂ + x₁*y₀*y₁^2 - 6*x₁*y₀*y₁*y₂ + 14*x₁*y₀*y₂^2 - x₁*y₁^2*y₂ + 4*x₁*y₁*y₂^2 - 6*x₁*y₂^3 + 3*x₂^4*y₀ + 3*x₂^4*y₁ - 6*x₂^4*y₂ - 4*x₂*y₀^3 - 2*x₂*y₀^2*y₁ + 8*x₂*y₀^2*y₂ - x₂*y₀*y₁^2 + 4*x₂*y₀*y₁*y₂ - 6*x₂*y₀*y₂^2 - x₂*y₁^3 + 4*x₂*y₁^2*y₂ - 6*x₂*y₁*y₂^2 + 4*x₂*y₂^3) * hP₁
    + (-W.a₁^2*x₀^3*y₁ + 2*W.a₁^2*x₀^2*x₁*y₁ + W.a₁^2*x₀^2*x₂*y₁ - W.a₁^2*x₀*x₁^2*y₁ + W.a₁^2*x₀*x₁^2*y₂ - 2*W.a₁^2*x₀*x₁*x₂*y₁ - 2*W.a₁^2*x₀*x₁*x₂*y₂ + W.a₁^2*x₀*x₂^2*y₂ - W.a₁^2*x₁^3*y₂ + W.a₁^2*x₁^2*x₂*y₁ + 2*W.a₁^2*x₁^2*x₂*y₂ - W.a₁^2*x₁*x₂^2*y₂ - 2*W.a₁*W.a₂*x₀^3*x₁ + 2*W.a₁*W.a₂*x₀^3*x₂ + 2*W.a₁*W.a₂*x₀^2*x₁^2 - 4*W.a₁*W.a₂*x₀^2*x₁*x₂ + W.a₁*W.a₂*x₀^2*x₂^2 + 2*W.a₁*W.a₂*x₀*x₁^3 - 2*W.a₁*W.a₂*x₀*x₁^2*x₂ + 3*W.a₁*W.a₂*x₀*x₁*x₂^2 - W.a₁*W.a₂*x₀*x₂^3 - 2*W.a₁*W.a₂*x₁^2*x₂^2 + W.a₁*W.a₂*x₁*x₂^3 - 3*W.a₁*W.a₄*x₀^2*x₁ + 2*W.a₁*W.a₄*x₀^2*x₂ + 4*W.a₁*W.a₄*x₀*x₁^2 - 3*W.a₁*W.a₄*x₀*x₁*x₂ + W.a₁*W.a₄*x₀*x₂^2 + W.a₁*W.a₄*x₁^3 - 3*W.a₁*W.a₄*x₁^2*x₂ + W.a₁*W.a₄*x₁*x₂^2 - W.a₁*W.a₆*x₀^2 - W.a₁*W.a₆*x₀*x₁ + 3*W.a₁*W.a₆*x₀*x₂ + 4*W.a₁*W.a₆*x₁^2 - 7*W.a₁*W.a₆*x₁*x₂ + 2*W.a₁*W.a₆*x₂^2 - 2*W.a₁*x₀^4*x₁ + 2*W.a₁*x₀^4*x₂ + 3*W.a₁*x₀^3*x₁^2 - 4*W.a₁*x₀^3*x₁*x₂ + W.a₁*x₀^3*x₂^2 - W.a₁*x₀^2*x₁^3 - 4*W.a₁*x₀^2*y₀*y₁ + 3*W.a₁*x₀^2*y₁*y₂ + 2*W.a₁*x₀*x₁^4 - 3*W.a₁*x₀*x₁^2*x₂^2 + 5*W.a₁*x₀*x₁*x₂^3 - 2*W.a₁*x₀*x₁*y₀^2 + 7*W.a₁*x₀*x₁*y₀*y₁ - 4*W.a₁*x₀*x₁*y₁*y₂ - 2*W.a₁*x₀*x₁*y₂^2 - 2*W.a₁*x₀*x₂^4 + 2*W.a₁*x₀*x₂*y₀^2 + W.a₁*x₀*x₂*y₀*y₁ - 2*W.a₁*x₀*x₂*y₁*y₂ + 2*W.a₁*x₀*x₂*y₂^2 - 2*W.a₁*x₁^4*x₂ + 4*W.a₁*x₁^3*x₂^2 - 5*W.a₁*x₁^2*x₂^3 + 3*W.a₁*x₁^2*y₀^2 - 2*W.a₁*x₁^2*y₀*y₁ + W.a₁*x₁^2*y₀*y₂ + 2*W.a₁*x₁^2*y₂^2 + 2*W.a₁*x₁*x₂^4 - 4*W.a₁*x₁*x₂*y₀^2 - 3*W.a₁*x₁*x₂*y₀*y₁ - 2*W.a₁*x₁*x₂*y₀*y₂ + 4*W.a₁*x₁*x₂*y₁*y₂ - 2*W.a₁*x₁*x₂*y₂^2 + W.a₁*x₂^2*y₀^2 + W.a₁*x₂^2*y₀*y₁ + W.a₁*x₂^2*y₀*y₂ - W.a₁*x₂^2*y₁*y₂ - 4*W.a₂*x₀^2*x₁*y₀ + 6*W.a₂*x₀^2*x₁*y₁ - 2*W.a₂*x₀^2*x₁*y₂ + 4*W.a₂*x₀^2*x₂*y₀ - 6*W.a₂*x₀^2*x₂*y₁ + 2*W.a₂*x₀^2*x₂*y₂ - 2*W.a₂*x₀*x₁^2*y₀ + 2*W.a₂*x₀*x₁^2*y₂ - 2*W.a₂*x₀*x₁*x₂*y₁ + 2*W.a₂*x₀*x₁*x₂*y₂ + W.a₂*x₀*x₂^2*y₁ - W.a₂*x₀*x₂^2*y₂ + 4*W.a₂*x₁^3*y₀ - 4*W.a₂*x₁^3*y₂ - 4*W.a₂*x₁^2*x₂*y₀ + 4*W.a₂*x₁^2*x₂*y₁ + 3*W.a₂*x₁*x₂^2*y₀ - 4*W.a₂*x₁*x₂^2*y₁ + W.a₂*x₁*x₂^2*y₂ - W.a₂*x₂^3*y₀ + W.a₂*x₂^3*y₁ - 6*W.a₄*x₀*x₁*y₀ + 5*W.a₄*x₀*x₁*y₁ + W.a₄*x₀*x₁*y₂ + 4*W.a₄*x₀*x₂*y₀ - 6*W.a₄*x₀*x₂*y₁ + 2*W.a₄*x₀*x₂*y₂ + 3*W.a₄*x₁^2*y₀ + 2*W.a₄*x₁^2*y₁ - 5*W.a₄*x₁^2*y₂ - W.a₄*x₁*x₂*y₀ - W.a₄*x₁*x₂*y₁ + 2*W.a₄*x₁*x₂*y₂ - 2*W.a₆*x₀*y₀ - W.a₆*x₀*y₁ + 3*W.a₆*x₀*y₂ - W.a₆*x₁*y₀ + 8*W.a₆*x₁*y₁ - 7*W.a₆*x₁*y₂ + 3*W.a₆*x₂*y₀ - 7*W.a₆*x₂*y₁ + 4*W.a₆*x₂*y₂ - 4*x₀^3*x₁*y₀ + 6*x₀^3*x₁*y₁ - 2*x₀^3*x₁*y₂ + 4*x₀^3*x₂*y₀ - 6*x₀^3*x₂*y₁ + 2*x₀^3*x₂*y₂ - 2*x₀*x₁^3*y₀ + 2*x₀*x₁^3*y₂ - 3*x₀*x₁*x₂^2*y₁ + 3*x₀*x₁*x₂^2*y₂ + 2*x₀*x₂^3*y₁ - 2*x₀*x₂^3*y₂ - 4*x₀*y₀^2*y₁ + 6*x₀*y₀*y₁*y₂ - 3*x₀*y₁*y₂^2 + x₀*y₂^3 + 4*x₁^4*y₀ - 4*x₁^4*y₂ - 2*x₁^3*x₂*y₀ + 2*x₁^3*x₂*y₂ - 3*x₁^2*x₂^2*y₀ + 6*x₁^2*x₂^2*y₁ - 3*x₁^2*x₂^2*y₂ + 5*x₁*x₂^3*y₀ - 7*x₁*x₂^3*y₁ + 2*x₁*x₂^3*y₂ - 4*x₁*y₀^3 + 12*x₁*y₀^2*y₁ - 2*x₁*y₀^2*y₂ - 8*x₁*y₀*y₁*y₂ - x₁*y₀*y₂^2 + 4*x₁*y₁*y₂^2 - x₁*y₂^3 - 2*x₂^4*y₀ + 2*x₂^4*y₁ + 4*x₂*y₀^3 - 8*x₂*y₀^2*y₁ + 2*x₂*y₀^2*y₂ + 2*x₂*y₀*y₁*y₂ + x₂*y₀*y₂^2 - x₂*y₁*y₂^2) * hP₂
    + (-2*W.a₁^2*x₀^2*x₁*y₁ + 2*W.a₁^2*x₀^2*x₁*y₂ + 2*W.a₁^2*x₀^2*x₂*y₁ - 2*W.a₁^2*x₀^2*x₂*y₂ + W.a₁^2*x₀*x₁^2*y₁ - 3*W.a₁^2*x₀*x₁^2*y₂ + 2*W.a₁^2*x₀*x₁*x₂*y₁ + 2*W.a₁^2*x₀*x₁*x₂*y₂ - 3*W.a₁^2*x₀*x₂^2*y₁ + W.a₁^2*x₀*x₂^2*y₂ + W.a₁^2*x₁^3*y₂ - W.a₁^2*x₁^2*x₂*y₁ - W.a₁^2*x₁*x₂^2*y₂ + W.a₁^2*x₂^3*y₁ - 2*W.a₁*W.a₂*x₀*x₁^3 + 2*W.a₁*W.a₂*x₀*x₁^2*x₂ + 2*W.a₁*W.a₂*x₀*x₁*x₂^2 - 2*W.a₁*W.a₂*x₀*x₂^3 - 2*W.a₁*W.a₄*x₀*x₁^2 + 4*W.a₁*W.a₄*x₀*x₁*x₂ - 2*W.a₁*W.a₄*x₀*x₂^2 - W.a₁*W.a₄*x₁^3 + W.a₁*W.a₄*x₁^2*x₂ + W.a₁*W.a₄*x₁*x₂^2 - W.a₁*W.a₄*x₂^3 - 4*W.a₁*W.a₆*x₁^2 + 8*W.a₁*W.a₆*x₁*x₂ - 4*W.a₁*W.a₆*x₂^2 - 2*W.a₁*x₀*x₁^4 + 2*W.a₁*x₀*x₁^3*x₂ + 2*W.a₁*x₀*x₁*x₂^3 - 8*W.a₁*x₀*x₁*y₀*y₁ + 8*W.a₁*x₀*x₁*y₀*y₂ - 2*W.a₁*x₀*x₂^4 + 8*W.a₁*x₀*x₂*y₀*y₁ - 8*W.a₁*x₀*x₂*y₀*y₂ + 2*W.a₁*x₁^4*x₂ - 5*W.a₁*x₁^3*x₂^2 + 5*W.a₁*x₁^2*x₂^3 + 2*W.a₁*x₁^2*y₀*y₁ - 6*W.a₁*x₁^2*y₀*y₂ - 3*W.a₁*x₁*x₂^4 + 4*W.a₁*x₁*x₂*y₀*y₁ + 4*W.a₁*x₁*x₂*y₀*y₂ + W.a₁*x₂^5 - 6*W.a₁*x₂^2*y₀*y₁ + 2*W.a₁*x₂^2*y₀*y₂ - 4*W.a₂*x₁^3*y₀ + 4*W.a₂*x₁^3*y₂ + 4*W.a₂*x₁^2*x₂*y₀ - 4*W.a₂*x₁^2*x₂*y₁ + 4*W.a₂*x₁*x₂^2*y₀ - 4*W.a₂*x₁*x₂^2*y₂ - 4*W.a₂*x₂^3*y₀ + 4*W.a₂*x₂^3*y₁ - 4*W.a₄*x₁^2*y₀ - 2*W.a₄*x₁^2*y₁ + 6*W.a₄*x₁^2*y₂ + 8*W.a₄*x₁*x₂*y₀ - 4*W.a₄*x₁*x₂*y₁ - 4*W.a₄*x₁*x₂*y₂ - 4*W.a₄*x₂^2*y₀ + 6*W.a₄*x₂^2*y₁ - 2*W.a₄*x₂^2*y₂ - 8*W.a₆*x₁*y₁ + 8*W.a₆*x₁*y₂ + 8*W.a₆*x₂*y₁ - 8*W.a₆*x₂*y₂ - 4*x₁^4*y₀ + 4*x₁^4*y₂ + 4*x₁^3*x₂*y₀ - 4*x₁^3*x₂*y₂ - 6*x₁^2*x₂^2*y₁ + 6*x₁^2*x₂^2*y₂ + 4*x₁*x₂^3*y₀ + 4*x₁*x₂^3*y₁ - 8*x₁*x₂^3*y₂ - 8*x₁*y₀^2*y₁ + 8*x₁*y₀^2*y₂ - 4*x₂^4*y₀ + 2*x₂^4*y₁ + 2*x₂^4*y₂ + 8*x₂*y₀^2*y₁ - 8*x₂*y₀^2*y₂) * hQ
    + (2*W.a₁^2*x₀^2*x₁*y₀*y₁ - 2*W.a₁^2*x₀^2*x₁*y₀*y₂ - W.a₁^2*x₀^2*x₁*y₁*y₂ - 2*W.a₁^2*x₀^2*x₂*y₀*y₁ + 2*W.a₁^2*x₀^2*x₂*y₀*y₂ + W.a₁^2*x₀^2*x₂*y₁*y₂ - W.a₁^2*x₀*x₁^2*y₀*y₁ + 3*W.a₁^2*x₀*x₁^2*y₀*y₂ - W.a₁^2*x₀*x₁^2*y₁^2 + 3*W.a₁^2*x₀*x₁^2*y₁*y₂ - W.a₁^2*x₀*x₁^2*y₂^2 - 2*W.a₁^2*x₀*x₁*x₂*y₀*y₁ - 2*W.a₁^2*x₀*x₁*x₂*y₀*y₂ + 2*W.a₁^2*x₀*x₁*x₂*y₁^2 - 4*W.a₁^2*x₀*x₁*x₂*y₁*y₂ + 2*W.a₁^2*x₀*x₁*x₂*y₂^2 + 3*W.a₁^2*x₀*x₂^2*y₀*y₁ - W.a₁^2*x₀*x₂^2*y₀*y₂ - W.a₁^2*x₀*x₂^2*y₁^2 + W.a₁^2*x₀*x₂^2*y₁*y₂ - W.a₁^2*x₀*x₂^2*y₂^2 - W.a₁^2*x₁^3*y₀*y₂ + W.a₁^2*x₁^3*y₂^2 + W.a₁^2*x₁^2*x₂*y₀*y₁ + W.a₁^2*x₁^2*x₂*y₁^2 - 3*W.a₁^2*x₁^2*x₂*y₁*y₂ - 2*W.a₁^2*x₁^2*x₂*y₂^2 + W.a₁^2*x₁*x₂^2*y₀*y₂ - 2*W.a₁^2*x₁*x₂^2*y₁^2 + 5*W.a₁^2*x₁*x₂^2*y₁*y₂ + W.a₁^2*x₁*x₂^2*y₂^2 - W.a₁^2*x₂^3*y₀*y₁ + W.a₁^2*x₂^3*y₁^2 - 2*W.a₁^2*x₂^3*y₁*y₂ - 2*W.a₁*W.a₂*x₀^3*x₁*y₁ + 2*W.a₁*W.a₂*x₀^3*x₁*y₂ + 2*W.a₁*W.a₂*x₀^3*x₂*y₁ - 2*W.a₁*W.a₂*x₀^3*x₂*y₂ - W.a₁*W.a₂*x₀^2*x₁^2*y₁ - 2*W.a₁*W.a₂*x₀^2*x₁^2*y₂ + 4*W.a₁*W.a₂*x₀^2*x₁*x₂*y₁ + 4*W.a₁*W.a₂*x₀^2*x₁*x₂*y₂ - 4*W.a₁*W.a₂*x₀^2*x₂^2*y₁ - W.a₁*W.a₂*x₀^2*x₂^2*y₂ + 2*W.a₁*W.a₂*x₀*x₁^3*y₀ + W.a₁*W.a₂*x₀*x₁^3*y₁ - 2*W.a₁*W.a₂*x₀*x₁^3*y₂ - 2*W.a₁*W.a₂*x₀*x₁^2*x₂*y₀ - 3*W.a₁*W.a₂*x₀*x₁^2*x₂*y₁ + 2*W.a₁*W.a₂*x₀*x₁^2*x₂*y₂ - 2*W.a₁*W.a₂*x₀*x₁*x₂^2*y₀ + 4*W.a₁*W.a₂*x₀*x₁*x₂^2*y₁ - 3*W.a₁*W.a₂*x₀*x₁*x₂^2*y₂ + 2*W.a₁*W.a₂*x₀*x₂^3*y₀ + W.a₁*W.a₂*x₀*x₂^3*y₂ - W.a₁*W.a₂*x₁^3*x₂*y₁ + 4*W.a₁*W.a₂*x₁^2*x₂^2*y₁ + 2*W.a₁*W.a₂*x₁^2*x₂^2*y₂ - 6*W.a₁*W.a₂*x₁*x₂^3*y₁ - W.a₁*W.a₂*x₁*x₂^3*y₂ + 2*W.a₁*W.a₂*x₂^4*y₁ - 2*W.a₁*W.a₄*x₀^2*x₁*y₁ + 3*W.a₁*W.a₄*x₀^2*x₁*y₂ + W.a₁*W.a₄*x₀^2*x₂*y₁ - 2*W.a₁*W.a₄*x₀^2*x₂*y₂ + 2*W.a₁*W.a₄*x₀*x₁^2*y₀ - W.a₁*W.a₄*x₀*x₁^2*y₁ - 4*W.a₁*W.a₄*x₀*x₁^2*y₂ - 4*W.a₁*W.a₄*x₀*x₁*x₂*y₀ + 5*W.a₁*W.a₄*x₀*x₁*x₂*y₁ + 3*W.a₁*W.a₄*x₀*x₁*x₂*y₂ + 2*W.a₁*W.a₄*x₀*x₂^2*y₀ - 2*W.a₁*W.a₄*x₀*x₂^2*y₁ - W.a₁*W.a₄*x₀*x₂^2*y₂ + W.a₁*W.a₄*x₁^3*y₀ - W.a₁*W.a₄*x₁^3*y₂ - W.a₁*W.a₄*x₁^2*x₂*y₀ + W.a₁*W.a₄*x₁^2*x₂*y₁ + 3*W.a₁*W.a₄*x₁^2*x₂*y₂ - W.a₁*W.a₄*x₁*x₂^2*y₀ - 3*W.a₁*W.a₄*x₁*x₂^2*y₁ - W.a₁*W.a₄*x₁*x₂^2*y₂ + W.a₁*W.a₄*x₂^3*y₀ + W.a₁*W.a₄*x₂^3*y₁ - W.a₁*W.a₆*x₀^2*y₁ + W.a₁*W.a₆*x₀^2*y₂ - W.a₁*W.a₆*x₀*x₁*y₁ + W.a₁*W.a₆*x₀*x₁*y₂ + 3*W.a₁*W.a₆*x₀*x₂*y₁ - 3*W.a₁*W.a₆*x₀*x₂*y₂ + 4*W.a₁*W.a₆*x₁^2*y₀ - 4*W.a₁*W.a₆*x₁^2*y₂ - 8*W.a₁*W.a₆*x₁*x₂*y₀ + W.a₁*W.a₆*x₁*x₂*y₁ + 7*W.a₁*W.a₆*x₁*x₂*y₂ + 4*W.a₁*W.a₆*x₂^2*y₀ - 2*W.a₁*W.a₆*x₂^2*y₁ - 2*W.a₁*W.a₆*x₂^2*y₂ - 2*W.a₁*x₀^4*x₁*y₁ + 2*W.a₁*x₀^4*x₁*y₂ + 2*W.a₁*x₀^4*x₂*y₁ - 2*W.a₁*x₀^4*x₂*y₂ - W.a₁*x₀^3*x₁^2*y₁ - 3*W.a₁*x₀^3*x₁^2*y₂ + 4*W.a₁*x₀^3*x₁*x₂*y₁ + 4*W.a₁*x₀^3*x₁*x₂*y₂ - 3*W.a₁*x₀^3*x₂^2*y₁ - W.a₁*x₀^3*x₂^2*y₂ + W.a₁*x₀^2*x₁^3*y₂ - W.a₁*x₀^2*x₂^3*y₁ - W.a₁*x₀^2*y₁^2*y₂ + W.a₁*x₀^2*y₁*y₂^2 + 2*W.a₁*x₀*x₁^4*y₀ + W.a₁*x₀*x₁^4*y₁ - 2*W.a₁*x₀*x₁^4*y₂ - 2*W.a₁*x₀*x₁^3*x₂*y₀ - W.a₁*x₀*x₁^3*x₂*y₁ - 3*W.a₁*x₀*x₁^2*x₂^2*y₁ + 3*W.a₁*x₀*x₁^2*x₂^2*y₂ - 2*W.a₁*x₀*x₁*x₂^3*y₀ + 6*W.a₁*x₀*x₁*x₂^3*y₁ - 5*W.a₁*x₀*x₁*x₂^3*y₂ + 6*W.a₁*x₀*x₁*y₀^2*y₁ - 6*W.a₁*x₀*x₁*y₀^2*y₂ - 2*W.a₁*x₀*x₁*y₀*y₁*y₂ - 2*W.a₁*x₀*x₁*y₁^3 + 6*W.a₁*x₀*x₁*y₁^2*y₂ - 4*W.a₁*x₀*x₁*y₁*y₂^2 + 2*W.a₁*x₀*x₁*y₂^3 + 2*W.a₁*x₀*x₂^4*y₀ - W.a₁*x₀*x₂^4*y₁ + 2*W.a₁*x₀*x₂^4*y₂ - 6*W.a₁*x₀*x₂*y₀^2*y₁ + 6*W.a₁*x₀*x₂*y₀^2*y₂ + 2*W.a₁*x₀*x₂*y₀*y₁*y₂ + 2*W.a₁*x₀*x₂*y₁^3 - 4*W.a₁*x₀*x₂*y₁^2*y₂ + 2*W.a₁*x₀*x₂*y₁*y₂^2 - 2*W.a₁*x₀*x₂*y₂^3 - 2*W.a₁*x₁^4*x₂*y₀ - W.a₁*x₁^4*x₂*y₁ + 2*W.a₁*x₁^4*x₂*y₂ + 5*W.a₁*x₁^3*x₂^2*y₀ + W.a₁*x₁^3*x₂^2*y₁ - 4*W.a₁*x₁^3*x₂^2*y₂ - 5*W.a₁*x₁^2*x₂^3*y₀ + 4*W.a₁*x₁^2*x₂^3*y₁ + 5*W.a₁*x₁^2*x₂^3*y₂ - 3*W.a₁*x₁^2*y₀^2*y₁ + 3*W.a₁*x₁^2*y₀^2*y₂ - W.a₁*x₁^2*y₀*y₁^2 + 5*W.a₁*x₁^2*y₀*y₁*y₂ - W.a₁*x₁^2*y₀*y₂^2 + W.a₁*x₁^2*y₁^2*y₂ - 2*W.a₁*x₁^2*y₁*y₂^2 - 2*W.a₁*x₁^2*y₂^3 + 3*W.a₁*x₁*x₂^4*y₀ - 8*W.a₁*x₁*x₂^4*y₁ - 2*W.a₁*x₁*x₂^4*y₂ + 2*W.a₁*x₁*x₂*y₀*y₁^2 - 8*W.a₁*x₁*x₂*y₀*y₁*y₂ + 2*W.a₁*x₁*x₂*y₀*y₂^2 + 2*W.a₁*x₁*x₂*y₁^3 - 8*W.a₁*x₁*x₂*y₁^2*y₂ + 8*W.a₁*x₁*x₂*y₁*y₂^2 + 2*W.a₁*x₁*x₂*y₂^3 - W.a₁*x₂^5*y₀ + 3*W.a₁*x₂^5*y₁ + 3*W.a₁*x₂^2*y₀^2*y₁ - 3*W.a₁*x₂^2*y₀^2*y₂ - W.a₁*x₂^2*y₀*y₁^2 + 3*W.a₁*x₂^2*y₀*y₁*y₂ - W.a₁*x₂^2*y₀*y₂^2 - 2*W.a₁*x₂^2*y₁^3 + 6*W.a₁*x₂^2*y₁^2*y₂ - 5*W.a₁*x₂^2*y₁*y₂^2 - 4*W.a₂*x₀^2*x₁*y₀*y₁ + 4*W.a₂*x₀^2*x₁*y₀*y₂ - 2*W.a₂*x₀^2*x₁*y₁^2 + 2*W.a₂*x₀^2*x₁*y₂^2 + 4*W.a₂*x₀^2*x₂*y₀*y₁ - 4*W.a₂*x₀^2*x₂*y₀*y₂ + 2*W.a₂*x₀^2*x₂*y₁^2 - 2*W.a₂*x₀^2*x₂*y₂^2 + 2*W.a₂*x₀*x₁^2*y₀*y₂ + W.a₂*x₀*x₁^2*y₁^2 - W.a₂*x₀*x₁^2*y₁*y₂ - 2*W.a₂*x₀*x₁^2*y₂^2 - 2*W.a₂*x₀*x₁*x₂*y₁^2 + 4*W.a₂*x₀*x₁*x₂*y₁*y₂ - 2*W.a₂*x₀*x₁*x₂*y₂^2 - 2*W.a₂*x₀*x₂^2*y₀*y₁ + W.a₂*x₀*x₂^2*y₁*y₂ + W.a₂*x₀*x₂^2*y₂^2 + 4*W.a₂*x₁^3*y₀^2 + W.a₂*x₁^3*y₀*y₁ - 8*W.a₂*x₁^3*y₀*y₂ - W.a₂*x₁^3*y₁*y₂ + 4*W.a₂*x₁^3*y₂^2 - 4*W.a₂*x₁^2*x₂*y₀^2 + W.a₂*x₁^2*x₂*y₀*y₁ + 4*W.a₂*x₁^2*x₂*y₀*y₂ - W.a₂*x₁^2*x₂*y₁^2 - 4*W.a₂*x₁*x₂^2*y₀^2 + 6*W.a₂*x₁*x₂^2*y₀*y₁ + W.a₂*x₁*x₂^2*y₀*y₂ + 4*W.a₂*x₁*x₂^2*y₁^2 - 6*W.a₂*x₁*x₂^2*y₁*y₂ - W.a₂*x₁*x₂^2*y₂^2 + 4*W.a₂*x₂^3*y₀^2 - 6*W.a₂*x₂^3*y₀*y₁ + W.a₂*x₂^3*y₀*y₂ - 2*W.a₂*x₂^3*y₁^2 + 3*W.a₂*x₂^3*y₁*y₂ - 4*W.a₄*x₀*x₁*y₀*y₁ + 6*W.a₄*x₀*x₁*y₀*y₂ - 2*W.a₄*x₀*x₁*y₁^2 + W.a₄*x₀*x₁*y₁*y₂ - W.a₄*x₀*x₁*y₂^2 + 2*W.a₄*x₀*x₂*y₀*y₁ - 4*W.a₄*x₀*x₂*y₀*y₂ + W.a₄*x₀*x₂*y₁^2 + 3*W.a₄*x₀*x₂*y₁*y₂ - 2*W.a₄*x₀*x₂*y₂^2 + 4*W.a₄*x₁^2*y₀^2 + 2*W.a₄*x₁^2*y₀*y₁ - 9*W.a₄*x₁^2*y₀*y₂ - 2*W.a₄*x₁^2*y₁*y₂ + 5*W.a₄*x₁^2*y₂^2 - 8*W.a₄*x₁*x₂*y₀^2 + 7*W.a₄*x₁*x₂*y₀*y₁ + 5*W.a₄*x₁*x₂*y₀*y₂ + 2*W.a₄*x₁*x₂*y₁^2 - 4*W.a₄*x₁*x₂*y₁*y₂ - 2*W.a₄*x₁*x₂*y₂^2 + 4*W.a₄*x₂^2*y₀^2 - 7*W.a₄*x₂^2*y₀*y₁ + 2*W.a₄*x₂^2*y₀*y₂ - W.a₄*x₂^2*y₁^2 + 2*W.a₄*x₂^2*y₁*y₂ - 2*W.a₆*x₀*y₀*y₁ + 2*W.a₆*x₀*y₀*y₂ - W.a₆*x₀*y₁^2 + 4*W.a₆*x₀*y₁*y₂ - 3*W.a₆*x₀*y₂^2 + 7*W.a₆*x₁*y₀*y₁ - 7*W.a₆*x₁*y₀*y₂ - 7*W.a₆*x₁*y₁*y₂ + 7*W.a₆*x₁*y₂^2 - 5*W.a₆*x₂*y₀*y₁ + 5*W.a₆*x₂*y₀*y₂ + W.a₆*x₂*y₁^2 + 3*W.a₆*x₂*y₁*y₂ - 4*W.a₆*x₂*y₂^2 - 4*x₀^3*x₁*y₀*y₁ + 4*x₀^3*x₁*y₀*y₂ - 2*x₀^3*x₁*y₁^2 + 2*x₀^3*x₁*y₂^2 + 4*x₀^3*x₂*y₀*y₁ - 4*x₀^3*x₂*y₀*y₂ + 2*x₀^3*x₂*y₁^2 - 2*x₀^3*x₂*y₂^2 + 2*x₀*x₁^3*y₀*y₂ + x₀*x₁^3*y₁^2 - x₀*x₁^3*y₁*y₂ - 2*x₀*x₁^3*y₂^2 - 3*x₀*x₁*x₂^2*y₁^2 + 6*x₀*x₁*x₂^2*y₁*y₂ - 3*x₀*x₁*x₂^2*y₂^2 - 2*x₀*x₂^3*y₀*y₁ + x₀*x₂^3*y₁^2 - x₀*x₂^3*y₁*y₂ + 2*x₀*x₂^3*y₂^2 - 2*x₀*y₀*y₁^2*y₂ + 2*x₀*y₀*y₁*y₂^2 - x₀*y₁^4 + 3*x₀*y₁^3*y₂ - 2*x₀*y₁^2*y₂^2 + x₀*y₁*y₂^3 - x₀*y₂^4 + 4*x₁^4*y₀^2 + x₁^4*y₀*y₁ - 8*x₁^4*y₀*y₂ - x₁^4*y₁*y₂ + 4*x₁^4*y₂^2 - 4*x₁^3*x₂*y₀^2 - x₁^3*x₂*y₀*y₁ + 6*x₁^3*x₂*y₀*y₂ - x₁^3*x₂*y₁^2 + 2*x₁^3*x₂*y₁*y₂ - 2*x₁^3*x₂*y₂^2 + 3*x₁^2*x₂^2*y₀*y₁ - 3*x₁^2*x₂^2*y₀*y₂ - 3*x₁^2*x₂^2*y₁*y₂ + 3*x₁^2*x₂^2*y₂^2 - 4*x₁*x₂^3*y₀^2 + 4*x₁*x₂^3*y₀*y₁ + 3*x₁*x₂^3*y₀*y₂ + 5*x₁*x₂^3*y₁^2 - 6*x₁*x₂^3*y₁*y₂ - 2*x₁*x₂^3*y₂^2 + 4*x₁*y₀^3*y₁ - 4*x₁*y₀^3*y₂ - 2*x₁*y₀^2*y₁^2 + 2*x₁*y₀^2*y₂^2 - x₁*y₀*y₁^3 + 6*x₁*y₀*y₁^2*y₂ - 6*x₁*y₀*y₁*y₂^2 + x₁*y₀*y₂^3 + x₁*y₁^3*y₂ - 4*x₁*y₁^2*y₂^2 + 2*x₁*y₁*y₂^3 + x₁*y₂^4 + 4*x₂^4*y₀^2 - 5*x₂^4*y₀*y₁ - 3*x₂^4*y₁^2 + 4*x₂^4*y₁*y₂ - 4*x₂*y₀^3*y₁ + 4*x₂*y₀^3*y₂ + 2*x₂*y₀^2*y₁^2 - 2*x₂*y₀^2*y₂^2 + x₂*y₀*y₁^3 - 4*x₂*y₀*y₁^2*y₂ + 4*x₂*y₀*y₁*y₂^2 - x₂*y₀*y₂^3 + x₂*y₁^4 - 4*x₂*y₁^3*y₂ + 6*x₂*y₁^2*y₂^2 - 3*x₂*y₁*y₂^3) * hord

/-! ### `velu2_tangent_negAddY_cleared_identity` — The tangent `negAddY` cleared identity. -/

set_option maxRecDepth 8000 in
theorem velu2_tangent_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hy : y ≠ W.toAffine.negY x y) :
    (x - x₀) * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
          * (x - W.toAffine.addX x x (W.toAffine.slope x x y y)) * (y - y₀)
        - (x - x₀)
          * ((W.a₁ * (x - x₀) + y - y₀)
                * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
                    + W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀)
                * (x - x₀) ^ 2)
        + W.veluGx x₀ y₀
          * ((W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - y₀)
              - (x - x₀) * (W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀))
      = 0 := by
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  rw [Affine.equation_iff] at hP hQ
  simp only [Affine.slope_of_Y_ne rfl hy, Affine.addX, Affine.negAddY, veluGx]
  field_simp [hsd]
  simp only [Affine.negY]
  linear_combination
    (-W.a₁^6*x^3*y + 3*W.a₁^6*x^2*x₀*y - 3*W.a₁^6*x*x₀^2*y + W.a₁^6*x₀^3*y + W.a₁^5*W.a₂*x^4 - 2*W.a₁^5*W.a₂*x^3*x₀ - W.a₁^5*W.a₂*x^2*x₀^2 + 4*W.a₁^5*W.a₂*x*x₀^3 - 2*W.a₁^5*W.a₂*x₀^4 + W.a₁^5*W.a₄*x^3 - 4*W.a₁^5*W.a₄*x^2*x₀ + 5*W.a₁^5*W.a₄*x*x₀^2 - 2*W.a₁^5*W.a₄*x₀^3 - W.a₁^5*W.a₆*x^2 + 2*W.a₁^5*W.a₆*x*x₀ - W.a₁^5*W.a₆*x₀^2 + 3*W.a₁^5*x^4*x₀ - 9*W.a₁^5*x^3*x₀^2 + 8*W.a₁^5*x^2*x₀^3 - 3*W.a₁^5*x^2*y^2 + 6*W.a₁^5*x^2*y*y₀ - W.a₁^5*x^2*y₀^2 - W.a₁^5*x*x₀^4 + 6*W.a₁^5*x*x₀*y^2 - 12*W.a₁^5*x*x₀*y*y₀ + 2*W.a₁^5*x*x₀*y₀^2 - W.a₁^5*x₀^5 - 3*W.a₁^5*x₀^2*y^2 + 6*W.a₁^5*x₀^2*y*y₀ - W.a₁^5*x₀^2*y₀^2 - 6*W.a₁^4*W.a₂*x^3*y - 4*W.a₁^4*W.a₂*x^3*y₀ + 18*W.a₁^4*W.a₂*x^2*x₀*y - 20*W.a₁^4*W.a₂*x*x₀^2*y + 16*W.a₁^4*W.a₂*x*x₀^2*y₀ + 8*W.a₁^4*W.a₂*x₀^3*y - 12*W.a₁^4*W.a₂*x₀^3*y₀ - 6*W.a₁^4*W.a₄*x^2*y₀ - 2*W.a₁^4*W.a₄*x*x₀*y + 16*W.a₁^4*W.a₄*x*x₀*y₀ + 2*W.a₁^4*W.a₄*x₀^2*y - 10*W.a₁^4*W.a₄*x₀^2*y₀ - 2*W.a₁^4*W.a₆*x*y + 4*W.a₁^4*W.a₆*x*y₀ + 2*W.a₁^4*W.a₆*x₀*y - 4*W.a₁^4*W.a₆*x₀*y₀ - 18*W.a₁^4*x^4*y + 6*W.a₁^4*x^4*y₀ + 54*W.a₁^4*x^3*x₀*y - 36*W.a₁^4*x^3*x₀*y₀ - 54*W.a₁^4*x^2*x₀^2*y + 54*W.a₁^4*x^2*x₀^2*y₀ + 16*W.a₁^4*x*x₀^3*y - 20*W.a₁^4*x*x₀^3*y₀ - 2*W.a₁^4*x*y^3 + 12*W.a₁^4*x*y^2*y₀ - 14*W.a₁^4*x*y*y₀^2 + 4*W.a₁^4*x*y₀^3 + 2*W.a₁^4*x₀^4*y - 4*W.a₁^4*x₀^4*y₀ + 2*W.a₁^4*x₀*y^3 - 12*W.a₁^4*x₀*y^2*y₀ + 14*W.a₁^4*x₀*y*y₀^2 - 4*W.a₁^4*x₀*y₀^3 + 8*W.a₁^3*W.a₂^2*x^4 - 12*W.a₁^3*W.a₂^2*x^3*x₀ - 8*W.a₁^3*W.a₂^2*x^2*x₀^2 + 16*W.a₁^3*W.a₂^2*x*x₀^3 - 4*W.a₁^3*W.a₂^2*x₀^4 + 10*W.a₁^3*W.a₂*W.a₄*x^3 - 26*W.a₁^3*W.a₂*W.a₄*x^2*x₀ + 16*W.a₁^3*W.a₂*W.a₄*x*x₀^2 - 8*W.a₁^3*W.a₂*W.a₆*x^2 + 12*W.a₁^3*W.a₂*W.a₆*x*x₀ - 4*W.a₁^3*W.a₂*W.a₆*x₀^2 + 18*W.a₁^3*W.a₂*x^5 - 18*W.a₁^3*W.a₂*x^4*x₀ - 36*W.a₁^3*W.a₂*x^3*x₀^2 + 40*W.a₁^3*W.a₂*x^2*x₀^3 - 24*W.a₁^3*W.a₂*x^2*y^2 + 36*W.a₁^3*W.a₂*x^2*y*y₀ - 8*W.a₁^3*W.a₂*x^2*y₀^2 + 36*W.a₁^3*W.a₂*x*x₀*y^2 - 72*W.a₁^3*W.a₂*x*x₀*y*y₀ + 36*W.a₁^3*W.a₂*x*x₀*y₀^2 - 4*W.a₁^3*W.a₂*x₀^5 - 12*W.a₁^3*W.a₂*x₀^2*y^2 + 40*W.a₁^3*W.a₂*x₀^2*y*y₀ - 32*W.a₁^3*W.a₂*x₀^2*y₀^2 + 3*W.a₁^3*W.a₄^2*x^2 - 8*W.a₁^3*W.a₄^2*x*x₀ + 5*W.a₁^3*W.a₄^2*x₀^2 - 2*W.a₁^3*W.a₄*W.a₆*x + 2*W.a₁^3*W.a₄*W.a₆*x₀ + 12*W.a₁^3*W.a₄*x^4 - 36*W.a₁^3*W.a₄*x^3*x₀ + 30*W.a₁^3*W.a₄*x^2*x₀^2 - 8*W.a₁^3*W.a₄*x*x₀^3 - 6*W.a₁^3*W.a₄*x*y^2 + 10*W.a₁^3*W.a₄*x*y₀^2 + 2*W.a₁^3*W.a₄*x₀^4 + 6*W.a₁^3*W.a₄*x₀*y^2 + 4*W.a₁^3*W.a₄*x₀*y*y₀ - 14*W.a₁^3*W.a₄*x₀*y₀^2 - 18*W.a₁^3*W.a₆*x^3 + 30*W.a₁^3*W.a₆*x^2*x₀ - 12*W.a₁^3*W.a₆*x*x₀^2 + 4*W.a₁^3*W.a₆*y*y₀ - 4*W.a₁^3*W.a₆*y₀^2 + 9*W.a₁^3*x^6 - 27*W.a₁^3*x^4*x₀^2 - 54*W.a₁^3*x^3*y^2 + 108*W.a₁^3*x^3*y*y₀ - 54*W.a₁^3*x^3*y₀^2 + 30*W.a₁^3*x^2*x₀^4 + 90*W.a₁^3*x^2*x₀*y^2 - 216*W.a₁^3*x^2*x₀*y*y₀ + 138*W.a₁^3*x^2*x₀*y₀^2 - 12*W.a₁^3*x*x₀^5 - 36*W.a₁^3*x*x₀^2*y^2 + 108*W.a₁^3*x*x₀^2*y*y₀ - 84*W.a₁^3*x*x₀^2*y₀^2 + 4*W.a₁^3*x₀^3*y*y₀ - 4*W.a₁^3*x₀^3*y₀^2 + 4*W.a₁^3*y^3*y₀ - 12*W.a₁^3*y^2*y₀^2 + 12*W.a₁^3*y*y₀^3 - 4*W.a₁^3*y₀^4 - 24*W.a₁^2*W.a₂^2*x^3*y₀ + 24*W.a₁^2*W.a₂^2*x^2*x₀*y - 40*W.a₁^2*W.a₂^2*x*x₀^2*y + 48*W.a₁^2*W.a₂^2*x*x₀^2*y₀ + 8*W.a₁^2*W.a₂^2*x₀^3*y - 16*W.a₁^2*W.a₂^2*x₀^3*y₀ + 12*W.a₁^2*W.a₂*W.a₄*x^2*y - 36*W.a₁^2*W.a₂*W.a₄*x^2*y₀ - 16*W.a₁^2*W.a₂*W.a₄*x*x₀*y + 48*W.a₁^2*W.a₂*W.a₄*x*x₀*y₀ - 8*W.a₁^2*W.a₂*W.a₄*x₀^2*y - 16*W.a₁^2*W.a₂*W.a₆*x*y + 24*W.a₁^2*W.a₂*W.a₆*x*y₀ + 8*W.a₁^2*W.a₂*W.a₆*x₀*y - 16*W.a₁^2*W.a₂*W.a₆*x₀*y₀ - 36*W.a₁^2*W.a₂*x^4*y - 36*W.a₁^2*W.a₂*x^4*y₀ + 144*W.a₁^2*W.a₂*x^3*x₀*y - 72*W.a₁^2*W.a₂*x^3*x₀*y₀ - 144*W.a₁^2*W.a₂*x^2*x₀^2*y + 168*W.a₁^2*W.a₂*x^2*x₀^2*y₀ + 8*W.a₁^2*W.a₂*x*x₀^3*y - 24*W.a₁^2*W.a₂*x*x₀^3*y₀ - 16*W.a₁^2*W.a₂*x*y^3 + 72*W.a₁^2*W.a₂*x*y^2*y₀ - 88*W.a₁^2*W.a₂*x*y*y₀^2 + 40*W.a₁^2*W.a₂*x*y₀^3 + 8*W.a₁^2*W.a₂*x₀^4*y - 16*W.a₁^2*W.a₂*x₀^4*y₀ + 8*W.a₁^2*W.a₂*x₀*y^3 - 48*W.a₁^2*W.a₂*x₀*y^2*y₀ + 80*W.a₁^2*W.a₂*x₀*y*y₀^2 - 48*W.a₁^2*W.a₂*x₀*y₀^3 + 6*W.a₁^2*W.a₄^2*x*y - 12*W.a₁^2*W.a₄^2*x*y₀ - 10*W.a₁^2*W.a₄^2*x₀*y + 16*W.a₁^2*W.a₄^2*x₀*y₀ - 4*W.a₁^2*W.a₄*W.a₆*y + 4*W.a₁^2*W.a₄*W.a₆*y₀ - 36*W.a₁^2*W.a₄*x^3*y₀ + 60*W.a₁^2*W.a₄*x^2*x₀*y₀ - 12*W.a₁^2*W.a₄*x*x₀^2*y - 12*W.a₁^2*W.a₄*x*x₀^2*y₀ - 4*W.a₁^2*W.a₄*x₀^3*y + 4*W.a₁^2*W.a₄*x₀^3*y₀ - 4*W.a₁^2*W.a₄*y^3 + 12*W.a₁^2*W.a₄*y^2*y₀ - 4*W.a₁^2*W.a₄*y*y₀^2 - 4*W.a₁^2*W.a₄*y₀^3 - 36*W.a₁^2*W.a₆*x^2*y + 60*W.a₁^2*W.a₆*x^2*y₀ + 24*W.a₁^2*W.a₆*x*x₀*y - 48*W.a₁^2*W.a₆*x*x₀*y₀ - 54*W.a₁^2*x^5*y + 162*W.a₁^2*x^4*x₀*y - 108*W.a₁^2*x^4*x₀*y₀ - 108*W.a₁^2*x^3*x₀^2*y + 108*W.a₁^2*x^3*x₀^2*y₀ - 36*W.a₁^2*x^2*x₀^3*y + 60*W.a₁^2*x^2*x₀^3*y₀ - 36*W.a₁^2*x^2*y^3 + 180*W.a₁^2*x^2*y^2*y₀ - 252*W.a₁^2*x^2*y*y₀^2 + 132*W.a₁^2*x^2*y₀^3 + 24*W.a₁^2*x*x₀^4*y - 48*W.a₁^2*x*x₀^4*y₀ + 24*W.a₁^2*x*x₀*y^3 - 144*W.a₁^2*x*x₀*y^2*y₀ + 240*W.a₁^2*x*x₀*y*y₀^2 - 144*W.a₁^2*x*x₀*y₀^3 + 16*W.a₁*W.a₂^3*x^4 - 16*W.a₁*W.a₂^3*x^3*x₀ - 16*W.a₁*W.a₂^3*x^2*x₀^2 + 16*W.a₁*W.a₂^3*x*x₀^3 + 24*W.a₁*W.a₂^2*W.a₄*x^3 - 40*W.a₁*W.a₂^2*W.a₄*x^2*x₀ + 8*W.a₁*W.a₂^2*W.a₄*x*x₀^2 + 8*W.a₁*W.a₂^2*W.a₄*x₀^3 - 16*W.a₁*W.a₂^2*W.a₆*x^2 + 16*W.a₁*W.a₂^2*W.a₆*x*x₀ + 72*W.a₁*W.a₂^2*x^5 - 72*W.a₁*W.a₂^2*x^4*x₀ - 72*W.a₁*W.a₂^2*x^3*x₀^2 + 56*W.a₁*W.a₂^2*x^2*x₀^3 - 48*W.a₁*W.a₂^2*x^2*y^2 + 48*W.a₁*W.a₂^2*x^2*y*y₀ - 16*W.a₁*W.a₂^2*x^2*y₀^2 + 16*W.a₁*W.a₂^2*x*x₀^4 + 48*W.a₁*W.a₂^2*x*x₀*y^2 - 96*W.a₁*W.a₂^2*x*x₀*y*y₀ + 64*W.a₁*W.a₂^2*x*x₀*y₀^2 + 16*W.a₁*W.a₂^2*x₀^2*y*y₀ - 16*W.a₁*W.a₂^2*x₀^2*y₀^2 + 12*W.a₁*W.a₂*W.a₄^2*x^2 - 20*W.a₁*W.a₂*W.a₄^2*x*x₀ + 8*W.a₁*W.a₂*W.a₄^2*x₀^2 - 8*W.a₁*W.a₂*W.a₄*W.a₆*x + 8*W.a₁*W.a₂*W.a₄*W.a₆*x₀ + 72*W.a₁*W.a₂*W.a₄*x^4 - 144*W.a₁*W.a₂*W.a₄*x^3*x₀ + 48*W.a₁*W.a₂*W.a₄*x^2*x₀^2 + 16*W.a₁*W.a₂*W.a₄*x*x₀^3 - 24*W.a₁*W.a₂*W.a₄*x*y^2 + 16*W.a₁*W.a₂*W.a₄*x*y₀^2 + 8*W.a₁*W.a₂*W.a₄*x₀^4 + 24*W.a₁*W.a₂*W.a₄*x₀*y^2 - 32*W.a₁*W.a₂*W.a₄*x₀*y*y₀ + 16*W.a₁*W.a₂*W.a₄*x₀*y₀^2 - 72*W.a₁*W.a₂*W.a₆*x^3 + 72*W.a₁*W.a₂*W.a₆*x^2*x₀ + 16*W.a₁*W.a₂*W.a₆*y*y₀ - 16*W.a₁*W.a₂*W.a₆*y₀^2 + 108*W.a₁*W.a₂*x^6 - 108*W.a₁*W.a₂*x^5*x₀ - 72*W.a₁*W.a₂*x^4*x₀^2 - 216*W.a₁*W.a₂*x^3*y^2 + 288*W.a₁*W.a₂*x^3*y*y₀ - 144*W.a₁*W.a₂*x^3*y₀^2 + 72*W.a₁*W.a₂*x^2*x₀^4 + 216*W.a₁*W.a₂*x^2*x₀*y^2 - 432*W.a₁*W.a₂*x^2*x₀*y*y₀ + 288*W.a₁*W.a₂*x^2*x₀*y₀^2 + 48*W.a₁*W.a₂*x*x₀^2*y*y₀ - 48*W.a₁*W.a₂*x*x₀^2*y₀^2 + 16*W.a₁*W.a₂*x₀^3*y*y₀ - 16*W.a₁*W.a₂*x₀^3*y₀^2 + 16*W.a₁*W.a₂*y^3*y₀ - 48*W.a₁*W.a₂*y^2*y₀^2 + 64*W.a₁*W.a₂*y*y₀^3 - 32*W.a₁*W.a₂*y₀^4 + 2*W.a₁*W.a₄^3*x - 2*W.a₁*W.a₄^3*x₀ + 18*W.a₁*W.a₄^2*x^3 - 42*W.a₁*W.a₄^2*x^2*x₀ + 24*W.a₁*W.a₄^2*x*x₀^2 - 12*W.a₁*W.a₄^2*y*y₀ + 12*W.a₁*W.a₄^2*y₀^2 - 24*W.a₁*W.a₄*W.a₆*x^2 + 24*W.a₁*W.a₄*W.a₆*x*x₀ + 54*W.a₁*W.a₄*x^5 - 126*W.a₁*W.a₄*x^4*x₀ + 72*W.a₁*W.a₄*x^3*x₀^2 - 24*W.a₁*W.a₄*x^2*x₀^3 - 72*W.a₁*W.a₄*x^2*y^2 + 72*W.a₁*W.a₄*x^2*y*y₀ - 24*W.a₁*W.a₄*x^2*y₀^2 + 24*W.a₁*W.a₄*x*x₀^4 + 72*W.a₁*W.a₄*x*x₀*y^2 - 96*W.a₁*W.a₄*x*x₀*y*y₀ + 48*W.a₁*W.a₄*x*x₀*y₀^2 - 72*W.a₁*W.a₆*x^4 + 72*W.a₁*W.a₆*x^3*x₀ + 48*W.a₁*W.a₆*x*y*y₀ - 48*W.a₁*W.a₆*x*y₀^2 + 54*W.a₁*x^7 - 54*W.a₁*x^6*x₀ - 72*W.a₁*x^4*x₀^3 - 216*W.a₁*x^4*y^2 + 324*W.a₁*x^4*y*y₀ - 180*W.a₁*x^4*y₀^2 + 72*W.a₁*x^3*x₀^4 + 216*W.a₁*x^3*x₀*y^2 - 432*W.a₁*x^3*x₀*y*y₀ + 288*W.a₁*x^3*x₀*y₀^2 + 48*W.a₁*x*x₀^3*y*y₀ - 48*W.a₁*x*x₀^3*y₀^2 + 48*W.a₁*x*y^3*y₀ - 144*W.a₁*x*y^2*y₀^2 + 192*W.a₁*x*y*y₀^3 - 96*W.a₁*x*y₀^4 + 32*W.a₂^3*x^3*y - 32*W.a₂^3*x^3*y₀ - 32*W.a₂^3*x*x₀^2*y + 32*W.a₂^3*x*x₀^2*y₀ + 48*W.a₂^2*W.a₄*x^2*y - 48*W.a₂^2*W.a₄*x^2*y₀ - 32*W.a₂^2*W.a₄*x*x₀*y + 32*W.a₂^2*W.a₄*x*x₀*y₀ - 16*W.a₂^2*W.a₄*x₀^2*y + 16*W.a₂^2*W.a₄*x₀^2*y₀ - 32*W.a₂^2*W.a₆*x*y + 32*W.a₂^2*W.a₆*x*y₀ + 144*W.a₂^2*x^4*y - 144*W.a₂^2*x^4*y₀ - 144*W.a₂^2*x^2*x₀^2*y + 144*W.a₂^2*x^2*x₀^2*y₀ - 32*W.a₂^2*x*x₀^3*y + 32*W.a₂^2*x*x₀^3*y₀ - 32*W.a₂^2*x*y^3 + 96*W.a₂^2*x*y^2*y₀ - 128*W.a₂^2*x*y*y₀^2 + 64*W.a₂^2*x*y₀^3 + 24*W.a₂*W.a₄^2*x*y - 24*W.a₂*W.a₄^2*x*y₀ - 16*W.a₂*W.a₄^2*x₀*y + 16*W.a₂*W.a₄^2*x₀*y₀ - 16*W.a₂*W.a₄*W.a₆*y + 16*W.a₂*W.a₄*W.a₆*y₀ + 144*W.a₂*W.a₄*x^3*y - 144*W.a₂*W.a₄*x^3*y₀ - 144*W.a₂*W.a₄*x^2*x₀*y + 144*W.a₂*W.a₄*x^2*x₀*y₀ - 48*W.a₂*W.a₄*x*x₀^2*y + 48*W.a₂*W.a₄*x*x₀^2*y₀ - 16*W.a₂*W.a₄*x₀^3*y + 16*W.a₂*W.a₄*x₀^3*y₀ - 16*W.a₂*W.a₄*y^3 + 48*W.a₂*W.a₄*y^2*y₀ - 64*W.a₂*W.a₄*y*y₀^2 + 32*W.a₂*W.a₄*y₀^3 - 144*W.a₂*W.a₆*x^2*y + 144*W.a₂*W.a₆*x^2*y₀ + 216*W.a₂*x^5*y - 216*W.a₂*x^5*y₀ - 144*W.a₂*x^3*x₀^2*y + 144*W.a₂*x^3*x₀^2*y₀ - 144*W.a₂*x^2*x₀^3*y + 144*W.a₂*x^2*x₀^3*y₀ - 144*W.a₂*x^2*y^3 + 432*W.a₂*x^2*y^2*y₀ - 576*W.a₂*x^2*y*y₀^2 + 288*W.a₂*x^2*y₀^3 + 4*W.a₄^3*y - 4*W.a₄^3*y₀ + 36*W.a₄^2*x^2*y - 36*W.a₄^2*x^2*y₀ - 48*W.a₄^2*x*x₀*y + 48*W.a₄^2*x*x₀*y₀ - 48*W.a₄*W.a₆*x*y + 48*W.a₄*W.a₆*x*y₀ + 108*W.a₄*x^4*y - 108*W.a₄*x^4*y₀ - 144*W.a₄*x^3*x₀*y + 144*W.a₄*x^3*x₀*y₀ - 48*W.a₄*x*x₀^3*y + 48*W.a₄*x*x₀^3*y₀ - 48*W.a₄*x*y^3 + 144*W.a₄*x*y^2*y₀ - 192*W.a₄*x*y*y₀^2 + 96*W.a₄*x*y₀^3 - 144*W.a₆*x^3*y + 144*W.a₆*x^3*y₀ + 108*x^6*y - 108*x^6*y₀ - 144*x^3*x₀^3*y + 144*x^3*x₀^3*y₀ - 144*x^3*y^3 + 432*x^3*y^2*y₀ - 576*x^3*y*y₀^2 + 288*x^3*y₀^3) * hP
    + (W.a₁^5*W.a₂*x^2*x₀^2 - 2*W.a₁^5*W.a₂*x*x₀^3 + W.a₁^5*W.a₂*x₀^4 + W.a₁^5*W.a₄*x^2*x₀ - 2*W.a₁^5*W.a₄*x*x₀^2 + W.a₁^5*W.a₄*x₀^3 + W.a₁^5*W.a₆*x^2 - 2*W.a₁^5*W.a₆*x*x₀ + W.a₁^5*W.a₆*x₀^2 + W.a₁^5*x^5 - 5*W.a₁^5*x^4*x₀ + 10*W.a₁^5*x^3*x₀^2 - 9*W.a₁^5*x^2*x₀^3 + 3*W.a₁^5*x*x₀^4 + 4*W.a₁^4*W.a₂*x^2*x₀*y₀ + 2*W.a₁^4*W.a₂*x*x₀^2*y - 12*W.a₁^4*W.a₂*x*x₀^2*y₀ - 2*W.a₁^4*W.a₂*x₀^3*y + 8*W.a₁^4*W.a₂*x₀^3*y₀ + 2*W.a₁^4*W.a₄*x^2*y₀ + 2*W.a₁^4*W.a₄*x*x₀*y - 8*W.a₁^4*W.a₄*x*x₀*y₀ - 2*W.a₁^4*W.a₄*x₀^2*y + 6*W.a₁^4*W.a₄*x₀^2*y₀ + 2*W.a₁^4*W.a₆*x*y - 4*W.a₁^4*W.a₆*x*y₀ - 2*W.a₁^4*W.a₆*x₀*y + 4*W.a₁^4*W.a₆*x₀*y₀ + 2*W.a₁^4*x^4*y - 10*W.a₁^4*x^4*y₀ - 8*W.a₁^4*x^3*x₀*y + 40*W.a₁^4*x^3*x₀*y₀ + 12*W.a₁^4*x^2*x₀^2*y - 54*W.a₁^4*x^2*x₀^2*y₀ - 6*W.a₁^4*x*x₀^3*y + 24*W.a₁^4*x*x₀^3*y₀ + 4*W.a₁^3*W.a₂^2*x^2*x₀^2 - 4*W.a₁^3*W.a₂^2*x*x₀^3 + 4*W.a₁^3*W.a₂*W.a₄*x^2*x₀ - 2*W.a₁^3*W.a₂*W.a₄*x*x₀^2 - 2*W.a₁^3*W.a₂*W.a₄*x₀^3 + 8*W.a₁^3*W.a₂*W.a₆*x^2 - 12*W.a₁^3*W.a₂*W.a₆*x*x₀ + 4*W.a₁^3*W.a₂*W.a₆*x₀^2 + 8*W.a₁^3*W.a₂*x^5 - 24*W.a₁^3*W.a₂*x^4*x₀ + 34*W.a₁^3*W.a₂*x^3*x₀^2 - 18*W.a₁^3*W.a₂*x^2*x₀^3 + 4*W.a₁^3*W.a₂*x^2*y₀^2 + 8*W.a₁^3*W.a₂*x*x₀*y*y₀ - 24*W.a₁^3*W.a₂*x*x₀*y₀^2 - 12*W.a₁^3*W.a₂*x₀^2*y*y₀ + 24*W.a₁^3*W.a₂*x₀^2*y₀^2 - W.a₁^3*W.a₄^2*x^2 + 4*W.a₁^3*W.a₄^2*x*x₀ - 3*W.a₁^3*W.a₄^2*x₀^2 + 2*W.a₁^3*W.a₄*W.a₆*x - 2*W.a₁^3*W.a₄*W.a₆*x₀ + 8*W.a₁^3*W.a₄*x^4 - 14*W.a₁^3*W.a₄*x^3*x₀ + 12*W.a₁^3*W.a₄*x^2*x₀^2 - 6*W.a₁^3*W.a₄*x*x₀^3 + 4*W.a₁^3*W.a₄*x*y*y₀ - 8*W.a₁^3*W.a₄*x*y₀^2 - 8*W.a₁^3*W.a₄*x₀*y*y₀ + 12*W.a₁^3*W.a₄*x₀*y₀^2 + 18*W.a₁^3*W.a₆*x^3 - 30*W.a₁^3*W.a₆*x^2*x₀ + 12*W.a₁^3*W.a₆*x*x₀^2 - 4*W.a₁^3*W.a₆*y*y₀ + 4*W.a₁^3*W.a₆*y₀^2 + 9*W.a₁^3*x^6 - 30*W.a₁^3*x^5*x₀ + 39*W.a₁^3*x^4*x₀^2 - 18*W.a₁^3*x^3*x₀^3 - 16*W.a₁^3*x^3*y*y₀ + 40*W.a₁^3*x^3*y₀^2 + 48*W.a₁^3*x^2*x₀*y*y₀ - 108*W.a₁^3*x^2*x₀*y₀^2 - 36*W.a₁^3*x*x₀^2*y*y₀ + 72*W.a₁^3*x*x₀^2*y₀^2 + 16*W.a₁^2*W.a₂^2*x^2*x₀*y₀ + 8*W.a₁^2*W.a₂^2*x*x₀^2*y - 24*W.a₁^2*W.a₂^2*x*x₀^2*y₀ + 8*W.a₁^2*W.a₂*W.a₄*x^2*y₀ + 8*W.a₁^2*W.a₂*W.a₄*x*x₀*y - 8*W.a₁^2*W.a₂*W.a₄*x*x₀*y₀ + 4*W.a₁^2*W.a₂*W.a₄*x₀^2*y - 12*W.a₁^2*W.a₂*W.a₄*x₀^2*y₀ + 16*W.a₁^2*W.a₂*W.a₆*x*y - 24*W.a₁^2*W.a₂*W.a₆*x*y₀ - 8*W.a₁^2*W.a₂*W.a₆*x₀*y + 16*W.a₁^2*W.a₂*W.a₆*x₀*y₀ + 16*W.a₁^2*W.a₂*x^4*y - 48*W.a₁^2*W.a₂*x^4*y₀ - 32*W.a₁^2*W.a₂*x^3*x₀*y + 136*W.a₁^2*W.a₂*x^3*x₀*y₀ + 36*W.a₁^2*W.a₂*x^2*x₀^2*y - 108*W.a₁^2*W.a₂*x^2*x₀^2*y₀ + 8*W.a₁^2*W.a₂*x*y*y₀^2 - 16*W.a₁^2*W.a₂*x*y₀^3 - 24*W.a₁^2*W.a₂*x₀*y*y₀^2 + 32*W.a₁^2*W.a₂*x₀*y₀^3 - 2*W.a₁^2*W.a₄^2*x*y + 8*W.a₁^2*W.a₄^2*x*y₀ + 6*W.a₁^2*W.a₄^2*x₀*y - 12*W.a₁^2*W.a₄^2*x₀*y₀ + 4*W.a₁^2*W.a₄*W.a₆*y - 4*W.a₁^2*W.a₄*W.a₆*y₀ + 16*W.a₁^2*W.a₄*x^3*y - 28*W.a₁^2*W.a₄*x^3*y₀ - 12*W.a₁^2*W.a₄*x^2*x₀*y + 48*W.a₁^2*W.a₄*x^2*x₀*y₀ + 12*W.a₁^2*W.a₄*x*x₀^2*y - 36*W.a₁^2*W.a₄*x*x₀^2*y₀ - 8*W.a₁^2*W.a₄*y*y₀^2 + 8*W.a₁^2*W.a₄*y₀^3 + 36*W.a₁^2*W.a₆*x^2*y - 60*W.a₁^2*W.a₆*x^2*y₀ - 24*W.a₁^2*W.a₆*x*x₀*y + 48*W.a₁^2*W.a₆*x*x₀*y₀ + 18*W.a₁^2*x^5*y - 60*W.a₁^2*x^5*y₀ - 42*W.a₁^2*x^4*x₀*y + 156*W.a₁^2*x^4*x₀*y₀ + 36*W.a₁^2*x^3*x₀^2*y - 108*W.a₁^2*x^3*x₀^2*y₀ + 48*W.a₁^2*x^2*y*y₀^2 - 72*W.a₁^2*x^2*y₀^3 - 72*W.a₁^2*x*x₀*y*y₀^2 + 96*W.a₁^2*x*x₀*y₀^3 + 16*W.a₁*W.a₂^2*W.a₆*x^2 - 16*W.a₁*W.a₂^2*W.a₆*x*x₀ + 16*W.a₁*W.a₂^2*x^5 - 16*W.a₁*W.a₂^2*x^4*x₀ + 16*W.a₁*W.a₂^2*x^2*y₀^2 + 32*W.a₁*W.a₂^2*x*x₀*y*y₀ - 48*W.a₁*W.a₂^2*x*x₀*y₀^2 - 4*W.a₁*W.a₂*W.a₄^2*x^2 + 4*W.a₁*W.a₂*W.a₄^2*x*x₀ + 8*W.a₁*W.a₂*W.a₄*W.a₆*x - 8*W.a₁*W.a₂*W.a₄*W.a₆*x₀ + 32*W.a₁*W.a₂*W.a₄*x^4 - 32*W.a₁*W.a₂*W.a₄*x^3*x₀ + 16*W.a₁*W.a₂*W.a₄*x*y*y₀ - 8*W.a₁*W.a₂*W.a₄*x*y₀^2 + 16*W.a₁*W.a₂*W.a₄*x₀*y*y₀ - 24*W.a₁*W.a₂*W.a₄*x₀*y₀^2 + 72*W.a₁*W.a₂*W.a₆*x^3 - 72*W.a₁*W.a₂*W.a₆*x^2*x₀ - 16*W.a₁*W.a₂*W.a₆*y*y₀ + 16*W.a₁*W.a₂*W.a₆*y₀^2 + 36*W.a₁*W.a₂*x^6 - 36*W.a₁*W.a₂*x^5*x₀ - 64*W.a₁*W.a₂*x^3*y*y₀ + 136*W.a₁*W.a₂*x^3*y₀^2 + 144*W.a₁*W.a₂*x^2*x₀*y*y₀ - 216*W.a₁*W.a₂*x^2*x₀*y₀^2 - 16*W.a₁*W.a₂*y*y₀^3 + 16*W.a₁*W.a₂*y₀^4 - 2*W.a₁*W.a₄^3*x + 2*W.a₁*W.a₄^3*x₀ + 6*W.a₁*W.a₄^2*x^3 - 6*W.a₁*W.a₄^2*x^2*x₀ + 12*W.a₁*W.a₄^2*y*y₀ - 12*W.a₁*W.a₄^2*y₀^2 + 24*W.a₁*W.a₄*W.a₆*x^2 - 24*W.a₁*W.a₄*W.a₆*x*x₀ + 42*W.a₁*W.a₄*x^5 - 42*W.a₁*W.a₄*x^4*x₀ - 24*W.a₁*W.a₄*x^2*y*y₀ + 48*W.a₁*W.a₄*x^2*y₀^2 + 48*W.a₁*W.a₄*x*x₀*y*y₀ - 72*W.a₁*W.a₄*x*x₀*y₀^2 + 72*W.a₁*W.a₆*x^4 - 72*W.a₁*W.a₆*x^3*x₀ - 48*W.a₁*W.a₆*x*y*y₀ + 48*W.a₁*W.a₆*x*y₀^2 + 18*W.a₁*x^7 - 18*W.a₁*x^6*x₀ - 84*W.a₁*x^4*y*y₀ + 156*W.a₁*x^4*y₀^2 + 144*W.a₁*x^3*x₀*y*y₀ - 216*W.a₁*x^3*x₀*y₀^2 - 48*W.a₁*x*y*y₀^3 + 48*W.a₁*x*y₀^4 + 32*W.a₂^2*W.a₆*x*y - 32*W.a₂^2*W.a₆*x*y₀ + 32*W.a₂^2*x^4*y - 32*W.a₂^2*x^4*y₀ + 32*W.a₂^2*x*y*y₀^2 - 32*W.a₂^2*x*y₀^3 - 8*W.a₂*W.a₄^2*x*y + 8*W.a₂*W.a₄^2*x*y₀ + 16*W.a₂*W.a₄*W.a₆*y - 16*W.a₂*W.a₄*W.a₆*y₀ + 64*W.a₂*W.a₄*x^3*y - 64*W.a₂*W.a₄*x^3*y₀ + 16*W.a₂*W.a₄*y*y₀^2 - 16*W.a₂*W.a₄*y₀^3 + 144*W.a₂*W.a₆*x^2*y - 144*W.a₂*W.a₆*x^2*y₀ + 72*W.a₂*x^5*y - 72*W.a₂*x^5*y₀ + 144*W.a₂*x^2*y*y₀^2 - 144*W.a₂*x^2*y₀^3 - 4*W.a₄^3*y + 4*W.a₄^3*y₀ + 12*W.a₄^2*x^2*y - 12*W.a₄^2*x^2*y₀ + 48*W.a₄*W.a₆*x*y - 48*W.a₄*W.a₆*x*y₀ + 84*W.a₄*x^4*y - 84*W.a₄*x^4*y₀ + 48*W.a₄*x*y*y₀^2 - 48*W.a₄*x*y₀^3 + 144*W.a₆*x^3*y - 144*W.a₆*x^3*y₀ + 36*x^6*y - 36*x^6*y₀ + 144*x^3*y*y₀^2 - 144*x^3*y₀^3) * hQ
    + (-W.a₁^6*x^3*y^2 + 2*W.a₁^6*x^2*x₀*y^2 - W.a₁^6*x*x₀^2*y^2 + W.a₁^5*W.a₂*x^4*y - 3*W.a₁^5*W.a₂*x^2*x₀^2*y - W.a₁^5*W.a₂*x^2*x₀^2*y₀ + 2*W.a₁^5*W.a₂*x*x₀^3*y + 2*W.a₁^5*W.a₂*x*x₀^3*y₀ - W.a₁^5*W.a₂*x₀^4*y₀ - W.a₁^5*W.a₃*x^2*y^2 + 2*W.a₁^5*W.a₃*x*x₀*y^2 - W.a₁^5*W.a₃*x₀^2*y^2 + 3*W.a₁^5*W.a₄*x^3*y - 6*W.a₁^5*W.a₄*x^2*x₀*y - W.a₁^5*W.a₄*x^2*x₀*y₀ + 3*W.a₁^5*W.a₄*x*x₀^2*y + 2*W.a₁^5*W.a₄*x*x₀^2*y₀ - W.a₁^5*W.a₄*x₀^3*y₀ + W.a₁^5*W.a₆*x^2*y - W.a₁^5*W.a₆*x^2*y₀ - 2*W.a₁^5*W.a₆*x*x₀*y + 2*W.a₁^5*W.a₆*x*x₀*y₀ + W.a₁^5*W.a₆*x₀^2*y - W.a₁^5*W.a₆*x₀^2*y₀ - 3*W.a₁^5*x^5*y - W.a₁^5*x^5*y₀ + 9*W.a₁^5*x^4*x₀*y + 5*W.a₁^5*x^4*x₀*y₀ - 8*W.a₁^5*x^3*x₀^2*y - 10*W.a₁^5*x^3*x₀^2*y₀ + W.a₁^5*x^2*x₀^3*y + 9*W.a₁^5*x^2*x₀^3*y₀ - 3*W.a₁^5*x^2*y^3 + 5*W.a₁^5*x^2*y^2*y₀ - 2*W.a₁^5*x^2*y*y₀^2 + W.a₁^5*x*x₀^4*y - 3*W.a₁^5*x*x₀^4*y₀ + 4*W.a₁^5*x*x₀*y^3 - 4*W.a₁^5*x*x₀*y^2*y₀ + W.a₁^5*x*x₀*y*y₀^2 - W.a₁^5*x₀^2*y^3 - 2*W.a₁^4*W.a₂^2*x^4*x₀ + 4*W.a₁^4*W.a₂^2*x^3*x₀^2 - W.a₁^4*W.a₂^2*x^2*x₀^3 - 2*W.a₁^4*W.a₂^2*x*x₀^4 + W.a₁^4*W.a₂^2*x₀^5 - 2*W.a₁^4*W.a₂*W.a₃*x^3*y + 6*W.a₁^4*W.a₂*W.a₃*x^2*x₀*y - 6*W.a₁^4*W.a₂*W.a₃*x*x₀^2*y + 2*W.a₁^4*W.a₂*W.a₃*x₀^3*y - 2*W.a₁^4*W.a₂*W.a₄*x^4 + 2*W.a₁^4*W.a₂*W.a₄*x^3*x₀ + 4*W.a₁^4*W.a₂*W.a₄*x^2*x₀^2 - 6*W.a₁^4*W.a₂*W.a₄*x*x₀^3 + 2*W.a₁^4*W.a₂*W.a₄*x₀^4 + 4*W.a₁^4*W.a₂*x^6 - 12*W.a₁^4*W.a₂*x^5*x₀ + 8*W.a₁^4*W.a₂*x^4*x₀^2 + 7*W.a₁^4*W.a₂*x^3*x₀^3 - 6*W.a₁^4*W.a₂*x^3*y^2 - 3*W.a₁^4*W.a₂*x^3*y*y₀ + 2*W.a₁^4*W.a₂*x^3*y₀^2 - 9*W.a₁^4*W.a₂*x^2*x₀^4 + 14*W.a₁^4*W.a₂*x^2*x₀*y^2 - 4*W.a₁^4*W.a₂*x^2*x₀*y*y₀ - 4*W.a₁^4*W.a₂*x^2*x₀*y₀^2 + W.a₁^4*W.a₂*x*x₀^5 - 12*W.a₁^4*W.a₂*x*x₀^2*y^2 + 6*W.a₁^4*W.a₂*x*x₀^2*y*y₀ + 10*W.a₁^4*W.a₂*x*x₀^2*y₀^2 + W.a₁^4*W.a₂*x₀^6 + 2*W.a₁^4*W.a₂*x₀^3*y^2 + 2*W.a₁^4*W.a₂*x₀^3*y*y₀ - 7*W.a₁^4*W.a₂*x₀^3*y₀^2 + 2*W.a₁^4*W.a₃*W.a₄*x^2*y - 4*W.a₁^4*W.a₃*W.a₄*x*x₀*y + 2*W.a₁^4*W.a₃*W.a₄*x₀^2*y - 9*W.a₁^4*W.a₃*x^4*y + 20*W.a₁^4*W.a₃*x^3*x₀*y - 12*W.a₁^4*W.a₃*x^2*x₀^2*y - 2*W.a₁^4*W.a₃*x*y^3 + 6*W.a₁^4*W.a₃*x*y^2*y₀ - 3*W.a₁^4*W.a₃*x*y*y₀^2 + W.a₁^4*W.a₃*x₀^4*y + 2*W.a₁^4*W.a₃*x₀*y^3 - 4*W.a₁^4*W.a₃*x₀*y^2*y₀ + W.a₁^4*W.a₃*x₀*y*y₀^2 - 2*W.a₁^4*W.a₄^2*x^3 + 5*W.a₁^4*W.a₄^2*x^2*x₀ - 4*W.a₁^4*W.a₄^2*x*x₀^2 + W.a₁^4*W.a₄^2*x₀^3 + 3*W.a₁^4*W.a₄*x^5 - 12*W.a₁^4*W.a₄*x^4*x₀ + 17*W.a₁^4*W.a₄*x^3*x₀^2 - 9*W.a₁^4*W.a₄*x^2*x₀^3 + 5*W.a₁^4*W.a₄*x^2*y^2 - 10*W.a₁^4*W.a₄*x^2*y*y₀ + W.a₁^4*W.a₄*x^2*y₀^2 - 8*W.a₁^4*W.a₄*x*x₀*y^2 + 8*W.a₁^4*W.a₄*x*x₀*y*y₀ + 5*W.a₁^4*W.a₄*x*x₀*y₀^2 + W.a₁^4*W.a₄*x₀^5 + 2*W.a₁^4*W.a₄*x₀^2*y^2 + 2*W.a₁^4*W.a₄*x₀^2*y*y₀ - 5*W.a₁^4*W.a₄*x₀^2*y₀^2 + 2*W.a₁^4*W.a₆*x*y^2 - 6*W.a₁^4*W.a₆*x*y*y₀ + 4*W.a₁^4*W.a₆*x*y₀^2 - 2*W.a₁^4*W.a₆*x₀*y^2 + 6*W.a₁^4*W.a₆*x₀*y*y₀ - 4*W.a₁^4*W.a₆*x₀*y₀^2 + 3*W.a₁^4*x^7 - 9*W.a₁^4*x^6*x₀ + 9*W.a₁^4*x^5*x₀^2 - 6*W.a₁^4*x^4*x₀^3 - 27*W.a₁^4*x^4*y^2 + 13*W.a₁^4*x^4*y*y₀ + 7*W.a₁^4*x^4*y₀^2 + 9*W.a₁^4*x^3*x₀^4 + 51*W.a₁^4*x^3*x₀*y^2 - 24*W.a₁^4*x^3*x₀*y*y₀ - 31*W.a₁^4*x^3*x₀*y₀^2 - 9*W.a₁^4*x^2*x₀^5 - 27*W.a₁^4*x^2*x₀^2*y^2 + 6*W.a₁^4*x^2*x₀^2*y*y₀ + 45*W.a₁^4*x^2*x₀^2*y₀^2 + 3*W.a₁^4*x*x₀^6 - W.a₁^4*x*x₀^3*y^2 + 8*W.a₁^4*x*x₀^3*y*y₀ - 21*W.a₁^4*x*x₀^3*y₀^2 - 2*W.a₁^4*x*y^4 + 9*W.a₁^4*x*y^3*y₀ - 8*W.a₁^4*x*y^2*y₀^2 + 2*W.a₁^4*x*y*y₀^3 + W.a₁^4*x₀^4*y^2 + 2*W.a₁^4*x₀*y^4 - 4*W.a₁^4*x₀*y^3*y₀ + W.a₁^4*x₀*y^2*y₀^2 + 2*W.a₁^3*W.a₂^2*W.a₃*x^4 - 4*W.a₁^3*W.a₂^2*W.a₃*x^3*x₀ + W.a₁^3*W.a₂^2*W.a₃*x^2*x₀^2 + 2*W.a₁^3*W.a₂^2*W.a₃*x*x₀^3 - W.a₁^3*W.a₂^2*W.a₃*x₀^4 + 8*W.a₁^3*W.a₂^2*x^4*y - 2*W.a₁^3*W.a₂^2*x^4*y₀ - 2*W.a₁^3*W.a₂^2*x^3*x₀*y + 8*W.a₁^3*W.a₂^2*x^3*x₀*y₀ - 8*W.a₁^3*W.a₂^2*x^2*x₀^2*y - 10*W.a₁^3*W.a₂^2*x^2*x₀^2*y₀ + 6*W.a₁^3*W.a₂^2*x*x₀^3*y - 4*W.a₁^3*W.a₂^2*x*x₀^3*y₀ - 2*W.a₁^3*W.a₂^2*x₀^4*y + 6*W.a₁^3*W.a₂^2*x₀^4*y₀ - 2*W.a₁^3*W.a₂*W.a₃^2*x^2*y + 4*W.a₁^3*W.a₂*W.a₃^2*x*x₀*y - 2*W.a₁^3*W.a₂*W.a₃^2*x₀^2*y + 2*W.a₁^3*W.a₂*W.a₃*W.a₄*x^3 - 6*W.a₁^3*W.a₂*W.a₃*W.a₄*x^2*x₀ + 6*W.a₁^3*W.a₂*W.a₃*W.a₄*x*x₀^2 - 2*W.a₁^3*W.a₂*W.a₃*W.a₄*x₀^3 + 6*W.a₁^3*W.a₂*W.a₃*x^5 - 8*W.a₁^3*W.a₂*W.a₃*x^4*x₀ - 5*W.a₁^3*W.a₂*W.a₃*x^3*x₀^2 + 9*W.a₁^3*W.a₂*W.a₃*x^2*x₀^3 - 14*W.a₁^3*W.a₂*W.a₃*x^2*y^2 + 7*W.a₁^3*W.a₂*W.a₃*x^2*y*y₀ - W.a₁^3*W.a₂*W.a₃*x*x₀^4 + 20*W.a₁^3*W.a₂*W.a₃*x*x₀*y^2 - 12*W.a₁^3*W.a₂*W.a₃*x*x₀*y*y₀ + 2*W.a₁^3*W.a₂*W.a₃*x*x₀*y₀^2 - W.a₁^3*W.a₂*W.a₃*x₀^5 - 10*W.a₁^3*W.a₂*W.a₃*x₀^2*y^2 + 8*W.a₁^3*W.a₂*W.a₃*x₀^2*y*y₀ - W.a₁^3*W.a₂*W.a₃*x₀^2*y₀^2 + 17*W.a₁^3*W.a₂*W.a₄*x^3*y + 3*W.a₁^3*W.a₂*W.a₄*x^3*y₀ - 22*W.a₁^3*W.a₂*W.a₄*x^2*x₀*y + 12*W.a₁^3*W.a₂*W.a₄*x*x₀^2*y - 18*W.a₁^3*W.a₂*W.a₄*x*x₀^2*y₀ - 4*W.a₁^3*W.a₂*W.a₄*x₀^3*y + 12*W.a₁^3*W.a₂*W.a₄*x₀^3*y₀ + 8*W.a₁^3*W.a₂*W.a₆*x^2*y - 8*W.a₁^3*W.a₂*W.a₆*x^2*y₀ - 12*W.a₁^3*W.a₂*W.a₆*x*x₀*y + 12*W.a₁^3*W.a₂*W.a₆*x*x₀*y₀ + 4*W.a₁^3*W.a₂*W.a₆*x₀^2*y - 4*W.a₁^3*W.a₂*W.a₆*x₀^2*y₀ + 15*W.a₁^3*W.a₂*x^5*y - 29*W.a₁^3*W.a₂*x^5*y₀ + 6*W.a₁^3*W.a₂*x^4*x₀*y + 68*W.a₁^3*W.a₂*x^4*x₀*y₀ - 30*W.a₁^3*W.a₂*x^3*x₀^2*y - 40*W.a₁^3*W.a₂*x^3*x₀^2*y₀ + 14*W.a₁^3*W.a₂*x^2*x₀^3*y - 18*W.a₁^3*W.a₂*x^2*x₀^3*y₀ - 24*W.a₁^3*W.a₂*x^2*y^3 + 34*W.a₁^3*W.a₂*x^2*y^2*y₀ - 14*W.a₁^3*W.a₂*x^2*y*y₀^2 - 4*W.a₁^3*W.a₂*x^2*y₀^3 + 10*W.a₁^3*W.a₂*x*x₀^4*y₀ + 22*W.a₁^3*W.a₂*x*x₀*y^3 - 32*W.a₁^3*W.a₂*x*x₀*y^2*y₀ + 10*W.a₁^3*W.a₂*x*x₀*y*y₀^2 + 16*W.a₁^3*W.a₂*x*x₀*y₀^3 - 2*W.a₁^3*W.a₂*x₀^5*y + 6*W.a₁^3*W.a₂*x₀^5*y₀ - 8*W.a₁^3*W.a₂*x₀^2*y^3 + 8*W.a₁^3*W.a₂*x₀^2*y^2*y₀ + 10*W.a₁^3*W.a₂*x₀^2*y*y₀^2 - 18*W.a₁^3*W.a₂*x₀^2*y₀^3 - 5*W.a₁^3*W.a₃^2*x^3*y + 9*W.a₁^3*W.a₃^2*x^2*x₀*y - 3*W.a₁^3*W.a₃^2*x*x₀^2*y - W.a₁^3*W.a₃^2*x₀^3*y + W.a₁^3*W.a₃^2*y^2*y₀ - W.a₁^3*W.a₃^2*y*y₀^2 - W.a₁^3*W.a₃*W.a₄^2*x^2 + 2*W.a₁^3*W.a₃*W.a₄^2*x*x₀ - W.a₁^3*W.a₃*W.a₄^2*x₀^2 + 9*W.a₁^3*W.a₃*W.a₄*x^4 - 20*W.a₁^3*W.a₃*W.a₄*x^3*x₀ + 12*W.a₁^3*W.a₃*W.a₄*x^2*x₀^2 - 6*W.a₁^3*W.a₃*W.a₄*x*y*y₀ + 3*W.a₁^3*W.a₃*W.a₄*x*y₀^2 - W.a₁^3*W.a₃*W.a₄*x₀^4 - 2*W.a₁^3*W.a₃*W.a₄*x₀*y^2 + 6*W.a₁^3*W.a₃*W.a₄*x₀*y*y₀ - W.a₁^3*W.a₃*W.a₄*x₀*y₀^2 + 3*W.a₁^3*W.a₃*x^4*x₀^2 - 9*W.a₁^3*W.a₃*x^3*x₀^3 - 39*W.a₁^3*W.a₃*x^3*y^2 + 37*W.a₁^3*W.a₃*x^3*y*y₀ - 9*W.a₁^3*W.a₃*x^3*y₀^2 + 9*W.a₁^3*W.a₃*x^2*x₀^4 + 57*W.a₁^3*W.a₃*x^2*x₀*y^2 - 48*W.a₁^3*W.a₃*x^2*x₀*y*y₀ + 9*W.a₁^3*W.a₃*x^2*x₀*y₀^2 - 3*W.a₁^3*W.a₃*x*x₀^5 - 21*W.a₁^3*W.a₃*x*x₀^2*y^2 + 18*W.a₁^3*W.a₃*x*x₀^2*y*y₀ - 3*W.a₁^3*W.a₃*x*x₀^2*y₀^2 - 3*W.a₁^3*W.a₃*x₀^3*y^2 + 2*W.a₁^3*W.a₃*x₀^3*y*y₀ + 5*W.a₁^3*W.a₃*y^3*y₀ - 7*W.a₁^3*W.a₃*y^2*y₀^2 + 2*W.a₁^3*W.a₃*y*y₀^3 + 2*W.a₁^3*W.a₄^2*x^2*y + 6*W.a₁^3*W.a₄^2*x^2*y₀ + W.a₁^3*W.a₄^2*x*x₀*y - 14*W.a₁^3*W.a₄^2*x*x₀*y₀ - 2*W.a₁^3*W.a₄^2*x₀^2*y + 7*W.a₁^3*W.a₄^2*x₀^2*y₀ + 2*W.a₁^3*W.a₄*W.a₆*x*y - 2*W.a₁^3*W.a₄*W.a₆*x*y₀ - 2*W.a₁^3*W.a₄*W.a₆*x₀*y + 2*W.a₁^3*W.a₄*W.a₆*x₀*y₀ + 39*W.a₁^3*W.a₄*x^4*y - 23*W.a₁^3*W.a₄*x^4*y₀ - 66*W.a₁^3*W.a₄*x^3*x₀*y + 64*W.a₁^3*W.a₄*x^3*x₀*y₀ + 36*W.a₁^3*W.a₄*x^2*x₀^2*y - 66*W.a₁^3*W.a₄*x^2*x₀^2*y₀ - 4*W.a₁^3*W.a₄*x*x₀^3*y + 18*W.a₁^3*W.a₄*x*x₀^3*y₀ - 3*W.a₁^3*W.a₄*x*y^3 - 7*W.a₁^3*W.a₄*x*y^2*y₀ + 6*W.a₁^3*W.a₄*x*y*y₀^2 + 2*W.a₁^3*W.a₄*x*y₀^3 - 2*W.a₁^3*W.a₄*x₀^4*y + 4*W.a₁^3*W.a₄*x₀^4*y₀ - 2*W.a₁^3*W.a₄*x₀*y^3 + 6*W.a₁^3*W.a₄*x₀*y^2*y₀ + 6*W.a₁^3*W.a₄*x₀*y*y₀^2 - 8*W.a₁^3*W.a₄*x₀*y₀^3 + 18*W.a₁^3*W.a₆*x^3*y - 18*W.a₁^3*W.a₆*x^3*y₀ - 30*W.a₁^3*W.a₆*x^2*x₀*y + 30*W.a₁^3*W.a₆*x^2*x₀*y₀ + 12*W.a₁^3*W.a₆*x*x₀^2*y - 12*W.a₁^3*W.a₆*x*x₀^2*y₀ - 4*W.a₁^3*W.a₆*y^2*y₀ + 8*W.a₁^3*W.a₆*y*y₀^2 - 4*W.a₁^3*W.a₆*y₀^3 - 9*W.a₁^3*x^6*y - 27*W.a₁^3*x^6*y₀ + 27*W.a₁^3*x^5*x₀*y + 66*W.a₁^3*x^5*x₀*y₀ - 57*W.a₁^3*x^4*x₀^2*y₀ - 36*W.a₁^3*x^3*x₀^3*y + 36*W.a₁^3*x^3*x₀^3*y₀ - 61*W.a₁^3*x^3*y^3 + 117*W.a₁^3*x^3*y^2*y₀ - 52*W.a₁^3*x^3*y*y₀^2 - 22*W.a₁^3*x^3*y₀^3 + 24*W.a₁^3*x^2*x₀^4*y - 36*W.a₁^3*x^2*x₀^4*y₀ + 66*W.a₁^3*x^2*x₀*y^3 - 108*W.a₁^3*x^2*x₀*y^2*y₀ + 12*W.a₁^3*x^2*x₀*y*y₀^2 + 72*W.a₁^3*x^2*x₀*y₀^3 - 6*W.a₁^3*x*x₀^5*y + 18*W.a₁^3*x*x₀^5*y₀ - 18*W.a₁^3*x*x₀^2*y^3 + 18*W.a₁^3*x*x₀^2*y^2*y₀ + 30*W.a₁^3*x*x₀^2*y*y₀^2 - 54*W.a₁^3*x*x₀^2*y₀^3 - 2*W.a₁^3*x₀^3*y^3 + 2*W.a₁^3*x₀^3*y^2*y₀ + 4*W.a₁^3*y^4*y₀ - 6*W.a₁^3*y^3*y₀^2 + 2*W.a₁^3*y^2*y₀^3 - 12*W.a₁^2*W.a₂^3*x^4*x₀ + 16*W.a₁^2*W.a₂^3*x^3*x₀^2 - 4*W.a₁^2*W.a₂^3*x*x₀^4 + W.a₁^2*W.a₂^2*W.a₃^2*x^2*x₀ - 2*W.a₁^2*W.a₂^2*W.a₃^2*x*x₀^2 + W.a₁^2*W.a₂^2*W.a₃^2*x₀^3 - 4*W.a₁^2*W.a₂^2*W.a₃*x^3*y - 6*W.a₁^2*W.a₂^2*W.a₃*x^3*y₀ + 22*W.a₁^2*W.a₂^2*W.a₃*x^2*x₀*y + 4*W.a₁^2*W.a₂^2*W.a₃*x^2*x₀*y₀ - 22*W.a₁^2*W.a₂^2*W.a₃*x*x₀^2*y + 4*W.a₁^2*W.a₂^2*W.a₃*x*x₀^2*y₀ + 6*W.a₁^2*W.a₂^2*W.a₃*x₀^3*y - 4*W.a₁^2*W.a₂^2*W.a₃*x₀^3*y₀ - 10*W.a₁^2*W.a₂^2*W.a₄*x^4 - 2*W.a₁^2*W.a₂^2*W.a₄*x^3*x₀ + 24*W.a₁^2*W.a₂^2*W.a₄*x^2*x₀^2 - 10*W.a₁^2*W.a₂^2*W.a₄*x*x₀^3 - 2*W.a₁^2*W.a₂^2*W.a₄*x₀^4 + 18*W.a₁^2*W.a₂^2*x^6 - 66*W.a₁^2*W.a₂^2*x^5*x₀ + 40*W.a₁^2*W.a₂^2*x^4*x₀^2 + 30*W.a₁^2*W.a₂^2*x^3*x₀^3 - 28*W.a₁^2*W.a₂^2*x^3*y*y₀ + 20*W.a₁^2*W.a₂^2*x^3*y₀^2 - 18*W.a₁^2*W.a₂^2*x^2*x₀^4 + 28*W.a₁^2*W.a₂^2*x^2*x₀*y^2 + 8*W.a₁^2*W.a₂^2*x^2*x₀*y*y₀ - 28*W.a₁^2*W.a₂^2*x^2*x₀*y₀^2 - 4*W.a₁^2*W.a₂^2*x*x₀^5 - 24*W.a₁^2*W.a₂^2*x*x₀^2*y^2 + 4*W.a₁^2*W.a₂^2*x*x₀^2*y*y₀ + 12*W.a₁^2*W.a₂^2*x*x₀^2*y₀^2 + 4*W.a₁^2*W.a₂^2*x₀^3*y^2 - 8*W.a₁^2*W.a₂^2*x₀^3*y*y₀ + 12*W.a₁^2*W.a₂^2*x₀^3*y₀^2 + 2*W.a₁^2*W.a₂*W.a₃^2*W.a₄*x^2 - 4*W.a₁^2*W.a₂*W.a₃^2*W.a₄*x*x₀ + 2*W.a₁^2*W.a₂*W.a₃^2*W.a₄*x₀^2 - 4*W.a₁^2*W.a₂*W.a₃^2*x^4 + 11*W.a₁^2*W.a₂*W.a₃^2*x^3*x₀ - 9*W.a₁^2*W.a₂*W.a₃^2*x^2*x₀^2 + W.a₁^2*W.a₂*W.a₃^2*x*x₀^3 - 4*W.a₁^2*W.a₂*W.a₃^2*x*y^2 + 7*W.a₁^2*W.a₂*W.a₃^2*x*y*y₀ - 2*W.a₁^2*W.a₂*W.a₃^2*x*y₀^2 + W.a₁^2*W.a₂*W.a₃^2*x₀^4 + 2*W.a₁^2*W.a₂*W.a₃^2*x₀*y^2 - 4*W.a₁^2*W.a₂*W.a₃^2*x₀*y*y₀ + W.a₁^2*W.a₂*W.a₃^2*x₀*y₀^2 + 13*W.a₁^2*W.a₂*W.a₃*W.a₄*x^2*y - 7*W.a₁^2*W.a₂*W.a₃*W.a₄*x^2*y₀ - 12*W.a₁^2*W.a₂*W.a₃*W.a₄*x*x₀*y + 8*W.a₁^2*W.a₂*W.a₃*W.a₄*x*x₀*y₀ + 4*W.a₁^2*W.a₂*W.a₃*W.a₄*x₀^2*y - 6*W.a₁^2*W.a₂*W.a₃*W.a₄*x₀^2*y₀ - 45*W.a₁^2*W.a₂*W.a₃*x^4*y - 19*W.a₁^2*W.a₂*W.a₃*x^4*y₀ + 108*W.a₁^2*W.a₂*W.a₃*x^3*x₀*y + 16*W.a₁^2*W.a₂*W.a₃*x^3*x₀*y₀ - 72*W.a₁^2*W.a₂*W.a₃*x^2*x₀^2*y + 18*W.a₁^2*W.a₂*W.a₃*x^2*x₀^2*y₀ - 8*W.a₁^2*W.a₂*W.a₃*x*x₀^3*y₀ - 20*W.a₁^2*W.a₂*W.a₃*x*y^3 + 50*W.a₁^2*W.a₂*W.a₃*x*y^2*y₀ - 30*W.a₁^2*W.a₂*W.a₃*x*y*y₀^2 + 4*W.a₁^2*W.a₂*W.a₃*x*y₀^3 + 6*W.a₁^2*W.a₂*W.a₃*x₀^4*y - 4*W.a₁^2*W.a₂*W.a₃*x₀^4*y₀ + 10*W.a₁^2*W.a₂*W.a₃*x₀*y^3 - 28*W.a₁^2*W.a₂*W.a₃*x₀*y^2*y₀ + 18*W.a₁^2*W.a₂*W.a₃*x₀*y*y₀^2 - 4*W.a₁^2*W.a₂*W.a₃*x₀*y₀^3 - 13*W.a₁^2*W.a₂*W.a₄^2*x^3 + 16*W.a₁^2*W.a₂*W.a₄^2*x^2*x₀ + 2*W.a₁^2*W.a₂*W.a₄^2*x*x₀^2 - 5*W.a₁^2*W.a₂*W.a₄^2*x₀^3 - 48*W.a₁^2*W.a₂*W.a₄*x^4*x₀ + 62*W.a₁^2*W.a₂*W.a₄*x^3*x₀^2 + 34*W.a₁^2*W.a₂*W.a₄*x^2*y^2 - 46*W.a₁^2*W.a₂*W.a₄*x^2*y*y₀ + 14*W.a₁^2*W.a₂*W.a₄*x^2*y₀^2 - 12*W.a₁^2*W.a₂*W.a₄*x*x₀^4 - 14*W.a₁^2*W.a₂*W.a₄*x*x₀*y^2 + 20*W.a₁^2*W.a₂*W.a₄*x*x₀*y*y₀ - 18*W.a₁^2*W.a₂*W.a₄*x*x₀*y₀^2 - 2*W.a₁^2*W.a₂*W.a₄*x₀^5 - 16*W.a₁^2*W.a₂*W.a₄*x₀^2*y*y₀ + 26*W.a₁^2*W.a₂*W.a₄*x₀^2*y₀^2 + 16*W.a₁^2*W.a₂*W.a₆*x*y^2 - 40*W.a₁^2*W.a₂*W.a₆*x*y*y₀ + 24*W.a₁^2*W.a₂*W.a₆*x*y₀^2 - 8*W.a₁^2*W.a₂*W.a₆*x₀*y^2 + 24*W.a₁^2*W.a₂*W.a₆*x₀*y*y₀ - 16*W.a₁^2*W.a₂*W.a₆*x₀*y₀^2 + 45*W.a₁^2*W.a₂*x^7 - 108*W.a₁^2*W.a₂*x^6*x₀ + 36*W.a₁^2*W.a₂*x^5*x₀^2 + 45*W.a₁^2*W.a₂*x^4*x₀^3 - 66*W.a₁^2*W.a₂*x^4*y^2 - 82*W.a₁^2*W.a₂*x^4*y*y₀ + 110*W.a₁^2*W.a₂*x^4*y₀^2 + 138*W.a₁^2*W.a₂*x^3*x₀*y^2 + 56*W.a₁^2*W.a₂*x^3*x₀*y*y₀ - 166*W.a₁^2*W.a₂*x^3*x₀*y₀^2 - 18*W.a₁^2*W.a₂*x^2*x₀^5 - 72*W.a₁^2*W.a₂*x^2*x₀^2*y^2 + 12*W.a₁^2*W.a₂*x^2*x₀^2*y*y₀ + 54*W.a₁^2*W.a₂*x^2*x₀^2*y₀^2 - 8*W.a₁^2*W.a₂*x*x₀^3*y^2 - 12*W.a₁^2*W.a₂*x*x₀^3*y*y₀ + 28*W.a₁^2*W.a₂*x*x₀^3*y₀^2 - 16*W.a₁^2*W.a₂*x*y^4 + 52*W.a₁^2*W.a₂*x*y^3*y₀ - 52*W.a₁^2*W.a₂*x*y^2*y₀^2 + 12*W.a₁^2*W.a₂*x*y*y₀^3 + 8*W.a₁^2*W.a₂*x*y₀^4 + 4*W.a₁^2*W.a₂*x₀^4*y^2 - 8*W.a₁^2*W.a₂*x₀^4*y*y₀ + 12*W.a₁^2*W.a₂*x₀^4*y₀^2 + 8*W.a₁^2*W.a₂*x₀*y^4 - 24*W.a₁^2*W.a₂*x₀*y^3*y₀ + 16*W.a₁^2*W.a₂*x₀*y^2*y₀^2 + 16*W.a₁^2*W.a₂*x₀*y*y₀^3 - 20*W.a₁^2*W.a₂*x₀*y₀^4 + 5*W.a₁^2*W.a₃^2*W.a₄*x^3 - 9*W.a₁^2*W.a₃^2*W.a₄*x^2*x₀ + 3*W.a₁^2*W.a₃^2*W.a₄*x*x₀^2 + W.a₁^2*W.a₃^2*W.a₄*x₀^3 - W.a₁^2*W.a₃^2*W.a₄*y^2 + W.a₁^2*W.a₃^2*W.a₄*y₀^2 - 9*W.a₁^2*W.a₃^2*x^5 + 15*W.a₁^2*W.a₃^2*x^4*x₀ - 9*W.a₁^2*W.a₃^2*x^2*x₀^3 - 9*W.a₁^2*W.a₃^2*x^2*y^2 + 21*W.a₁^2*W.a₃^2*x^2*y*y₀ - 9*W.a₁^2*W.a₃^2*x^2*y₀^2 + 3*W.a₁^2*W.a₃^2*x*x₀^4 + 6*W.a₁^2*W.a₃^2*x*x₀*y^2 - 12*W.a₁^2*W.a₃^2*x*x₀*y*y₀ + 3*W.a₁^2*W.a₃^2*x*x₀*y₀^2 + 3*W.a₁^2*W.a₃*W.a₄^2*x*y - W.a₁^2*W.a₃*W.a₄^2*x₀*y - 2*W.a₁^2*W.a₃*W.a₄^2*x₀*y₀ + 21*W.a₁^2*W.a₃*W.a₄*x^3*y - 19*W.a₁^2*W.a₃*W.a₄*x^3*y₀ - 30*W.a₁^2*W.a₃*W.a₄*x^2*x₀*y + 30*W.a₁^2*W.a₃*W.a₄*x^2*x₀*y₀ + 12*W.a₁^2*W.a₃*W.a₄*x*x₀^2*y - 12*W.a₁^2*W.a₃*W.a₄*x*x₀^2*y₀ - 2*W.a₁^2*W.a₃*W.a₄*x₀^3*y₀ - 5*W.a₁^2*W.a₃*W.a₄*y^3 + 3*W.a₁^2*W.a₃*W.a₄*y^2*y₀ + 4*W.a₁^2*W.a₃*W.a₄*y*y₀^2 - 2*W.a₁^2*W.a₃*W.a₄*y₀^3 - 72*W.a₁^2*W.a₃*x^5*y - 9*W.a₁^2*W.a₃*x^5*y₀ + 117*W.a₁^2*W.a₃*x^4*x₀*y + 12*W.a₁^2*W.a₃*x^4*x₀*y₀ - 18*W.a₁^2*W.a₃*x^3*x₀^2*y - 54*W.a₁^2*W.a₃*x^2*x₀^3*y + 18*W.a₁^2*W.a₃*x^2*x₀^3*y₀ - 45*W.a₁^2*W.a₃*x^2*y^3 + 141*W.a₁^2*W.a₃*x^2*y^2*y₀ - 102*W.a₁^2*W.a₃*x^2*y*y₀^2 + 18*W.a₁^2*W.a₃*x^2*y₀^3 + 18*W.a₁^2*W.a₃*x*x₀^4*y - 12*W.a₁^2*W.a₃*x*x₀^4*y₀ + 30*W.a₁^2*W.a₃*x*x₀*y^3 - 84*W.a₁^2*W.a₃*x*x₀*y^2*y₀ + 54*W.a₁^2*W.a₃*x*x₀*y*y₀^2 - 12*W.a₁^2*W.a₃*x*x₀*y₀^3 - 4*W.a₁^2*W.a₄^3*x^2 + 7*W.a₁^2*W.a₄^3*x*x₀ - 3*W.a₁^2*W.a₄^3*x₀^2 - 9*W.a₁^2*W.a₄^2*x^4 + 6*W.a₁^2*W.a₄^2*x^3*x₀ + 6*W.a₁^2*W.a₄^2*x^2*x₀^2 + 11*W.a₁^2*W.a₄^2*x*y^2 - 5*W.a₁^2*W.a₄^2*x*y*y₀ - 6*W.a₁^2*W.a₄^2*x*y₀^2 - 3*W.a₁^2*W.a₄^2*x₀^4 - 3*W.a₁^2*W.a₄^2*x₀*y^2 - 10*W.a₁^2*W.a₄^2*x₀*y*y₀ + 13*W.a₁^2*W.a₄^2*x₀*y₀^2 + 4*W.a₁^2*W.a₄*W.a₆*y^2 - 8*W.a₁^2*W.a₄*W.a₆*y*y₀ + 4*W.a₁^2*W.a₄*W.a₆*y₀^2 + 18*W.a₁^2*W.a₄*x^6 - 63*W.a₁^2*W.a₄*x^5*x₀ + 51*W.a₁^2*W.a₄*x^4*x₀^2 + 42*W.a₁^2*W.a₄*x^3*y^2 - 112*W.a₁^2*W.a₄*x^3*y*y₀ + 78*W.a₁^2*W.a₄*x^3*y₀^2 - 30*W.a₁^2*W.a₄*x^2*x₀*y^2 + 108*W.a₁^2*W.a₄*x^2*x₀*y*y₀ - 120*W.a₁^2*W.a₄*x^2*x₀*y₀^2 - 6*W.a₁^2*W.a₄*x*x₀^5 + 6*W.a₁^2*W.a₄*x*x₀^2*y^2 - 36*W.a₁^2*W.a₄*x*x₀^2*y*y₀ + 66*W.a₁^2*W.a₄*x*x₀^2*y₀^2 - 2*W.a₁^2*W.a₄*x₀^3*y^2 - 4*W.a₁^2*W.a₄*x₀^3*y*y₀ + 4*W.a₁^2*W.a₄*x₀^3*y₀^2 - 4*W.a₁^2*W.a₄*y^4 + 2*W.a₁^2*W.a₄*y^3*y₀ + 2*W.a₁^2*W.a₄*y^2*y₀^2 + 4*W.a₁^2*W.a₄*y*y₀^3 - 4*W.a₁^2*W.a₄*y₀^4 + 36*W.a₁^2*W.a₆*x^2*y^2 - 96*W.a₁^2*W.a₆*x^2*y*y₀ + 60*W.a₁^2*W.a₆*x^2*y₀^2 - 24*W.a₁^2*W.a₆*x*x₀*y^2 + 72*W.a₁^2*W.a₆*x*x₀*y*y₀ - 48*W.a₁^2*W.a₆*x*x₀*y₀^2 + 27*W.a₁^2*x^8 - 54*W.a₁^2*x^7*x₀ + 18*W.a₁^2*x^6*x₀^2 - 117*W.a₁^2*x^5*y^2 - 27*W.a₁^2*x^5*y*y₀ + 96*W.a₁^2*x^5*y₀^2 + 27*W.a₁^2*x^4*x₀^4 + 153*W.a₁^2*x^4*x₀*y^2 + 42*W.a₁^2*x^4*x₀*y*y₀ - 165*W.a₁^2*x^4*x₀*y₀^2 - 18*W.a₁^2*x^3*x₀^5 - 18*W.a₁^2*x^3*x₀^2*y^2 - 36*W.a₁^2*x^3*x₀^2*y*y₀ + 90*W.a₁^2*x^3*x₀^2*y₀^2 - 54*W.a₁^2*x^2*x₀^3*y^2 + 48*W.a₁^2*x^2*x₀^3*y*y₀ - 36*W.a₁^2*x^2*x₀^3*y₀^2 - 36*W.a₁^2*x^2*y^4 + 150*W.a₁^2*x^2*y^3*y₀ - 162*W.a₁^2*x^2*y^2*y₀^2 + 24*W.a₁^2*x^2*y*y₀^3 + 36*W.a₁^2*x^2*y₀^4 + 12*W.a₁^2*x*x₀^4*y^2 - 24*W.a₁^2*x*x₀^4*y*y₀ + 36*W.a₁^2*x*x₀^4*y₀^2 + 24*W.a₁^2*x*x₀*y^4 - 72*W.a₁^2*x*x₀*y^3*y₀ + 48*W.a₁^2*x*x₀*y^2*y₀^2 + 48*W.a₁^2*x*x₀*y*y₀^3 - 60*W.a₁^2*x*x₀*y₀^4 + 8*W.a₁*W.a₂^3*W.a₃*x^4 - 12*W.a₁*W.a₂^3*W.a₃*x^3*x₀ + 4*W.a₁*W.a₂^3*W.a₃*x*x₀^3 + 16*W.a₁*W.a₂^3*x^4*y - 8*W.a₁*W.a₂^3*x^4*y₀ - 8*W.a₁*W.a₂^3*x^3*x₀*y + 16*W.a₁*W.a₂^3*x^3*x₀*y₀ - 8*W.a₁*W.a₂^3*x^2*x₀^2*y + 8*W.a₁*W.a₂^3*x*x₀^3*y - 16*W.a₁*W.a₂^3*x*x₀^3*y₀ - W.a₁*W.a₂^2*W.a₃^3*x^2 + 2*W.a₁*W.a₂^2*W.a₃^3*x*x₀ - W.a₁*W.a₂^2*W.a₃^3*x₀^2 - 8*W.a₁*W.a₂^2*W.a₃^2*x^2*y + 12*W.a₁*W.a₂^2*W.a₃^2*x*x₀*y - 6*W.a₁*W.a₂^2*W.a₃^2*x₀^2*y + 2*W.a₁*W.a₂^2*W.a₃^2*x₀^2*y₀ + 10*W.a₁*W.a₂^2*W.a₃*W.a₄*x^3 - 22*W.a₁*W.a₂^2*W.a₃*W.a₄*x^2*x₀ + 10*W.a₁*W.a₂^2*W.a₃*W.a₄*x*x₀^2 + 2*W.a₁*W.a₂^2*W.a₃*W.a₄*x₀^3 + 42*W.a₁*W.a₂^2*W.a₃*x^5 - 46*W.a₁*W.a₂^2*W.a₃*x^4*x₀ - 18*W.a₁*W.a₂^2*W.a₃*x^3*x₀^2 + 18*W.a₁*W.a₂^2*W.a₃*x^2*x₀^3 - 40*W.a₁*W.a₂^2*W.a₃*x^2*y^2 + 16*W.a₁*W.a₂^2*W.a₃*x^2*y*y₀ + 4*W.a₁*W.a₂^2*W.a₃*x^2*y₀^2 + 4*W.a₁*W.a₂^2*W.a₃*x*x₀^4 + 36*W.a₁*W.a₂^2*W.a₃*x*x₀*y^2 - 16*W.a₁*W.a₂^2*W.a₃*x*x₀*y*y₀ + 4*W.a₁*W.a₂^2*W.a₃*x*x₀*y₀^2 - 12*W.a₁*W.a₂^2*W.a₃*x₀^2*y^2 + 12*W.a₁*W.a₂^2*W.a₃*x₀^2*y*y₀ - 4*W.a₁*W.a₂^2*W.a₃*x₀^2*y₀^2 + 20*W.a₁*W.a₂^2*W.a₄*x^3*y - 28*W.a₁*W.a₂^2*W.a₄*x^2*x₀*y + 24*W.a₁*W.a₂^2*W.a₄*x^2*x₀*y₀ + 16*W.a₁*W.a₂^2*W.a₄*x*x₀^2*y - 28*W.a₁*W.a₂^2*W.a₄*x*x₀^2*y₀ + 4*W.a₁*W.a₂^2*W.a₄*x₀^3*y - 8*W.a₁*W.a₂^2*W.a₄*x₀^3*y₀ + 16*W.a₁*W.a₂^2*W.a₆*x^2*y - 16*W.a₁*W.a₂^2*W.a₆*x^2*y₀ - 16*W.a₁*W.a₂^2*W.a₆*x*x₀*y + 16*W.a₁*W.a₂^2*W.a₆*x*x₀*y₀ + 108*W.a₁*W.a₂^2*x^5*y - 88*W.a₁*W.a₂^2*x^5*y₀ - 36*W.a₁*W.a₂^2*x^4*x₀*y + 104*W.a₁*W.a₂^2*x^4*x₀*y₀ - 72*W.a₁*W.a₂^2*x^3*x₀^2*y + 36*W.a₁*W.a₂^2*x^3*x₀^2*y₀ + 28*W.a₁*W.a₂^2*x^2*x₀^3*y - 72*W.a₁*W.a₂^2*x^2*x₀^3*y₀ - 48*W.a₁*W.a₂^2*x^2*y^3 + 56*W.a₁*W.a₂^2*x^2*y^2*y₀ - 24*W.a₁*W.a₂^2*x^2*y₀^3 + 8*W.a₁*W.a₂^2*x*x₀^4*y - 16*W.a₁*W.a₂^2*x*x₀^4*y₀ + 24*W.a₁*W.a₂^2*x*x₀*y^3 - 16*W.a₁*W.a₂^2*x*x₀*y^2*y₀ - 24*W.a₁*W.a₂^2*x*x₀*y*y₀^2 + 32*W.a₁*W.a₂^2*x*x₀*y₀^3 - 8*W.a₁*W.a₂^2*x₀^2*y^3 + 8*W.a₁*W.a₂^2*x₀^2*y^2*y₀ - 8*W.a₁*W.a₂^2*x₀^2*y*y₀^2 + 8*W.a₁*W.a₂^2*x₀^2*y₀^3 - 5*W.a₁*W.a₂*W.a₃^3*x^3 + 9*W.a₁*W.a₂*W.a₃^3*x^2*x₀ - 3*W.a₁*W.a₂*W.a₃^3*x*x₀^2 - W.a₁*W.a₂*W.a₃^3*x₀^3 + W.a₁*W.a₂*W.a₃^3*y*y₀ - W.a₁*W.a₂*W.a₃^3*y₀^2 + W.a₁*W.a₂*W.a₃^2*W.a₄*x*y - 3*W.a₁*W.a₂*W.a₃^2*W.a₄*x*y₀ + 2*W.a₁*W.a₂*W.a₃^2*W.a₄*x₀*y₀ - 45*W.a₁*W.a₂*W.a₃^2*x^3*y + 7*W.a₁*W.a₂*W.a₃^2*x^3*y₀ + 54*W.a₁*W.a₂*W.a₃^2*x^2*x₀*y - 18*W.a₁*W.a₂*W.a₃^2*x*x₀^2*y + 6*W.a₁*W.a₂*W.a₃^2*x*x₀^2*y₀ - 6*W.a₁*W.a₂*W.a₃^2*x₀^3*y + 2*W.a₁*W.a₂*W.a₃^2*x₀^3*y₀ + 8*W.a₁*W.a₂*W.a₃^2*y^2*y₀ - 10*W.a₁*W.a₂*W.a₃^2*y*y₀^2 + 2*W.a₁*W.a₂*W.a₃^2*y₀^3 + W.a₁*W.a₂*W.a₃*W.a₄^2*x^2 - 6*W.a₁*W.a₂*W.a₃*W.a₄^2*x*x₀ + 5*W.a₁*W.a₂*W.a₃*W.a₄^2*x₀^2 + 48*W.a₁*W.a₂*W.a₃*W.a₄*x^4 - 80*W.a₁*W.a₂*W.a₃*W.a₄*x^3*x₀ + 18*W.a₁*W.a₂*W.a₃*W.a₄*x^2*x₀^2 + 12*W.a₁*W.a₂*W.a₃*W.a₄*x*x₀^3 - 6*W.a₁*W.a₂*W.a₃*W.a₄*x*y^2 - 12*W.a₁*W.a₂*W.a₃*W.a₄*x*y*y₀ + 10*W.a₁*W.a₂*W.a₃*W.a₄*x*y₀^2 + 2*W.a₁*W.a₂*W.a₃*W.a₄*x₀^4 + 6*W.a₁*W.a₂*W.a₃*W.a₄*x₀*y^2 + 4*W.a₁*W.a₂*W.a₃*W.a₄*x₀*y*y₀ - 2*W.a₁*W.a₂*W.a₃*W.a₄*x₀*y₀^2 + 63*W.a₁*W.a₂*W.a₃*x^6 - 54*W.a₁*W.a₂*W.a₃*x^5*x₀ - 27*W.a₁*W.a₂*W.a₃*x^4*x₀^2 - 210*W.a₁*W.a₂*W.a₃*x^3*y^2 + 120*W.a₁*W.a₂*W.a₃*x^3*y*y₀ - 2*W.a₁*W.a₂*W.a₃*x^3*y₀^2 + 18*W.a₁*W.a₂*W.a₃*x^2*x₀^4 + 162*W.a₁*W.a₂*W.a₃*x^2*x₀*y^2 - 72*W.a₁*W.a₂*W.a₃*x^2*x₀*y*y₀ + 18*W.a₁*W.a₂*W.a₃*x^2*x₀*y₀^2 - 36*W.a₁*W.a₂*W.a₃*x*x₀^2*y^2 + 36*W.a₁*W.a₂*W.a₃*x*x₀^2*y*y₀ - 12*W.a₁*W.a₂*W.a₃*x*x₀^2*y₀^2 - 12*W.a₁*W.a₂*W.a₃*x₀^3*y^2 + 12*W.a₁*W.a₂*W.a₃*x₀^3*y*y₀ - 4*W.a₁*W.a₂*W.a₃*x₀^3*y₀^2 + 24*W.a₁*W.a₂*W.a₃*y^3*y₀ - 40*W.a₁*W.a₂*W.a₃*y^2*y₀^2 + 20*W.a₁*W.a₂*W.a₃*y*y₀^3 - 4*W.a₁*W.a₂*W.a₃*y₀^4 - 4*W.a₁*W.a₂*W.a₄^2*x^2*y + 16*W.a₁*W.a₂*W.a₄^2*x^2*y₀ - 8*W.a₁*W.a₂*W.a₄^2*x*x₀*y₀ + 10*W.a₁*W.a₂*W.a₄^2*x₀^2*y - 14*W.a₁*W.a₂*W.a₄^2*x₀^2*y₀ + 8*W.a₁*W.a₂*W.a₄*W.a₆*x*y - 8*W.a₁*W.a₂*W.a₄*W.a₆*x*y₀ - 8*W.a₁*W.a₂*W.a₄*W.a₆*x₀*y + 8*W.a₁*W.a₂*W.a₄*W.a₆*x₀*y₀ + 144*W.a₁*W.a₂*W.a₄*x^4*y - 92*W.a₁*W.a₂*W.a₄*x^4*y₀ - 156*W.a₁*W.a₂*W.a₄*x^3*x₀*y + 172*W.a₁*W.a₂*W.a₄*x^3*x₀*y₀ + 24*W.a₁*W.a₂*W.a₄*x^2*x₀^2*y - 72*W.a₁*W.a₂*W.a₄*x^2*x₀^2*y₀ + 20*W.a₁*W.a₂*W.a₄*x*x₀^3*y - 36*W.a₁*W.a₂*W.a₄*x*x₀^3*y₀ - 12*W.a₁*W.a₂*W.a₄*x*y^3 + 8*W.a₁*W.a₂*W.a₄*x*y^2*y₀ + 8*W.a₁*W.a₂*W.a₄*x*y*y₀^2 - 12*W.a₁*W.a₂*W.a₄*x*y₀^3 + 4*W.a₁*W.a₂*W.a₄*x₀^4*y - 8*W.a₁*W.a₂*W.a₄*x₀^4*y₀ + 4*W.a₁*W.a₂*W.a₄*x₀*y^3 - 20*W.a₁*W.a₂*W.a₄*x₀*y*y₀^2 + 24*W.a₁*W.a₂*W.a₄*x₀*y₀^3 + 72*W.a₁*W.a₂*W.a₆*x^3*y - 72*W.a₁*W.a₂*W.a₆*x^3*y₀ - 72*W.a₁*W.a₂*W.a₆*x^2*x₀*y + 72*W.a₁*W.a₂*W.a₆*x^2*x₀*y₀ - 16*W.a₁*W.a₂*W.a₆*y^2*y₀ + 32*W.a₁*W.a₂*W.a₆*y*y₀^2 - 16*W.a₁*W.a₂*W.a₆*y₀^3 + 180*W.a₁*W.a₂*x^6*y - 180*W.a₁*W.a₂*x^6*y₀ - 36*W.a₁*W.a₂*x^5*x₀*y + 180*W.a₁*W.a₂*x^5*x₀*y₀ - 90*W.a₁*W.a₂*x^4*x₀^2*y + 54*W.a₁*W.a₂*x^4*x₀^2*y₀ - 36*W.a₁*W.a₂*x^3*x₀^3*y - 36*W.a₁*W.a₂*x^3*x₀^3*y₀ - 244*W.a₁*W.a₂*x^3*y^3 + 288*W.a₁*W.a₂*x^3*y^2*y₀ + 16*W.a₁*W.a₂*x^3*y*y₀^2 - 132*W.a₁*W.a₂*x^3*y₀^3 + 36*W.a₁*W.a₂*x^2*x₀^4*y - 72*W.a₁*W.a₂*x^2*x₀^4*y₀ + 108*W.a₁*W.a₂*x^2*x₀*y^3 - 72*W.a₁*W.a₂*x^2*x₀*y^2*y₀ - 108*W.a₁*W.a₂*x^2*x₀*y*y₀^2 + 144*W.a₁*W.a₂*x^2*x₀*y₀^3 - 24*W.a₁*W.a₂*x*x₀^2*y^3 + 24*W.a₁*W.a₂*x*x₀^2*y^2*y₀ - 24*W.a₁*W.a₂*x*x₀^2*y*y₀^2 + 24*W.a₁*W.a₂*x*x₀^2*y₀^3 - 8*W.a₁*W.a₂*x₀^3*y^3 + 8*W.a₁*W.a₂*x₀^3*y^2*y₀ - 8*W.a₁*W.a₂*x₀^3*y*y₀^2 + 8*W.a₁*W.a₂*x₀^3*y₀^3 + 16*W.a₁*W.a₂*y^4*y₀ - 32*W.a₁*W.a₂*y^3*y₀^2 + 16*W.a₁*W.a₂*y^2*y₀^3 + 8*W.a₁*W.a₂*y*y₀^4 - 8*W.a₁*W.a₂*y₀^5 - 6*W.a₁*W.a₃^3*x^4 + 9*W.a₁*W.a₃^3*x^3*x₀ - 3*W.a₁*W.a₃^3*x*x₀^3 + 3*W.a₁*W.a₃^3*x*y*y₀ - 3*W.a₁*W.a₃^3*x*y₀^2 + W.a₁*W.a₃^2*W.a₄^2*y - W.a₁*W.a₃^2*W.a₄^2*y₀ - 3*W.a₁*W.a₃^2*W.a₄*x^2*y - 3*W.a₁*W.a₃^2*W.a₄*x^2*y₀ + 6*W.a₁*W.a₃^2*W.a₄*x*x₀*y₀ - 54*W.a₁*W.a₃^2*x^4*y + 12*W.a₁*W.a₃^2*x^4*y₀ + 54*W.a₁*W.a₃^2*x^3*x₀*y - 18*W.a₁*W.a₃^2*x*x₀^3*y + 6*W.a₁*W.a₃^2*x*x₀^3*y₀ + 24*W.a₁*W.a₃^2*x*y^2*y₀ - 30*W.a₁*W.a₃^2*x*y*y₀^2 + 6*W.a₁*W.a₃^2*x*y₀^3 - W.a₁*W.a₃*W.a₄^3*x + W.a₁*W.a₃*W.a₄^3*x₀ + 9*W.a₁*W.a₃*W.a₄^2*x^3 - 18*W.a₁*W.a₃*W.a₄^2*x^2*x₀ + 6*W.a₁*W.a₃*W.a₄^2*x*x₀^2 + 3*W.a₁*W.a₃*W.a₄^2*x₀^3 + 4*W.a₁*W.a₃*W.a₄^2*y^2 - 7*W.a₁*W.a₃*W.a₄^2*y*y₀ + 3*W.a₁*W.a₃*W.a₄^2*y₀^2 + 45*W.a₁*W.a₃*W.a₄*x^5 - 69*W.a₁*W.a₃*W.a₄*x^4*x₀ + 18*W.a₁*W.a₃*W.a₄*x^3*x₀^2 - 42*W.a₁*W.a₃*W.a₄*x^2*y^2 + 6*W.a₁*W.a₃*W.a₄*x^2*y*y₀ + 12*W.a₁*W.a₃*W.a₄*x^2*y₀^2 + 6*W.a₁*W.a₃*W.a₄*x*x₀^4 + 18*W.a₁*W.a₃*W.a₄*x*x₀*y^2 + 12*W.a₁*W.a₃*W.a₄*x*x₀*y*y₀ - 6*W.a₁*W.a₃*W.a₄*x*x₀*y₀^2 + 27*W.a₁*W.a₃*x^7 - 18*W.a₁*W.a₃*x^6*x₀ - 27*W.a₁*W.a₃*x^4*x₀^3 - 234*W.a₁*W.a₃*x^4*y^2 + 153*W.a₁*W.a₃*x^4*y*y₀ - 15*W.a₁*W.a₃*x^4*y₀^2 + 18*W.a₁*W.a₃*x^3*x₀^4 + 162*W.a₁*W.a₃*x^3*x₀*y^2 - 72*W.a₁*W.a₃*x^3*x₀*y*y₀ + 18*W.a₁*W.a₃*x^3*x₀*y₀^2 - 36*W.a₁*W.a₃*x*x₀^3*y^2 + 36*W.a₁*W.a₃*x*x₀^3*y*y₀ - 12*W.a₁*W.a₃*x*x₀^3*y₀^2 + 72*W.a₁*W.a₃*x*y^3*y₀ - 120*W.a₁*W.a₃*x*y^2*y₀^2 + 60*W.a₁*W.a₃*x*y*y₀^3 - 12*W.a₁*W.a₃*x*y₀^4 - 5*W.a₁*W.a₄^3*x*y + 7*W.a₁*W.a₄^3*x*y₀ + 6*W.a₁*W.a₄^3*x₀*y - 8*W.a₁*W.a₄^3*x₀*y₀ + 27*W.a₁*W.a₄^2*x^3*y - 9*W.a₁*W.a₄^2*x^3*y₀ - 36*W.a₁*W.a₄^2*x^2*x₀*y + 30*W.a₁*W.a₄^2*x^2*x₀*y₀ + 12*W.a₁*W.a₄^2*x*x₀^2*y - 24*W.a₁*W.a₄^2*x*x₀^2*y₀ + 6*W.a₁*W.a₄^2*x₀^3*y - 6*W.a₁*W.a₄^2*x₀^3*y₀ + 4*W.a₁*W.a₄^2*y^3 - 4*W.a₁*W.a₄^2*y^2*y₀ - 6*W.a₁*W.a₄^2*y*y₀^2 + 6*W.a₁*W.a₄^2*y₀^3 + 24*W.a₁*W.a₄*W.a₆*x^2*y - 24*W.a₁*W.a₄*W.a₆*x^2*y₀ - 24*W.a₁*W.a₄*W.a₆*x*x₀*y + 24*W.a₁*W.a₄*W.a₆*x*x₀*y₀ + 153*W.a₁*W.a₄*x^5*y - 123*W.a₁*W.a₄*x^5*y₀ - 162*W.a₁*W.a₄*x^4*x₀*y + 192*W.a₁*W.a₄*x^4*x₀*y₀ + 36*W.a₁*W.a₄*x^3*x₀^2*y - 72*W.a₁*W.a₄*x^3*x₀^2*y₀ - 12*W.a₁*W.a₄*x^2*x₀^3*y - 60*W.a₁*W.a₄*x^2*y^3 + 48*W.a₁*W.a₄*x^2*y^2*y₀ + 60*W.a₁*W.a₄*x^2*y*y₀^2 - 72*W.a₁*W.a₄*x^2*y₀^3 + 12*W.a₁*W.a₄*x*x₀^4*y - 24*W.a₁*W.a₄*x*x₀^4*y₀ + 12*W.a₁*W.a₄*x*x₀*y^3 - 60*W.a₁*W.a₄*x*x₀*y*y₀^2 + 72*W.a₁*W.a₄*x*x₀*y₀^3 + 72*W.a₁*W.a₆*x^4*y - 72*W.a₁*W.a₆*x^4*y₀ - 72*W.a₁*W.a₆*x^3*x₀*y + 72*W.a₁*W.a₆*x^3*x₀*y₀ - 48*W.a₁*W.a₆*x*y^2*y₀ + 96*W.a₁*W.a₆*x*y*y₀^2 - 48*W.a₁*W.a₆*x*y₀^3 + 81*W.a₁*x^7*y - 99*W.a₁*x^7*y₀ + 90*W.a₁*x^6*x₀*y₀ - 90*W.a₁*x^4*x₀^3*y + 54*W.a₁*x^4*x₀^3*y₀ - 264*W.a₁*x^4*y^3 + 324*W.a₁*x^4*y^2*y₀ - 6*W.a₁*x^4*y*y₀^2 - 126*W.a₁*x^4*y₀^3 + 36*W.a₁*x^3*x₀^4*y - 72*W.a₁*x^3*x₀^4*y₀ + 108*W.a₁*x^3*x₀*y^3 - 72*W.a₁*x^3*x₀*y^2*y₀ - 108*W.a₁*x^3*x₀*y*y₀^2 + 144*W.a₁*x^3*x₀*y₀^3 - 24*W.a₁*x*x₀^3*y^3 + 24*W.a₁*x*x₀^3*y^2*y₀ - 24*W.a₁*x*x₀^3*y*y₀^2 + 24*W.a₁*x*x₀^3*y₀^3 + 48*W.a₁*x*y^4*y₀ - 96*W.a₁*x*y^3*y₀^2 + 48*W.a₁*x*y^2*y₀^3 + 24*W.a₁*x*y*y₀^4 - 24*W.a₁*x*y₀^5 - 16*W.a₂^4*x^4*x₀ + 16*W.a₂^4*x^3*x₀^2 + 4*W.a₂^3*W.a₃^2*x^2*x₀ - 4*W.a₂^3*W.a₃^2*x*x₀^2 + 16*W.a₂^3*W.a₃*x^3*y - 16*W.a₂^3*W.a₃*x^3*y₀ + 16*W.a₂^3*W.a₃*x^2*x₀*y - 24*W.a₂^3*W.a₃*x*x₀^2*y + 8*W.a₂^3*W.a₃*x*x₀^2*y₀ - 8*W.a₂^3*W.a₄*x^4 - 16*W.a₂^3*W.a₄*x^3*x₀ + 24*W.a₂^3*W.a₄*x^2*x₀^2 + 8*W.a₂^3*x^6 - 96*W.a₂^3*x^5*x₀ + 72*W.a₂^3*x^4*x₀^2 + 16*W.a₂^3*x^3*x₀^3 + 32*W.a₂^3*x^3*y^2 - 64*W.a₂^3*x^3*y*y₀ + 32*W.a₂^3*x^3*y₀^2 + 16*W.a₂^3*x^2*x₀*y^2 - 16*W.a₂^3*x*x₀^2*y^2 + 16*W.a₂^3*x*x₀^2*y*y₀ - 16*W.a₂^3*x*x₀^2*y₀^2 - 2*W.a₂^2*W.a₃^3*x*y + 2*W.a₂^2*W.a₃^3*x*y₀ + 2*W.a₂^2*W.a₃^2*W.a₄*x^2 - 2*W.a₂^2*W.a₃^2*W.a₄*x₀^2 - 2*W.a₂^2*W.a₃^2*x^4 + 24*W.a₂^2*W.a₃^2*x^3*x₀ - 18*W.a₂^2*W.a₃^2*x^2*x₀^2 - 4*W.a₂^2*W.a₃^2*x*x₀^3 - 16*W.a₂^2*W.a₃^2*x*y^2 + 20*W.a₂^2*W.a₃^2*x*y*y₀ - 4*W.a₂^2*W.a₃^2*x*y₀^2 + 32*W.a₂^2*W.a₃*W.a₄*x^2*y - 24*W.a₂^2*W.a₃*W.a₄*x^2*y₀ - 8*W.a₂^2*W.a₃*W.a₄*x*x₀*y + 8*W.a₂^2*W.a₃*W.a₄*x*x₀*y₀ - 12*W.a₂^2*W.a₃*W.a₄*x₀^2*y + 4*W.a₂^2*W.a₃*W.a₄*x₀^2*y₀ + 72*W.a₂^2*W.a₃*x^4*y - 80*W.a₂^2*W.a₃*x^4*y₀ + 96*W.a₂^2*W.a₃*x^3*x₀*y - 108*W.a₂^2*W.a₃*x^2*x₀^2*y + 36*W.a₂^2*W.a₃*x^2*x₀^2*y₀ - 24*W.a₂^2*W.a₃*x*x₀^3*y + 8*W.a₂^2*W.a₃*x*x₀^3*y₀ - 48*W.a₂^2*W.a₃*x*y^3 + 80*W.a₂^2*W.a₃*x*y^2*y₀ - 40*W.a₂^2*W.a₃*x*y*y₀^2 + 8*W.a₂^2*W.a₃*x*y₀^3 - 12*W.a₂^2*W.a₄^2*x^3 + 12*W.a₂^2*W.a₄^2*x*x₀^2 - 24*W.a₂^2*W.a₄*x^5 - 72*W.a₂^2*W.a₄*x^4*x₀ + 72*W.a₂^2*W.a₄*x^3*x₀^2 + 24*W.a₂^2*W.a₄*x^2*x₀^3 + 56*W.a₂^2*W.a₄*x^2*y^2 - 96*W.a₂^2*W.a₄*x^2*y*y₀ + 48*W.a₂^2*W.a₄*x^2*y₀^2 + 16*W.a₂^2*W.a₄*x*x₀*y*y₀ - 16*W.a₂^2*W.a₄*x*x₀*y₀^2 - 8*W.a₂^2*W.a₄*x₀^2*y^2 + 8*W.a₂^2*W.a₄*x₀^2*y*y₀ - 8*W.a₂^2*W.a₄*x₀^2*y₀^2 + 32*W.a₂^2*W.a₆*x*y^2 - 64*W.a₂^2*W.a₆*x*y*y₀ + 32*W.a₂^2*W.a₆*x*y₀^2 + 36*W.a₂^2*x^7 - 216*W.a₂^2*x^6*x₀ + 108*W.a₂^2*x^5*x₀^2 + 72*W.a₂^2*x^4*x₀^3 + 168*W.a₂^2*x^4*y^2 - 368*W.a₂^2*x^4*y*y₀ + 192*W.a₂^2*x^4*y₀^2 + 96*W.a₂^2*x^3*x₀*y^2 - 72*W.a₂^2*x^2*x₀^2*y^2 + 72*W.a₂^2*x^2*x₀^2*y*y₀ - 72*W.a₂^2*x^2*x₀^2*y₀^2 - 16*W.a₂^2*x*x₀^3*y^2 + 16*W.a₂^2*x*x₀^3*y*y₀ - 16*W.a₂^2*x*x₀^3*y₀^2 - 32*W.a₂^2*x*y^4 + 64*W.a₂^2*x*y^3*y₀ - 32*W.a₂^2*x*y^2*y₀^2 - 16*W.a₂^2*x*y*y₀^3 + 16*W.a₂^2*x*y₀^4 - W.a₂*W.a₃^3*W.a₄*y + W.a₂*W.a₃^3*W.a₄*y₀ - 9*W.a₂*W.a₃^3*x^2*y + 9*W.a₂*W.a₃^3*x^2*y₀ + W.a₂*W.a₃^2*W.a₄^2*x - W.a₂*W.a₃^2*W.a₄^2*x₀ + 8*W.a₂*W.a₃^2*W.a₄*x^3 - 6*W.a₂*W.a₃^2*W.a₄*x*x₀^2 - 2*W.a₂*W.a₃^2*W.a₄*x₀^3 - 8*W.a₂*W.a₃^2*W.a₄*y^2 + 10*W.a₂*W.a₃^2*W.a₄*y*y₀ - 2*W.a₂*W.a₃^2*W.a₄*y₀^2 - 9*W.a₂*W.a₃^2*x^5 + 45*W.a₂*W.a₃^2*x^4*x₀ - 18*W.a₂*W.a₃^2*x^3*x₀^2 - 18*W.a₂*W.a₃^2*x^2*x₀^3 - 72*W.a₂*W.a₃^2*x^2*y^2 + 90*W.a₂*W.a₃^2*x^2*y*y₀ - 18*W.a₂*W.a₃^2*x^2*y₀^2 + 14*W.a₂*W.a₃*W.a₄^2*x*y - 10*W.a₂*W.a₃*W.a₄^2*x*y₀ - 8*W.a₂*W.a₃*W.a₄^2*x₀*y + 4*W.a₂*W.a₃*W.a₄^2*x₀*y₀ + 120*W.a₂*W.a₃*W.a₄*x^3*y - 88*W.a₂*W.a₃*W.a₄*x^3*y₀ - 36*W.a₂*W.a₃*W.a₄*x^2*x₀*y + 36*W.a₂*W.a₃*W.a₄*x^2*x₀*y₀ - 36*W.a₂*W.a₃*W.a₄*x*x₀^2*y + 12*W.a₂*W.a₃*W.a₄*x*x₀^2*y₀ - 12*W.a₂*W.a₃*W.a₄*x₀^3*y + 4*W.a₂*W.a₃*W.a₄*x₀^3*y₀ - 24*W.a₂*W.a₃*W.a₄*y^3 + 40*W.a₂*W.a₃*W.a₄*y^2*y₀ - 20*W.a₂*W.a₃*W.a₄*y*y₀^2 + 4*W.a₂*W.a₃*W.a₄*y₀^3 + 90*W.a₂*W.a₃*x^5*y - 126*W.a₂*W.a₃*x^5*y₀ + 180*W.a₂*W.a₃*x^4*x₀*y - 108*W.a₂*W.a₃*x^3*x₀^2*y + 36*W.a₂*W.a₃*x^3*x₀^2*y₀ - 108*W.a₂*W.a₃*x^2*x₀^3*y + 36*W.a₂*W.a₃*x^2*x₀^3*y₀ - 216*W.a₂*W.a₃*x^2*y^3 + 360*W.a₂*W.a₃*x^2*y^2*y₀ - 180*W.a₂*W.a₃*x^2*y*y₀^2 + 36*W.a₂*W.a₃*x^2*y₀^3 - 6*W.a₂*W.a₄^3*x^2 + 4*W.a₂*W.a₄^3*x*x₀ + 2*W.a₂*W.a₄^3*x₀^2 - 30*W.a₂*W.a₄^2*x^4 + 18*W.a₂*W.a₄^2*x^2*x₀^2 + 12*W.a₂*W.a₄^2*x*x₀^3 + 20*W.a₂*W.a₄^2*x*y^2 - 28*W.a₂*W.a₄^2*x*y*y₀ + 12*W.a₂*W.a₄^2*x*y₀^2 - 4*W.a₂*W.a₄^2*x₀*y^2 + 8*W.a₂*W.a₄^2*x₀*y*y₀ - 8*W.a₂*W.a₄^2*x₀*y₀^2 + 16*W.a₂*W.a₄*W.a₆*y^2 - 32*W.a₂*W.a₄*W.a₆*y*y₀ + 16*W.a₂*W.a₄*W.a₆*y₀^2 - 18*W.a₂*W.a₄*x^6 - 108*W.a₂*W.a₄*x^5*x₀ + 54*W.a₂*W.a₄*x^4*x₀^2 + 72*W.a₂*W.a₄*x^3*x₀^3 + 240*W.a₂*W.a₄*x^3*y^2 - 448*W.a₂*W.a₄*x^3*y*y₀ + 240*W.a₂*W.a₄*x^3*y₀^2 + 72*W.a₂*W.a₄*x^2*x₀*y*y₀ - 72*W.a₂*W.a₄*x^2*x₀*y₀^2 - 24*W.a₂*W.a₄*x*x₀^2*y^2 + 24*W.a₂*W.a₄*x*x₀^2*y*y₀ - 24*W.a₂*W.a₄*x*x₀^2*y₀^2 - 8*W.a₂*W.a₄*x₀^3*y^2 + 8*W.a₂*W.a₄*x₀^3*y*y₀ - 8*W.a₂*W.a₄*x₀^3*y₀^2 - 16*W.a₂*W.a₄*y^4 + 32*W.a₂*W.a₄*y^3*y₀ - 16*W.a₂*W.a₄*y^2*y₀^2 - 8*W.a₂*W.a₄*y*y₀^3 + 8*W.a₂*W.a₄*y₀^4 + 144*W.a₂*W.a₆*x^2*y^2 - 288*W.a₂*W.a₆*x^2*y*y₀ + 144*W.a₂*W.a₆*x^2*y₀^2 + 54*W.a₂*x^8 - 216*W.a₂*x^7*x₀ + 54*W.a₂*x^6*x₀^2 + 108*W.a₂*x^5*x₀^3 + 252*W.a₂*x^5*y^2 - 612*W.a₂*x^5*y*y₀ + 324*W.a₂*x^5*y₀^2 + 180*W.a₂*x^4*x₀*y^2 - 72*W.a₂*x^3*x₀^2*y^2 + 72*W.a₂*x^3*x₀^2*y*y₀ - 72*W.a₂*x^3*x₀^2*y₀^2 - 72*W.a₂*x^2*x₀^3*y^2 + 72*W.a₂*x^2*x₀^3*y*y₀ - 72*W.a₂*x^2*x₀^3*y₀^2 - 144*W.a₂*x^2*y^4 + 288*W.a₂*x^2*y^3*y₀ - 144*W.a₂*x^2*y^2*y₀^2 - 72*W.a₂*x^2*y*y₀^3 + 72*W.a₂*x^2*y₀^4 - 3*W.a₃^3*W.a₄*x*y + 3*W.a₃^3*W.a₄*x*y₀ - 9*W.a₃^3*x^3*y + 9*W.a₃^3*x^3*y₀ + 3*W.a₃^2*W.a₄^2*x^2 - 3*W.a₃^2*W.a₄^2*x*x₀ + 6*W.a₃^2*W.a₄*x^4 - 6*W.a₃^2*W.a₄*x*x₀^3 - 24*W.a₃^2*W.a₄*x*y^2 + 30*W.a₃^2*W.a₄*x*y*y₀ - 6*W.a₃^2*W.a₄*x*y₀^2 - 9*W.a₃^2*x^6 + 27*W.a₃^2*x^5*x₀ - 18*W.a₃^2*x^3*x₀^3 - 72*W.a₃^2*x^3*y^2 + 90*W.a₃^2*x^3*y*y₀ - 18*W.a₃^2*x^3*y₀^2 + W.a₃*W.a₄^3*y - W.a₃*W.a₄^3*y₀ + 33*W.a₃*W.a₄^2*x^2*y - 21*W.a₃*W.a₄^2*x^2*y₀ - 24*W.a₃*W.a₄^2*x*x₀*y + 12*W.a₃*W.a₄^2*x*x₀*y₀ + 99*W.a₃*W.a₄*x^4*y - 75*W.a₃*W.a₄*x^4*y₀ - 36*W.a₃*W.a₄*x^3*x₀*y + 36*W.a₃*W.a₄*x^3*x₀*y₀ - 36*W.a₃*W.a₄*x*x₀^3*y + 12*W.a₃*W.a₄*x*x₀^3*y₀ - 72*W.a₃*W.a₄*x*y^3 + 120*W.a₃*W.a₄*x*y^2*y₀ - 60*W.a₃*W.a₄*x*y*y₀^2 + 12*W.a₃*W.a₄*x*y₀^3 + 27*W.a₃*x^6*y - 63*W.a₃*x^6*y₀ + 108*W.a₃*x^5*x₀*y - 108*W.a₃*x^3*x₀^3*y + 36*W.a₃*x^3*x₀^3*y₀ - 216*W.a₃*x^3*y^3 + 360*W.a₃*x^3*y^2*y₀ - 180*W.a₃*x^3*y*y₀^2 + 36*W.a₃*x^3*y₀^3 - W.a₄^4*x + W.a₄^4*x₀ - 8*W.a₄^3*x^3 + 6*W.a₄^3*x^2*x₀ + 2*W.a₄^3*x₀^3 + 2*W.a₄^3*y*y₀ - 2*W.a₄^3*y₀^2 - 18*W.a₄^2*x^5 + 18*W.a₄^2*x^2*x₀^3 + 60*W.a₄^2*x^2*y^2 - 102*W.a₄^2*x^2*y*y₀ + 54*W.a₄^2*x^2*y₀^2 - 12*W.a₄^2*x*x₀*y^2 + 24*W.a₄^2*x*x₀*y*y₀ - 24*W.a₄^2*x*x₀*y₀^2 + 48*W.a₄*W.a₆*x*y^2 - 96*W.a₄*W.a₆*x*y*y₀ + 48*W.a₄*W.a₆*x*y₀^2 - 54*W.a₄*x^6*x₀ + 54*W.a₄*x^4*x₀^3 + 216*W.a₄*x^4*y^2 - 426*W.a₄*x^4*y*y₀ + 234*W.a₄*x^4*y₀^2 + 72*W.a₄*x^3*x₀*y*y₀ - 72*W.a₄*x^3*x₀*y₀^2 - 24*W.a₄*x*x₀^3*y^2 + 24*W.a₄*x*x₀^3*y*y₀ - 24*W.a₄*x*x₀^3*y₀^2 - 48*W.a₄*x*y^4 + 96*W.a₄*x*y^3*y₀ - 48*W.a₄*x*y^2*y₀^2 - 24*W.a₄*x*y*y₀^3 + 24*W.a₄*x*y₀^4 + 144*W.a₆*x^3*y^2 - 288*W.a₆*x^3*y*y₀ + 144*W.a₆*x^3*y₀^2 + 27*x^9 - 81*x^8*x₀ + 54*x^6*x₀^3 + 108*x^6*y^2 - 306*x^6*y*y₀ + 162*x^6*y₀^2 + 108*x^5*x₀*y^2 - 72*x^3*x₀^3*y^2 + 72*x^3*x₀^3*y*y₀ - 72*x^3*x₀^3*y₀^2 - 144*x^3*y^4 + 288*x^3*y^3*y₀ - 144*x^3*y^2*y₀^2 - 72*x^3*y*y₀^3 + 72*x^3*y₀^4) * hord

/-! ### `veluGx_ne_zero_of_two_torsion` — `veluGx` does not vanish at a nonsingular 2-torsion point. -/

section

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem veluGx_ne_zero_of_two_torsion {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.veluGx x₀ y₀ ≠ 0  :=  by
  intro h
  exact hΔ (by rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h]; ring)

end

/-! ### `velu2QuadDisc_ne_zero_of_two_torsion` — … nor does the quadratic discriminant. -/

section

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem velu2QuadDisc_ne_zero_of_two_torsion {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.velu2QuadDisc x₀ ≠ 0  :=  by
  intro h
  exact hΔ (by rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h]; ring)

end

/-! ### `veluQuotient2_Delta_ne_zero` — The quotient discriminant is nonzero. -/

section

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {W : WeierstrassCurve R} {x₀ y₀ : R}
open Affine
theorem veluQuotient2_Delta_ne_zero (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ ≠ 0  :=  by
  rw [veluQuotient2_Delta_eq hQ hgy]
  exact mul_ne_zero (veluGx_ne_zero_of_two_torsion hΔ hQ hgy)
    (pow_ne_zero 2 (velu2QuadDisc_ne_zero_of_two_torsion hΔ hQ hgy))

end

/-! ### `isElliptic_veluQuotient2_of_isElliptic` — The order-two quotient of an elliptic curve is elliptic. -/

section

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
open Affine
theorem isElliptic_veluQuotient2_of_isElliptic
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).IsElliptic  :=   ⟨isUnit_iff_ne_zero.mpr (veluQuotient2_Delta_ne_zero W.isUnit_Δ.ne_zero hQ hgy)⟩

end

/-! ### `veluQuotient2_j` — The `j`-invariant of the order-two quotient. -/

section

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
open Affine
theorem veluQuotient2_j (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic :=
      isElliptic_veluQuotient2_of_isElliptic hQ hgy
    (W.veluQuotient2 x₀ y₀).j
      = (W.c₄ + 240 * W.veluGx x₀ y₀) ^ 3
        / (W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2)  :=  by
  haveI hE : (W.veluQuotient2 x₀ y₀).IsElliptic :=
    isElliptic_veluQuotient2_of_isElliptic hQ hgy
  have hΔ' : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := (W.veluQuotient2 x₀ y₀).isUnit_Δ.ne_zero
  rw [← veluQuotient2_Delta_eq hQ hgy, eq_div_iff hΔ', mul_comm, Δ_mul_j, veluQuotient2_cFour]

end

/-! ### `exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero` — The three 2-torsion quotients with nonzero discriminant, enumerated. -/

private theorem twoTorsionPair {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) {x₀ : K}
    (hx : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0) :
    W.toAffine.Equation x₀ (-(W.a₁ * x₀ + W.a₃) / 2) ∧
      W.veluGy x₀ (-(W.a₁ * x₀ + W.a₃) / 2) = 0 := by
  constructor
  · rw [Affine.equation_iff]
    simp only [b₂, b₄, b₆] at hx
    field_simp
    linear_combination -hx
  · simp only [veluGy]
    field_simp
    ring

theorem exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ P : ι → K × K, Function.Injective P ∧
        (∀ i, W.toAffine.Equation (P i).1 (P i).2) ∧ (∀ i, W.veluGy (P i).1 (P i).2 = 0) ∧
        ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := by
  classical

  set C3 : Cubic K := W.twoTorsionPolynomial with hC3
  have ha : C3.a ≠ 0 := by
    show (4 : K) ≠ 0
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hsplit : (Polynomial.map (RingHom.id K) C3.toPoly).Splits := IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc : C3.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) W.isUnit_Δ
  have hnodup : (Cubic.map (RingHom.id K) C3).roots.Nodup :=
    (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
  rw [h3] at hnodup
  have h12 : x₁ ≠ x₂ := by intro h; subst h; simp at hnodup
  have h13 : x₁ ≠ x₃ := by intro h; subst h; simp at hnodup
  have h23 : x₂ ≠ x₃ := by intro h; subst h; simp at hnodup
  have ha' : (Cubic.map (RingHom.id K) C3).a ≠ 0 := by simpa [Cubic.map] using ha
  have hroot : ∀ x ∈ ({x₁, x₂, x₃} : Multiset K),
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    intro x hx
    have hx' : x ∈ (Cubic.map (RingHom.id K) C3).roots := by rw [h3]; exact hx
    have := (Cubic.mem_roots_iff (Cubic.ne_zero_of_a_ne_zero ha') x).mp hx'
    simpa [Cubic.map, hC3, twoTorsionPolynomial] using this

  let yy : K → K := fun x => -(W.a₁ * x + W.a₃) / 2
  let P : Fin 3 → K × K := ![(x₁, yy x₁), (x₂, yy x₂), (x₃, yy x₃)]
  have hPfst : ∀ i, (P i).1 ∈ ({x₁, x₂, x₃} : Multiset K) := by
    intro i; fin_cases i <;> simp [P]
  have hPsnd : ∀ i, (P i).2 = yy (P i).1 := by
    intro i; fin_cases i <;> rfl
  have hPpair : ∀ i, W.toAffine.Equation (P i).1 (P i).2 ∧ W.veluGy (P i).1 (P i).2 = 0 := by
    intro i; rw [hPsnd]; exact twoTorsionPair h2 W (hroot _ (hPfst i))
  have hPinj : Function.Injective P := by
    intro i i' h
    have h1 := congrArg Prod.fst h
    fin_cases i <;> fin_cases i' <;> simp [P] at h1 ⊢ <;> simp_all
  have hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := fun i =>
    (@WeierstrassCurve.isUnit_Δ _ _ (W.veluQuotient2 (P i).1 (P i).2)
      (WeierstrassCurve.isElliptic_veluQuotient2_of_isElliptic (hPpair i).1 (hPpair i).2)).ne_zero
  exact ⟨Fin 3, inferInstance, Fintype.card_fin 3, P, hPinj, fun i => (hPpair i).1, fun i => (hPpair i).2, hΔ⟩

end WeierstrassCurve
