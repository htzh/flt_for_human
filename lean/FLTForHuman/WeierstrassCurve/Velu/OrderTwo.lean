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
  exact dite_eq_left hx

lemma veluPointMap2_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ (.some x y h)
      = .some _ _ (velu2_map_nonsingular hchar h.1 hQ hgy hx hΔ) := by
  simp only [veluPointMap2]
  exact dite_eq_right hx

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

/- The secant identity, factored through the chord intercept.  With `c = v₁ - m u₁`
the line `v = m u + c` meets the curve in the roots of
`u³ - (m²+a₁m-β)u² + (G - c(2m+a₁))u - c²`; writing `uR` for the third root, two Vieta
relations (`u₂uR + u₁u₂ + u₁uR = G - c(2m+a₁)` and `u₁u₂uR = c²`) turn the statement into
the product `(u₂ - uR) · [c(σ₂ - G) + (2m+a₁)u₁u₂uR]`, which vanishes by those two
relations.  No characteristic hypothesis and no case split. -/
/-- The secant statement, factored through the intercept `v₁ - m u₁` of the chord and the
`u`-coordinate `uR` of the third intersection, kept as a free variable.  The second point
is written on the chord: `v₂ = v₁ - m (u₁ - u₂)`. -/
private lemma secant_factor {F : Type*} [CommRing F] (a₁ G u₁ v₁ u₂ m uR : F) :
    u₂ * uR * (u₂ - uR) * v₁
      - u₁ * ((a₁ * u₂ + (v₁ - m * (u₁ - u₂))) * uR ^ 2
          - (a₁ * uR + (v₁ + m * (uR - u₁))) * u₂ ^ 2)
      + G * (uR * (v₁ - m * (u₁ - u₂)) - u₂ * (v₁ + m * (uR - u₁)))
    = (u₂ - uR) * ((v₁ - m * u₁) * (u₂ * uR + u₁ * u₂ + u₁ * uR - G)
        + (2 * m + a₁) * u₁ * u₂ * uR) := by
  ring

set_option maxHeartbeats 200000 in
private lemma velu_secant_core {F : Type*} [Field F] (a₁ β G u₁ v₁ u₂ v₂ m : F)
    (hd : u₁ - u₂ ≠ 0)
    (h1 : v₁ ^ 2 + a₁ * u₁ * v₁ = u₁ ^ 3 + β * u₁ ^ 2 + G * u₁)
    (h2 : v₂ ^ 2 + a₁ * u₂ * v₂ = u₂ ^ 3 + β * u₂ ^ 2 + G * u₂)
    (hsl : m * (u₁ - u₂) = v₁ - v₂) :
    let uR := m ^ 2 + a₁ * m - β - u₁ - u₂
    let vR := v₁ + m * (uR - u₁)
    u₂ * uR * (u₂ - uR) * v₁
      - u₁ * ((a₁ * u₂ + v₂) * uR ^ 2 - (a₁ * uR + vR) * u₂ ^ 2)
      + G * (uR * v₂ - u₂ * vR) = 0 := by
  dsimp only
  have hv₂ : v₂ = v₁ - m * (u₁ - u₂) := by linear_combination hsl
  rw [hv₂] at h2 ⊢
  set X : F := m ^ 2 + a₁ * m - β - u₁ - u₂ with hX
  rw [secant_factor a₁ G u₁ v₁ u₂ m X]
  have hσ : (u₂ * X + u₁ * u₂ + u₁ * X) - G + (v₁ - m * u₁) * (2 * m + a₁) = 0 := by
    have h : (u₁ - u₂) * ((u₂ * X + u₁ * u₂ + u₁ * X) - G
        + (v₁ - m * u₁) * (2 * m + a₁)) = 0 := by
      rw [hX]
      linear_combination h1 - h2
    exact (mul_eq_zero.mp h).resolve_left hd
  have he1 : (v₁ - m * u₁) ^ 2 + (v₁ - m * u₁) * u₁ * (2 * m + a₁)
      + u₁ ^ 2 * (m ^ 2 + a₁ * m - β) - u₁ ^ 3 - G * u₁ = 0 := by
    linear_combination h1
  have hp : u₁ * u₂ * X - (v₁ - m * u₁) ^ 2 = 0 := by
    have h : u₁ * u₂ * X - (v₁ - m * u₁) ^ 2
        = u₁ * ((u₂ * X + u₁ * u₂ + u₁ * X) - G + (v₁ - m * u₁) * (2 * m + a₁))
          - ((v₁ - m * u₁) ^ 2 + (v₁ - m * u₁) * u₁ * (2 * m + a₁)
              + u₁ ^ 2 * (m ^ 2 + a₁ * m - β) - u₁ ^ 3 - G * u₁) := by
      rw [hX]; ring
    rw [h, hσ, he1, mul_zero, sub_zero]
  have hb : (v₁ - m * u₁) * (u₂ * X + u₁ * u₂ + u₁ * X - G)
      + (2 * m + a₁) * u₁ * u₂ * X = 0 := by
    have h : (v₁ - m * u₁) * (u₂ * X + u₁ * u₂ + u₁ * X - G)
        + (2 * m + a₁) * u₁ * u₂ * X
        = (v₁ - m * u₁) * ((u₂ * X + u₁ * u₂ + u₁ * X) - G
              + (v₁ - m * u₁) * (2 * m + a₁))
          + (2 * m + a₁) * (u₁ * u₂ * X - (v₁ - m * u₁) ^ 2) := by ring
    rw [h, hσ, hp, mul_zero, mul_zero, add_zero]
  rw [hb, mul_zero]

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
  have hd : (x₁ - x₀) - (x₂ - x₀) ≠ 0 := by
    intro h; apply hx12; linear_combination h
  rw [Affine.equation_iff] at hP₁ hP₂ hQ
  have hmul : W.toAffine.slope x₁ x₂ y₁ y₂ * ((x₁ - x₀) - (x₂ - x₀))
      = (y₁ - y₀) - (y₂ - y₀) := by
    rw [Affine.slope_of_X_ne hx12]
    rw [show (x₁ - x₀) - (x₂ - x₀) = x₁ - x₂ by ring]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hx12)]
    ring
  have h1 : (y₁ - y₀) ^ 2 + W.a₁ * (x₁ - x₀) * (y₁ - y₀) =
      (x₁ - x₀) ^ 3 + (W.a₂ + 3 * x₀) * (x₁ - x₀) ^ 2 + W.veluGx x₀ y₀ * (x₁ - x₀) := by
    rw [veluGx]; linear_combination hP₁ - hQ - (y₁ - y₀) * hord
  have h2 : (y₂ - y₀) ^ 2 + W.a₁ * (x₂ - x₀) * (y₂ - y₀) =
      (x₂ - x₀) ^ 3 + (W.a₂ + 3 * x₀) * (x₂ - x₀) ^ 2 + W.veluGx x₀ y₀ * (x₂ - x₀) := by
    rw [veluGx]; linear_combination hP₂ - hQ - (y₂ - y₀) * hord
  have hcore := velu_secant_core W.a₁ (W.a₂ + 3 * x₀) (W.veluGx x₀ y₀)
    (x₁ - x₀) (y₁ - y₀) (x₂ - x₀) (y₂ - y₀) (W.toAffine.slope x₁ x₂ y₁ y₂) hd h1 h2 hmul
  simp only [Affine.addX, Affine.negAddY]
  linear_combination hcore

/-! ### `velu2_tangent_negAddY_cleared_identity` — The tangent `negAddY` cleared identity. -/

/- The shifted tangent identity, refactored: two small certificates instead of the
263 MB one.  `T` is linear in `v`; `Fx = 2*E + a₁*D` and `g2 = mP*D - E`.
Branch `Fx = 0`: `2^5*T = P1*Fx + 2*Q*(2*mP+a₁)`.  Branch `Fx ≠ 0`: divide
`T*(2*mP+a₁) = -(u-u_R)*((2*mP+a₁)²*curve + S*g2) + B*g2`. -/
set_option maxHeartbeats 200000 in
private lemma velu_tangent_core {F : Type*} [Field F] {a₁ β G u v mP : F}
    (hD : 2 * v + a₁ * u ≠ 0)
    (hmP : mP * (2 * v + a₁ * u) = 3 * u ^ 2 + 2 * β * u + G - a₁ * v)
    (h1 : v ^ 2 + a₁ * u * v = u ^ 3 + β * u ^ 2 + G * u) :
    -(2 * u * v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) ^ 2) - u * (v + (mP) * (((mP) ^ 2 + a₁ * (mP) - β - 2 * u) - u)) * G - u ^ 2 * a₁ * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) ^ 2 + u ^ 2 * v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) + u ^ 3 * a₁ * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) + u ^ 3 * (v + (mP) * (((mP) ^ 2 + a₁ * (mP) - β - 2 * u) - u)) + v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) * G = 0 := by
  have hcurve : v ^ 2 + a₁ * u * v - (u ^ 3 + β * u ^ 2 + G * u) = 0 := by
    linear_combination h1
  have hg2 : mP * (2 * v + a₁ * u) - (3 * u ^ 2 + 2 * β * u + G - a₁ * v) = 0 := by
    linear_combination hmP
  have hDF : (2 * mP + a₁) * (2 * v + a₁ * u) =
      2 * (3 * u ^ 2 + 2 * β * u + G - a₁ * v) + a₁ * (2 * v + a₁ * u) := by
    linear_combination 2 * hg2
  by_cases hF0 : 2 * (3 * u ^ 2 + 2 * β * u + G - a₁ * v) + a₁ * (2 * v + a₁ * u) = 0
  · have h2mp : 2 * mP + a₁ = 0 := by
      have h := hDF
      rw [hF0] at h
      exact (mul_eq_zero.mp h).resolve_right hD
    have hT5 : (2 : F) ^ 5 * (-(2 * u * v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) ^ 2) - u * (v + (mP) * (((mP) ^ 2 + a₁ * (mP) - β - 2 * u) - u)) * G - u ^ 2 * a₁ * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) ^ 2 + u ^ 2 * v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) + u ^ 3 * a₁ * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) + u ^ 3 * (v + (mP) * (((mP) ^ 2 + a₁ * (mP) - β - 2 * u) - u)) + v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) * G) = 0 := by
      linear_combination
        (-2*a₁^3*u - 4*a₁^2*v - 8*a₁*β*u - 24*a₁*u^2 - 16*β*v - 48*u*v) * hF0
        + (2 * (2*G*a₁^2*u - 4*G*a₁*mP*u + 4*G*a₁*v + 8*G*β*u - 8*G*mP^2*u + 8*G*mP*v + 24*G*u^2 + a₁^4*u^2 - 2*a₁^3*mP*u^2 + 2*a₁^3*u*v + 8*a₁^2*β*u^2 - 12*a₁^2*mP^2*u^2 - 4*a₁^2*mP*u*v + 18*a₁^2*u^3 + 16*a₁*β*mP*u^2 + 16*a₁*β*u*v - 8*a₁*mP^3*u^2 - 24*a₁*mP^2*u*v + 44*a₁*mP*u^3 + 36*a₁*u^2*v + 32*β*mP*u*v - 8*β*u^3 - 16*mP^3*u*v + 8*mP^2*u^3 + 72*mP*u^2*v - 24*u^4)) * h2mp
    by_cases h2 : (2 : F) = 0
    · exfalso
      have hFxa : 2 * (3 * u ^ 2 + 2 * β * u + G - a₁ * v) + a₁ * (2 * v + a₁ * u)
          = a₁ * (2 * v + a₁ * u) := by
        linear_combination (3 * u ^ 2 + 2 * β * u + G - a₁ * v) * h2
      have ha1 : a₁ = 0 := by
        have h := hF0
        rw [hFxa] at h
        exact (mul_eq_zero.mp h).resolve_right hD
      exact hD (by linear_combination v * h2 + u * ha1)
    · exact (mul_eq_zero.mp hT5).resolve_left (pow_ne_zero 5 h2)
  · have h2mp : 2 * mP + a₁ ≠ 0 := by
      intro h
      apply hF0
      rw [← hDF, h, zero_mul]
    have hkey : (-(2 * u * v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) ^ 2) - u * (v + (mP) * (((mP) ^ 2 + a₁ * (mP) - β - 2 * u) - u)) * G - u ^ 2 * a₁ * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) ^ 2 + u ^ 2 * v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) + u ^ 3 * a₁ * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) + u ^ 3 * (v + (mP) * (((mP) ^ 2 + a₁ * (mP) - β - 2 * u) - u)) + v * ((mP) ^ 2 + a₁ * (mP) - β - 2 * u) * G) * (2 * mP + a₁) = 0 := by
      linear_combination
        (-(u - (mP ^ 2 + a₁ * mP - β - 2 * u)) * (2 * mP + a₁) ^ 2) * hcurve
        + ((G*a₁*mP - G*β + G*mP^2 - 3*G*u - 2*a₁^2*mP^2*u + 4*a₁*β*mP*u - 4*a₁*mP^3*u + 9*a₁*mP*u^2 - 2*β^2*u + 4*β*mP^2*u - 9*β*u^2 - 2*mP^4*u + 9*mP^2*u^2 - 9*u^3) - (u - (mP ^ 2 + a₁ * mP - β - 2 * u)) * (-G - a₁^2*u - a₁*mP*u - a₁*v - 2*β*u - 2*mP*v - 3*u^2)) * hg2
    exact (mul_eq_zero.mp hkey).resolve_right h2mp

set_option maxHeartbeats 200000 in
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
  have hne : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h
    apply hy
    rw [Affine.negY]
    linear_combination h
  have hDuv : 2 * (y - y₀) + W.a₁ * (x - x₀) = 2 * y + W.a₁ * x + W.a₃ := by
    linear_combination -hord
  have hD : 2 * (y - y₀) + W.a₁ * (x - x₀) ≠ 0 := by rw [hDuv]; exact hne
  rw [Affine.equation_iff] at hP hQ
  have h1 : (y - y₀) ^ 2 + W.a₁ * (x - x₀) * (y - y₀) =
      (x - x₀) ^ 3 + (W.a₂ + 3 * x₀) * (x - x₀) ^ 2 + W.veluGx x₀ y₀ * (x - x₀) := by
    rw [veluGx]
    linear_combination hP - hQ - (y - y₀) * hord
  have hmP : W.toAffine.slope x x y y * (2 * (y - y₀) + W.a₁ * (x - x₀)) =
      3 * (x - x₀) ^ 2 + 2 * (W.a₂ + 3 * x₀) * (x - x₀) + W.veluGx x₀ y₀
        - W.a₁ * (y - y₀) := by
    rw [Affine.slope_of_Y_ne rfl hy]
    have hden : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
      rw [Affine.negY]; ring
    rw [hden, hDuv, div_mul_cancel₀ _ hne, veluGx]
    ring
  have hcore := velu_tangent_core (a₁ := W.a₁) (β := W.a₂ + 3 * x₀)
    (G := W.veluGx x₀ y₀) (u := x - x₀) (v := y - y₀) (mP := W.toAffine.slope x x y y)
    hD hmP h1
  simp only [Affine.addX, Affine.negAddY]
  linear_combination hcore

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
  have hE : (W.veluQuotient2 x₀ y₀).IsElliptic :=
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
