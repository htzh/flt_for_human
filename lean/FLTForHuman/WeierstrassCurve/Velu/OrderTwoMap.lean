/-
The order-two Vélu point map: `veluPointMap2` is an additive homomorphism.

This module carries the headline
`WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2` (V1-SET-1's wire
test), whose statement is transcribed verbatim from the pinned FLT `aa2d8b3`
wrapper

* `Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.lean`

and whose proof body is transcribed from

* `P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.lean`

(the pin's `solution`), adapted to mathlib `v4.34.0` and to the port's
`Velu/OrderTwo.lean`. Every intermediate `kw_*` declaration of that `S_` file —
the kernel/fibre algebra, the secant and tangent alignment identities, the
carrier predicates and the reduction to `AddMonoidHom.mk'` — is proof-local here
and declared `private`, so the checker diffs only the public headline; that is
the `OrderTwoMap.lean` deliverable's public surface, as the work order
prescribes.

The pin drives this file through the P2M tooling (`p2m_open`/`p2m_export`, which
re-export each piece's names into the `S_` namespace) and bumps `maxHeartbeats`
per piece. The port instead drops those commands, opens `Polynomial`,
`WeierstrassCurve` and `WeierstrassCurve.Affine` at file scope, keeps the pin's
per-piece `namespace WeierstrassCurve` blocks (so the `private` helper paths are
exactly `WeierstrassCurve.…`, matching their reference sites), drops every
`maxHeartbeats` bump (the global cap 4,000,000 is frozen) and keeps the pin's
`maxRecDepth` bumps. Only proof bodies are adapted; no statement moves.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.lean>

  spec-pin: Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.lean
-/
import FLTForHuman.WeierstrassCurve.Velu.OrderTwo
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine


set_option Elab.async false

section PieceKernelExact

open Polynomial

namespace WeierstrassCurve

section NegYFixedPoint

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R}

private lemma negY_eq_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    W.toAffine.negY x₀ y₀ = y₀ := by
  simp only [veluGy] at hgy
  simp only [Affine.negY]
  linear_combination hgy

private lemma veluGy_eq_zero_iff_negY_eq :
    W.veluGy x₀ y₀ = 0 ↔ W.toAffine.negY x₀ y₀ = y₀ :=
  ⟨negY_eq_of_veluGy_eq_zero, fun h => W.veluGy_eq_zero_of_negY_eq h⟩

end NegYFixedPoint

section FibreSingleton

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ : F}

private lemma eq_of_equation_of_veluGy_eq_zero (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) {y : F} (h : W.toAffine.Equation x₀ y) : y = y₀ := by
  rcases Affine.Y_eq_of_X_eq h hQ rfl with hy | hy
  · exact hy
  · rw [hy, negY_eq_of_veluGy_eq_zero hgy]

end FibreSingleton

end WeierstrassCurve

namespace WeierstrassCurve
namespace Affine

section PointFibre

variable {F : Type*} [Field F] {W : Affine F} {x₀ y₀ : F}


private theorem Point.some_eq_of_X_eq_of_veluGy_eq_zero (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hns : W.toAffine.Nonsingular x₀ y₀)
    {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    Point.some x y h = Point.some x₀ y₀ hns := by
  have hy : y = y₀ := eq_of_equation_of_veluGy_eq_zero hQ hgy (hx ▸ h.left)
  subst hx
  subst hy
  rfl

end PointFibre

section TwoTorsionOrder

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x₀ y₀ : F}

private theorem two_nsmul_some_eq_zero_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0)
    (hns : W.toAffine.Nonsingular x₀ y₀) :
    2 • (Point.some x₀ y₀ hns : W.toAffine.Point) = 0 := by
  rw [two_nsmul]
  exact Point.add_of_Y_eq rfl (negY_eq_of_veluGy_eq_zero hgy).symm

end TwoTorsionOrder

end WeierstrassCurve.Affine

end PieceKernelExact

section Piece_VeluOrderTwoNeg
set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

private theorem veluOrderTwoNeg_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ : F}

private theorem velu2Y_negY (hgy : W.veluGy x₀ y₀ = 0) (x y : F) :
    W.velu2Y x₀ y₀ x (W.toAffine.negY x y)
      = (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have _ := veluOrderTwoNeg_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  by_cases hx : x = x₀
  ·
    subst hx
    simp only [velu2Y, velu2X, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, sub_zero, add_zero, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
  ·
    have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
    simp only [velu2Y, velu2X, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
    field_simp
    linear_combination W.veluGx x₀ y₀ * hord

variable [DecidableEq F]
variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

omit [DecidableEq F] in

private lemma v2neg_some_congr {W' : Affine F} {x y₁ y₂ : F}
    {h₁ : W'.Nonsingular x y₁} {h₂ : W'.Nonsingular x y₂} (hy : y₁ = y₂) :
    Affine.Point.some x y₁ h₁ = Affine.Point.some x y₂ h₂ := by
  have _ := veluOrderTwoNeg_axiomAnchor
  subst hy; rfl

include hchar hQ hgy hΔ in

private theorem veluPointMap2_neg (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (-P) = -veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := veluOrderTwoNeg_axiomAnchor
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x = x₀
    · rw [veluPointMap2_some_of_eq hchar hQ hgy hΔ _ hx,
        veluPointMap2_some_of_eq hchar hQ hgy hΔ h hx]
      rfl
    · rw [veluPointMap2_some_of_ne hchar hQ hgy hΔ _ hx,
        veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx, Affine.Point.neg_some]
      exact v2neg_some_congr (velu2Y_negY hgy x y)

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoNeg

section Piece_VeluOrderTwoAddKernel
set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

private theorem veluOrderTwoAddKernel_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

private theorem veluGx_ne_zero_of_quotΔ (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.veluGx x₀ y₀ ≠ 0 := fun h =>
  hΔ (by rw [veluQuotient2_Delta_eq hQ hgy, h]; ring)

private theorem velu2_addX_kernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀)
      = x₀ + W.veluGx x₀ y₀ / (x - x₀) := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.equation_iff] at hP hQ
  simp only [Affine.slope_of_X_ne hx, Affine.addX, veluGx]
  field_simp
  linear_combination hP - hQ - (y - y₀) * hord

omit [DecidableEq F] in

private theorem velu2X_sub_velu2X {x₁ x₂ : F} (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀) :
    W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
          / ((x₁ - x₀) * (x₂ - x₀)) := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  simp only [velu2X]
  field_simp
  ring

omit [DecidableEq F] in

private theorem velu2X_eq_iff {x₁ x₂ : F} (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀) :
    W.velu2X x₀ y₀ x₁ = W.velu2X x₀ y₀ x₂
      ↔ x₁ = x₂ ∨ (x₁ - x₀) * (x₂ - x₀) = W.veluGx x₀ y₀ := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  rw [← sub_eq_zero, velu2X_sub_velu2X hx₁ hx₂, div_eq_zero_iff, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]
  simp only [mul_ne_zero hd₁ hd₂, or_false]

private theorem velu2X_addKernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (ht : W.veluGx x₀ y₀ ≠ 0) (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
      = W.velu2X x₀ y₀ x := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have htd : W.veluGx x₀ y₀ / (x - x₀) ≠ 0 := div_ne_zero ht hd
  rw [velu2_addX_kernel hP hQ hgy hx]
  simp only [velu2X, add_sub_cancel_left]
  field_simp
  ring

private theorem velu2_addY_kernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀
      = -(W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀)) / (x - x₀) ^ 2 := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hxP := velu2_addX_kernel hP hQ hgy hx
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.slope_of_X_ne hx] at hxP ⊢
  rw [hxP]
  field_simp
  linear_combination -((x - x₀) ^ 2 * hord)

private theorem velu2Y_addKernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (ht : W.veluGx x₀ y₀ ≠ 0) (hx : x ≠ x₀) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
        (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀))
      = W.velu2Y x₀ y₀ x y := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hxP := velu2_addX_kernel hP hQ hgy hx
  have hyP := velu2_addY_kernel hP hQ hgy hx
  simp only [velu2Y]
  have htd : W.veluGx x₀ y₀ / (x - x₀) ≠ 0 := div_ne_zero ht hd

  rw [hxP, add_sub_cancel_left]

  have key : W.veluGx x₀ y₀
        * (W.a₁ * (W.veluGx x₀ y₀ / (x - x₀))
            + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀)
        / (W.veluGx x₀ y₀ / (x - x₀)) ^ 2
      = y₀ - y := by
    rw [sub_eq_iff_eq_add.mp hyP]
    field_simp
    ring
  rw [key]
  linear_combination hyP

variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

omit [DecidableEq F] in

private lemma v2ker_some_congr {W' : Affine F} {u₁ u₂ v₁ v₂ : F}
    {h₁ : W'.Nonsingular u₁ v₁} {h₂ : W'.Nonsingular u₂ v₂} (hX : u₁ = u₂) (hY : v₁ = v₂) :
    Affine.Point.some u₁ v₁ h₁ = Affine.Point.some u₂ v₂ h₂ := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  subst hX; subst hY; rfl

include hchar hQ hgy hΔ in

private theorem veluPointMap2_add_kernel_gen (hQns : W.toAffine.Nonsingular x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P + .some x₀ y₀ hQns)
      = veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := veluOrderTwoAddKernel_axiomAnchor
  have ht : W.veluGx x₀ y₀ ≠ 0 := veluGx_ne_zero_of_quotΔ hQ hgy hΔ

  have h2P₀ : (2 : ℕ) • (Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = 0 :=
    Affine.two_nsmul_some_eq_zero_of_veluGy_eq_zero hgy hQns
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, zero_add, Affine.Point.zero_def, veluPointMap2_zero]
    exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hQns rfl
  | some x y h =>
    by_cases hx : x = x₀
    ·
      have hPP₀ : Affine.Point.some x y h = Affine.Point.some x₀ y₀ hQns :=
        Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hx
      rw [hPP₀, ← two_nsmul, h2P₀, veluPointMap2_some_of_eq hchar hQ hgy hΔ hQns rfl]
      rfl
    ·
      have hnsA : W.toAffine.Nonsingular
          (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
          (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) :=
        Affine.nonsingular_add h hQns fun hc => hx hc.1
      have hPP₀ : Affine.Point.some x y h + Affine.Point.some x₀ y₀ hQns
          = Affine.Point.some _ _ hnsA := Affine.Point.add_of_X_ne hx

      have hxA : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) ≠ x₀ := by
        rw [velu2_addX_kernel h.1 hQ hgy hx]
        simpa using div_ne_zero ht (sub_ne_zero.mpr hx)
      rw [hPP₀, veluPointMap2_some_of_ne hchar hQ hgy hΔ hnsA hxA,
        veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx]
      exact v2ker_some_congr (velu2X_addKernel h.1 hQ hgy ht hx)
        (velu2Y_addKernel h.1 hQ hgy ht hx)

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoAddKernel

section Piece_VeluOrderTwoSecantXContent
set_option autoImplicit false


namespace WeierstrassCurve

private theorem veluOrderTwoSecantXContent_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section CommRing

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x₁ y₁ x₂ y₂ : R}

private theorem velu2_secX_SI2 (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (x₁ - x₀) * (x₂ - x₀) * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
      = ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  have _ := veluOrderTwoSecantXContent_axiomAnchor
  rw [Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [veluGx]
  linear_combination (-(x₂ - x₀) ^ 2) * hP₁ + (x₁ - x₀) ^ 2 * hP₂
    + (-(x₁ - x₂) * ((x₁ - x₀) + (x₂ - x₀))) * hQ
    + ((x₂ - x₀) ^ 2 * y₁ - (x₁ - x₀) ^ 2 * y₂
        + (x₁ - x₂) * ((x₁ - x₀) + (x₂ - x₀)) * y₀) * hord

private theorem velu2_secX_SI3 (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2)
        * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  have _ := veluOrderTwoSecantXContent_axiomAnchor
  rw [Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [veluGx]
  linear_combination
    (-W.a₁*x₀*x₁ + W.a₁*x₀*x₂ + W.a₁*x₁*x₂ - W.a₁*x₂^2 - x₀*y₁ + x₀*y₂ - x₁*y₀ + x₁*y₂ + x₂*y₀
     + x₂*y₁ - 2*x₂*y₂) * hP₁
    + (W.a₁*x₀*x₁ - W.a₁*x₀*x₂ - W.a₁*x₁^2 + W.a₁*x₁*x₂ + x₀*y₁ - x₀*y₂ + x₁*y₀ - 2*x₁*y₁
     + x₁*y₂ - x₂*y₀ + x₂*y₁) * hP₂
    + ((x₁ - x₂) * (W.a₁ * (x₁ - x₂) + 2 * (y₁ - y₂))) * hQ
    + (-(W.a₁ * (x₁ - x₂) + (y₁ - y₂))
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀))) * hord

end CommRing

end WeierstrassCurve
end Piece_VeluOrderTwoSecantXContent

section Piece_VeluOrderTwoTangentYContent
set_option autoImplicit false
set_option maxRecDepth 8000


namespace WeierstrassCurve

private theorem veluOrderTwoTangentYContent_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

end Field

section CommRing

/-- `velu2_tanY_SI2c` in shifted coordinates (port-local): with `u = x-x₀`,
`v = y-y₀`, `β = a₂+3x₀`, `G = veluGx x₀ y₀`, `D = 2v+a₁u`, `E = 3u²+2βu+G-a₁v`,
the statement is a 9-term multiple of the shifted curve.  Replaces the pin's
4.8 kB raw-monomial certificate; see `TOPIC-order-two-tangent-direct.md`. -/
private lemma tanY_SI2c_shifted {F : Type*} [CommRing F] (a₁ β G u v : F)
    (h1 : v ^ 2 + a₁ * u * v - (u ^ 3 + β * u ^ 2 + G * u) = 0) :
    (2 * v + a₁ * u) ^ 3 * (u ^ 2 - G) * v
        + (a₁ ^ 2 * u + 4 * (u ^ 2 + β * u + G)) * u ^ 2
          * ((3 * u ^ 2 + 2 * β * u + G - a₁ * v) ^ 2
              + a₁ * (3 * u ^ 2 + 2 * β * u + G - a₁ * v) * (2 * v + a₁ * u)
              - (β + 2 * u) * (2 * v + a₁ * u) ^ 2)
      - (u ^ 2 - G) * u * (3 * u ^ 2 + 2 * β * u + G - a₁ * v) * (2 * v + a₁ * u) ^ 2 = 0 := by
  linear_combination
    (-(4*G^2*u + 6*G*a₁^2*u^2 + 8*G*a₁*u*v + 16*G*β*u^2 + 24*G*u^3 + 8*G*v^2 + a₁^4*u^3
      + 8*a₁^2*β*u^3 + 10*a₁^2*u^4 - 8*a₁*u^3*v + 16*β^2*u^3 + 48*β*u^4 + 36*u^5
      - 8*u^2*v^2)) * h1


variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}

private theorem velu2_tanY_SI2c (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (2 * y + W.a₁ * x + W.a₃) ^ 3 * ((x - x₀) ^ 2 - W.veluGx x₀ y₀) * (y - y₀)
        + (W.a₁ ^ 2 * (x - x₀)
              + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (x - x₀) ^ 2
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
        - ((x - x₀) ^ 2 - W.veluGx x₀ y₀) * (x - x₀)
          * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = 0 := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluGx]
  have h1 : (y - y₀) ^ 2 + W.a₁ * (x - x₀) * (y - y₀)
      - ((x - x₀) ^ 3 + (W.a₂ + 3 * x₀) * (x - x₀) ^ 2
          + (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) * (x - x₀)) = 0 := by
    linear_combination hP - hQ - (y - y₀) * hord
  have hD : 2 * y + W.a₁ * x + W.a₃ = 2 * (y - y₀) + W.a₁ * (x - x₀) := by
    linear_combination hord
  have hE : W.a₁ ^ 2 * (x - x₀)
        + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)
      = W.a₁ ^ 2 * (x - x₀)
        + 4 * ((x - x₀) ^ 2 + (W.a₂ + 3 * x₀) * (x - x₀)
            + (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)) := by
    ring
  have hF : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
      = 3 * (x - x₀) ^ 2 + 2 * (W.a₂ + 3 * x₀) * (x - x₀)
        + (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) - W.a₁ * (y - y₀) := by
    ring
  have hG : W.a₂ + 2 * x + x₀ = (W.a₂ + 3 * x₀) + 2 * (x - x₀) := by
    ring
  rw [hD, hE, hF, hG]
  have hS := tanY_SI2c_shifted W.a₁ (W.a₂ + 3 * x₀)
    (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) (x - x₀) (y - y₀) h1
  exact hS

end CommRing

end WeierstrassCurve
end Piece_VeluOrderTwoTangentYContent

section Piece_VeluOrderTwoSecantAtoms
set_option autoImplicit false


namespace WeierstrassCurve

private theorem veluOrderTwoSecantAtoms_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x₁ y₁ x₂ y₂ : F}

private theorem velu2_dXA_cleared (hx12 : x₁ ≠ x₂) :
    (x₁ - x₂) ^ 2 * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
      = (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂)
          - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have _ := veluOrderTwoSecantAtoms_axiomAnchor
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  simp only [Affine.addX, Affine.slope_of_X_ne hx12]
  field_simp
  ring

variable (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
  (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂)

include hx12 hx₁ hx₂ hX12 in

private theorem velu2_slopeDiff_cleared :
    ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)
        - W.toAffine.slope x₁ x₂ y₁ y₂)
      * ((x₁ - x₀) * (x₂ - x₀)) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
      = W.veluGx x₀ y₀
        * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀)
            - W.a₁ * ((x₁ - x₀) * (x₂ - x₀))) := by
  have _ := veluOrderTwoSecantAtoms_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12

  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  rw [Affine.slope_of_X_ne hX12, Affine.slope_of_X_ne hx12,
    velu2X_sub_velu2X hx₁ hx₂]
  simp only [velu2Y]
  field_simp
  ring

include hx12 hx₁ hx₂ hX12 in

private theorem velu2_slopeSum_cleared :
    ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)
        + W.toAffine.slope x₁ x₂ y₁ y₂ + W.a₁)
      * ((x₁ - x₀) * (x₂ - x₀)) * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀))
          * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
              + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀)
              - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
        + ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀) * ((x₁ - x₀) + (x₂ - x₀))
          * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  have _ := veluOrderTwoSecantAtoms_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  rw [Affine.slope_of_X_ne hX12, Affine.slope_of_X_ne hx12,
    velu2X_sub_velu2X hx₁ hx₂]
  simp only [velu2Y]
  field_simp
  ring

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoSecantAtoms

section Piece_VeluOrderTwoSecantCarrier
set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

private theorem veluOrderTwoSecantCarrier_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (x₀ y₀ : F)

private abbrev _root_.WeierstrassCurve.VeluOrderTwoSecantCompatDiffAvoidAt : Prop :=
  ∀ ⦃x₁ y₁ x₂ y₂ : F⦄, W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ →
    x₁ ≠ x₂ → x₁ ≠ x₀ → x₂ ≠ x₀ →
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀ →
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀ →
    W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂
    ∧ W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
              (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂))
    ∧ W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
        = (W.veluQuotient2 x₀ y₀).toAffine.addY
            (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂) (W.velu2Y x₀ y₀ x₁ y₁)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
              (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂))


private abbrev _root_.WeierstrassCurve.VeluOrderTwoTangentCompatAt : Prop :=
  ∀ ⦃x y : F⦄, W.toAffine.Equation x y → y ≠ W.toAffine.negY x y → x ≠ x₀ →
    W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀ →
    W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
    ∧ W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
              (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))
    ∧ W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
          (W.toAffine.addY x x y (W.toAffine.slope x x y y))
        = (W.veluQuotient2 x₀ y₀).toAffine.addY
            (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
              (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))


variable {x₀ y₀}
variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

include hchar hQ hgy hΔ in

private theorem veluPointMap2_add_of_secant_diffAvoid
    (hsec : W.VeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀)
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ
        ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + Affine.Point.some x₂ y₂ h₂)
      = veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₁ y₁ h₁)
        + veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₂ y₂ h₂) := by
  have _ := veluOrderTwoSecantCarrier_axiomAnchor
  obtain ⟨hX12, hXeq, hYeq⟩ := hsec h₁.1 h₂.1 hx12 hx₁ hx₂ hsp hsm
  rw [Affine.Point.add_of_X_ne hx12, veluPointMap2_some_of_ne hchar hQ hgy hΔ _ hsp,
    veluPointMap2_some_of_ne hchar hQ hgy hΔ h₁ hx₁,
    veluPointMap2_some_of_ne hchar hQ hgy hΔ h₂ hx₂]
  rw [Affine.Point.add_of_X_ne hX12]
  exact v2ker_some_congr hXeq hYeq

include hchar hQ hgy hΔ in

private theorem veluPointMap2_add_self_of_tangent
    (htan : W.VeluOrderTwoTangentCompatAt x₀ y₀)
    {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ
        ((Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h)
      = veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x y h)
        + veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x y h) := by
  have _ := veluOrderTwoSecantCarrier_axiomAnchor
  obtain ⟨hY, hXeq, hYeq⟩ := htan h.1 hy hx hx2
  rw [Affine.Point.add_self_of_Y_ne hy, veluPointMap2_some_of_ne hchar hQ hgy hΔ _ hx2,
    veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx]
  rw [Affine.Point.add_self_of_Y_ne hY]
  exact v2ker_some_congr hXeq hYeq

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoSecantCarrier

section Piece_VeluOrderTwoSecantConjunctOne
set_option autoImplicit false


namespace WeierstrassCurve

private theorem veluOrderTwoSecantConjunctOne_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

private theorem velu2_quotNegY_sub_factored (hgy : W.veluGy x₀ y₀ = 0)
    {x : F} (y : F) (hx : x ≠ x₀) :
    (x - x₀) ^ 2
        * (W.velu2Y x₀ y₀ x y
            - (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y))
      = (y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀) := by
  have _ := veluOrderTwoSecantConjunctOne_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2X, velu2Y, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃, veluGx]
  field_simp
  linear_combination (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) * hord

variable (hgy : W.veluGy x₀ y₀ = 0) (hQns : W.toAffine.Nonsingular x₀ y₀)

include hgy hQns in

private theorem velu2X_ne_of_diffAvoid
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀) :
    W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂ := by
  have _ := veluOrderTwoSecantConjunctOne_axiomAnchor
  intro hXeq
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁

  have hfib : (x₁ - x₀) * (x₂ - x₀) = W.veluGx x₀ y₀ :=
    ((velu2X_eq_iff hx₁ hx₂).mp hXeq).resolve_left hx12

  have hx₂eq : x₂ = W.toAffine.addX x₁ x₀ (W.toAffine.slope x₁ x₀ y₁ y₀) := by
    rw [velu2_addX_kernel h₁.1 hQns.1 hgy hx₁]
    field_simp
    linear_combination hfib

  have hnsA : W.toAffine.Nonsingular
      (W.toAffine.addX x₁ x₀ (W.toAffine.slope x₁ x₀ y₁ y₀))
      (W.toAffine.addY x₁ x₀ y₁ (W.toAffine.slope x₁ x₀ y₁ y₀)) :=
    Affine.nonsingular_add h₁ hQns fun hxy => hx₁ hxy.1
  have hP1P0 : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + Affine.Point.some x₀ y₀ hQns
      = Affine.Point.some _ _ hnsA :=
    Affine.Point.add_of_X_ne hx₁

  have hnegP₀ : -(Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
    rw [Affine.Point.neg_some]
    exact v2ker_some_congr rfl (negY_eq_of_veluGy_eq_zero hgy)

  rcases (Affine.Point.X_eq_iff (h₁ := h₂) (h₂ := hnsA)).mp hx₂eq with hPeq | hPeq
  ·
    refine hsm ?_
    have hdiff : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - Affine.Point.some x₂ y₂ h₂
        = Affine.Point.some x₀ y₀ hQns := by
      rw [hPeq, ← hP1P0, sub_add_cancel_left, hnegP₀]
    rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx12,
      Affine.Point.some.injEq] at hdiff
    exact hdiff.1
  ·
    refine hsp ?_
    have hsum : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + Affine.Point.some x₂ y₂ h₂
        = Affine.Point.some x₀ y₀ hQns := by
      rw [hPeq, ← hP1P0, ← sub_eq_add_neg, sub_add_cancel_left, hnegP₀]
    rw [Affine.Point.add_of_X_ne hx12, Affine.Point.some.injEq] at hsum
    exact hsum.1

include hgy hQns in

private theorem velu2Y_ne_quotNegY_of_tangent
    {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀) :
    W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have _ := veluOrderTwoSecantConjunctOne_axiomAnchor
  intro hcon
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx

  have hfact : (y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀) = 0 := by
    have h0 := velu2_quotNegY_sub_factored hgy y hx
    rw [sub_eq_zero.mpr hcon, mul_zero] at h0
    exact h0.symm

  have hd2t : (x - x₀) ^ 2 = W.veluGx x₀ y₀ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hy))

  have hxPP₀ : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) = x := by
    rw [velu2_addX_kernel h.1 hQns.1 hgy hx, ← hd2t]
    field_simp
    ring

  have hnsA : W.toAffine.Nonsingular
      (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
      (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) :=
    Affine.nonsingular_add h hQns fun hxy => hx hxy.1
  have hPP₀ : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x₀ y₀ hQns
      = Affine.Point.some _ _ hnsA :=
    Affine.Point.add_of_X_ne hx

  have hnegP₀ : -(Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
    rw [Affine.Point.neg_some]
    exact v2ker_some_congr rfl (negY_eq_of_veluGy_eq_zero hgy)

  rcases (Affine.Point.X_eq_iff (h₁ := hnsA) (h₂ := h)).mp hxPP₀ with hPeq | hPeq
  ·
    rw [← hPP₀, add_eq_left] at hPeq
    exact Affine.Point.some_ne_zero hQns hPeq
  ·
    refine hx2 ?_
    have h2P : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h
        = Affine.Point.some x₀ y₀ hQns := by
      have heq := hPP₀.trans hPeq
      rw [← hnegP₀, eq_neg_iff_add_eq_zero, add_right_comm, heq, neg_add_cancel]
    rw [Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h2P
    exact h2P.1

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoSecantConjunctOne

section Piece_VeluOrderTwoSecantAlign
set_option autoImplicit false
set_option maxRecDepth 100000


namespace WeierstrassCurve

private theorem veluOrderTwoSecantAlign_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
  {x₀ y₀ x₁ y₁ x₂ y₂ : F}

private theorem velu2_secX_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)) := by
  have _ := veluOrderTwoSecantAlign_axiomAnchor
  have hSI2 := velu2_secX_SI2 hP₁ hP₂ hQ hord
  have hSI3 := velu2_secX_SI3 hP₁ hP₂ hQ hord
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  have hdA : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀ ≠ 0 := sub_ne_zero.mpr hsp
  rw [Affine.slope_of_X_ne hX12, velu2X_sub_velu2X hx₁ hx₂]

  conv_lhs => rw [velu2X, add_comm]
  rw [← eq_sub_iff_add_eq, div_eq_iff hdA, ← sub_eq_zero]

  simp only [velu2X, velu2Y, Affine.slope_of_X_ne hx12, Affine.addX, veluQuotient2_a₁,
    veluQuotient2_a₂]
  -- Port-local: name the shifted atoms in the goal and in the `SI2`/`SI3`
  -- hypotheses, so the ring works on ~300 shifted monomials instead of the raw
  -- presentation (see `TOPIC-order-two-tangent-direct.md` §6.2).  Generalising
  -- `x₁-x₀`, `x₂-x₀`, `x₁-x₂` and `veluGx` loses the definitional relation
  -- `d = u₁-u₂`, which `hrel` restores and the certificate uses.
  generalize hu₁ : x₁ - x₀ = u₁ at *
  generalize hu₂ : x₂ - x₀ = u₂ at *
  generalize hd_def : x₁ - x₂ = d at *
  generalize hG : W.veluGx x₀ y₀ = G at *
  have hrel : d = u₁ - u₂ := by rw [← hd_def, ← hu₁, ← hu₂]; ring
  field_simp [hd₁, hd₂, hd₁₂, hD₁₂]
  linear_combination
    (G * d * (u₁ * u₂ - G) * (d ^ 2 * (u₁ * u₂) + ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * d - (W.a₂ + x₀ + x₁ + x₂) * d ^ 2) * (u₁ + u₂))) * hSI2
    + (-(G * d ^ 2 * (u₁ * u₂) * (u₂ * (W.a₁ * u₁ + y₁ - y₀) + u₁ * (W.a₁ * u₂ + y₂ - y₀) - W.a₁ * (u₁ * u₂)))) * hSI3
    + (-(G * (-W.a₁ * u₁ * u₂ + u₁ * y₀ - u₁ * y₂ + u₂ * y₀ - u₂ * y₁)
          * (-W.a₁ * d * y₁ + W.a₁ * d * y₂ + W.a₂ * d ^ 2 + d ^ 2 * x₀ + d ^ 2 * x₁ + d ^ 2 * x₂ - y₁ ^ 2 + 2 * y₁ * y₂ - y₂ ^ 2)
          * (-G * W.a₁ * u₁ ^ 2 * u₂ + G * W.a₁ * u₁ * u₂ ^ 2 + G * u₁ ^ 2 * y₀ - G * u₁ ^ 2 * y₂ + G * u₁ * u₂ * y₁ - G * u₁ * u₂ * y₂ - G * u₂ ^ 2 * y₀ + G * u₂ ^ 2 * y₁ - W.a₁ * d * u₁ ^ 2 * u₂ ^ 2 + d * u₁ ^ 2 * u₂ * y₀ - d * u₁ ^ 2 * u₂ * y₂ + d * u₁ * u₂ ^ 2 * y₀ - d * u₁ * u₂ ^ 2 * y₁ - 2 * u₁ ^ 2 * u₂ ^ 2 * y₁ + 2 * u₁ ^ 2 * u₂ ^ 2 * y₂))) * hrel

private theorem velu2_secY_negAddY_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (W.veluQuotient2 x₀ y₀).toAffine.negAddY (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)) := by
  have _ := veluOrderTwoSecantAlign_axiomAnchor
  have hSIY := velu2_secant_negAddY_cleared_identity hP₁ hP₂ hQ hord hx12
  have hXalign := velu2_secX_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hdA : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀ ≠ 0 := sub_ne_zero.mpr hsp

  have hColQ :
      (W.velu2X x₀ y₀ x₂ - W.velu2X x₀ y₀ x₁)
          * (W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
                (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
              - W.velu2Y x₀ y₀ x₁ y₁)
        = (W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
              - W.velu2X x₀ y₀ x₁)
          * (W.velu2Y x₀ y₀ x₂ y₂ - W.velu2Y x₀ y₀ x₁ y₁) := by

    generalize hxA_def : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) = xA at *
    generalize hnAY_def : W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) = nAY at *

    have hxA_rel : (x₁ - x₂) ^ 2 * (xA - x₀)
        = (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂)
            - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
      rw [← hxA_def]; simp only [Affine.slope_of_X_ne hx12, Affine.addX]; field_simp; ring
    have hnAY_rel : (x₁ - x₂) * (nAY - y₁) = (y₁ - y₂) * (xA - x₁) := by
      rw [← hnAY_def, ← hxA_def]
      simp only [Affine.slope_of_X_ne hx12, Affine.addX, Affine.negAddY]; field_simp; ring
    -- Factor each `velu2X`/`velu2Y` difference into a *single* fraction, so the
    -- clearing below is the reduced cross-multiplication of the shifted atoms
    -- (`uᵢ = xᵢ-x₀`, `U = xA-x₀`, `G = veluGx`).  The resulting polynomial
    -- identity is 30 terms, and its certificate against `hSIY`/`hnAY_rel` is
    -- 4+4 monomials, replacing the ported ~200-monomial certificate.
    have hX21 : W.velu2X x₀ y₀ x₂ - W.velu2X x₀ y₀ x₁
        = (x₁ - x₂) * (W.veluGx x₀ y₀ - (x₁ - x₀) * (x₂ - x₀))
            / ((x₁ - x₀) * (x₂ - x₀)) := by
      simp only [velu2X]; field_simp; ring
    have hXR1 : W.velu2X x₀ y₀ xA - W.velu2X x₀ y₀ x₁
        = (x₁ - xA) * (W.veluGx x₀ y₀ - (x₁ - x₀) * (xA - x₀))
            / ((x₁ - x₀) * (xA - x₀)) := by
      simp only [velu2X]; field_simp; ring
    have hYR1 : W.velu2Y x₀ y₀ xA nAY - W.velu2Y x₀ y₀ x₁ y₁
        = (((nAY - y₀) * (xA - x₀) ^ 2
                - W.veluGx x₀ y₀ * (W.a₁ * (xA - x₀) + (nAY - y₀))) * (x₁ - x₀) ^ 2
              - ((y₁ - y₀) * (x₁ - x₀) ^ 2
                  - W.veluGx x₀ y₀ * (W.a₁ * (x₁ - x₀) + (y₁ - y₀))) * (xA - x₀) ^ 2)
            / ((xA - x₀) ^ 2 * (x₁ - x₀) ^ 2) := by
      simp only [velu2Y]; field_simp; ring
    have hY21 : W.velu2Y x₀ y₀ x₂ y₂ - W.velu2Y x₀ y₀ x₁ y₁
        = (((y₂ - y₀) * (x₂ - x₀) ^ 2
                - W.veluGx x₀ y₀ * (W.a₁ * (x₂ - x₀) + (y₂ - y₀))) * (x₁ - x₀) ^ 2
              - ((y₁ - y₀) * (x₁ - x₀) ^ 2
                  - W.veluGx x₀ y₀ * (W.a₁ * (x₁ - x₀) + (y₁ - y₀))) * (x₂ - x₀) ^ 2)
            / ((x₁ - x₀) ^ 2 * (x₂ - x₀) ^ 2) := by
      simp only [velu2Y]; field_simp; ring
    rw [hX21, hXR1, hYR1, hY21]
    field_simp [hd₁, hd₂, hdA]
    linear_combination
      (W.veluGx x₀ y₀ * (x₁ - x₀) * (x₁ - xA) * (x₁ - x₂)) * hSIY
      + (-(xA - x₀) * (x₁ - x₀) * (x₂ - x₀) * ((xA - x₀)*(x₁ - x₀) - W.veluGx x₀ y₀)
          * ((x₁ - x₀)*(x₂ - x₀) - W.veluGx x₀ y₀)) * hnAY_rel
  conv_rhs => rw [Affine.negAddY, ← hXalign, Affine.slope_of_X_ne hX12]
  field_simp
  linear_combination -hColQ

private theorem velu2_secY_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (W.veluQuotient2 x₀ y₀).toAffine.addY (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)) := by
  have _ := veluOrderTwoSecantAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hXalign := velu2_secX_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  have hnAY := velu2_secY_negAddY_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  rw [Affine.addY, velu2Y_negY hgy, Affine.addY, hXalign, hnAY]

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoSecantAlign

section Piece_VeluOrderTwoTangentXAlign
set_option autoImplicit false
set_option maxRecDepth 8000


namespace WeierstrassCurve

private theorem veluOrderTwoTangentXAlign_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

private theorem velu2_tan_d2P_cleared (hy : y ≠ W.toAffine.negY x y) :
    (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - W.toAffine.negY x y) ^ 2
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
        + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
        - (W.a₂ + 2 * x + x₀) * (y - W.toAffine.negY x y) ^ 2 := by
  have _ := veluOrderTwoTangentXAlign_axiomAnchor
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  simp only [Affine.slope_of_Y_ne rfl hy, Affine.addX]
  field_simp
  ring

private theorem velu2_tan_quotSlope_eq (hgy : W.veluGy x₀ y₀ = 0)
    (hx : x ≠ x₀) (hy : y ≠ W.toAffine.negY x y)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    (W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
        (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)
      = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)
            + W.veluGx x₀ y₀
              * (W.a₁ ^ 2 * (x - x₀)
                  + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          / ((y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)) := by
  have _ := veluOrderTwoTangentXAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hsdp : W.velu2Y x₀ y₀ x y
      - (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) ≠ 0 :=
    sub_ne_zero.mpr hY

  have hD : (x - x₀) ^ 2 - W.veluGx x₀ y₀ ≠ 0 := by
    intro hD0
    refine hsdp ?_
    have h5a := velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  rw [Affine.slope_of_Y_ne rfl hY, div_eq_div_iff hsdp (mul_ne_zero hsd hD)]
  simp only [velu2X, velu2Y, veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃,
    veluQuotient2_a₄, Affine.negY, veluGx]
  field_simp
  linear_combination (-(3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
      * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
            * ((x - x₀) ^ 2 - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀))
          + (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
            * (W.a₁ ^ 2 * (x - x₀)
                + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))) * hord

private theorem velu2_tanX_align (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)) := by
  have _ := veluOrderTwoTangentXAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hD : (x - x₀) ^ 2 - W.veluGx x₀ y₀ ≠ 0 := by
    intro hD0
    refine sub_ne_zero.mpr hY ?_
    have h5a := velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  have hNpp := velu2_tangent_addX_cleared_identity hP hQ hord

  rw [velu2_tan_quotSlope_eq hgy hx hy hY]
  conv_lhs => rw [velu2X, add_comm]
  rw [← eq_sub_iff_add_eq, div_eq_iff (sub_ne_zero.mpr hx2), ← sub_eq_zero]
  simp only [velu2X, Affine.slope_of_Y_ne rfl hy, Affine.addX, veluQuotient2_a₁,
    veluQuotient2_a₂]
  simp only [Affine.negY] at *
  simp only [show W.toAffine.a₁ = W.a₁ from rfl, show W.toAffine.a₂ = W.a₂ from rfl,
    show W.toAffine.a₃ = W.a₃ from rfl, show W.toAffine.a₄ = W.a₄ from rfl] at *
  simp only [show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring,
    show 6 * x ^ 2 + (4 * W.a₂ + W.a₁ ^ 2) * x + 2 * W.a₄ + W.a₁ * W.a₃
        = W.a₁ * (2 * y + W.a₁ * x + W.a₃) + 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
        by ring] at *
  generalize hA : W.a₁ ^ 2 * (x - x₀) + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀) = A at *
  generalize hE : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = E at *
  generalize hDdef : 2 * y + W.a₁ * x + W.a₃ = D at *
  generalize hG : W.veluGx x₀ y₀ = G at *
  generalize hu : x - x₀ = u at *
  field_simp [hsd, hd, hD]
  linear_combination -G * hNpp

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoTangentXAlign

section Piece_VeluOrderTwoTangentYAlign
set_option autoImplicit false
set_option maxRecDepth 100000


namespace WeierstrassCurve

private theorem veluOrderTwoTangentYAlign_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

private theorem velu2_tanY_negAddY_align (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.negAddY x x y (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.negAddY (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          (W.velu2Y x₀ y₀ x y)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)) := by
  have _ := veluOrderTwoTangentYAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hD : (x - x₀) ^ 2 - W.veluGx x₀ y₀ ≠ 0 := by
    intro hD0
    refine sub_ne_zero.mpr hY ?_
    have h5a := velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  have hd2P : W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀ ≠ 0 := sub_ne_zero.mpr hx2
  have hsdEq : (2 * y + W.a₁ * x + W.a₃) = y - W.toAffine.negY x y := by
    simp only [Affine.negY]; ring
  have hSIYt := velu2_tangent_negAddY_cleared_identity hP hQ hord hy
  have hSI2c := velu2_tanY_SI2c hP hQ hord

  rw [hsdEq] at hSI2c
  have hXalign := velu2_tanX_align hP hQ hgy hy hx hx2 hY

  have hColQ :
      (W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
              (W.toAffine.negAddY x x y (W.toAffine.slope x x y y))
            - W.velu2Y x₀ y₀ x y)
          * ((y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀))
        = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)
              + W.veluGx x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
              - W.velu2X x₀ y₀ x) := by

    set x2P := W.toAffine.addX x x (W.toAffine.slope x x y y) with hx2P_def
    set nAY := W.toAffine.negAddY x x y (W.toAffine.slope x x y y) with hnAY_def

    have hx2P_rel : (x2P - x₀) * (y - W.toAffine.negY x y) ^ 2
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
          + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
          - (W.a₂ + 2 * x + x₀) * (y - W.toAffine.negY x y) ^ 2 := by
      rw [hx2P_def]; exact velu2_tan_d2P_cleared hy
    have hnAY_rel : (y - W.toAffine.negY x y) * (nAY - y)
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (x2P - x) := by
      rw [hnAY_def, hx2P_def]
      simp only [Affine.slope_of_Y_ne rfl hy, Affine.addX, Affine.negAddY]
      field_simp; ring
    simp only [velu2X, velu2Y]
    generalize hA : W.a₁ ^ 2 * (x - x₀)
        + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀) = A at *
    generalize hE : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = E at *
    generalize hG : W.veluGx x₀ y₀ = G at *
    field_simp [hd, hd2P]
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hsd) hd) ?_
    linear_combination
      (-G * ((x - x₀) ^ 2 - G) * (y - W.toAffine.negY x y) ^ 3) * hSIYt
      + (-G * (x2P - x) * ((x - x₀) * (x2P - x₀) - G) * A * (x - x₀) ^ 2) * hx2P_rel
      + ((x - x₀) * (y - W.toAffine.negY x y) ^ 2 * ((x - x₀) ^ 2 - G)
          * ((x - x₀) * (x2P - x₀) - G)
          * ((x - x₀) * (x2P - x₀) + G)) * hnAY_rel
      + (-G * (x2P - x) * ((x - x₀) * (x2P - x₀) - G)) * hSI2c

  conv_rhs => rw [Affine.negAddY, ← hXalign, velu2_tan_quotSlope_eq hgy hx hy hY]
  rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add, eq_div_iff (mul_ne_zero hsd hD)]
  linear_combination hColQ

private theorem velu2_tanY_align (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.addY (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          (W.velu2Y x₀ y₀ x y)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)) := by
  have _ := veluOrderTwoTangentYAlign_axiomAnchor
  have hXalign := velu2_tanX_align hP hQ hgy hy hx hx2 hY
  have hnAY := velu2_tanY_negAddY_align hP hQ hgy hy hx hx2 hY
  rw [Affine.addY, velu2Y_negY hgy, Affine.addY, hXalign, hnAY]

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoTangentYAlign

section PieceAbbrev

namespace WeierstrassCurve

section Held

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

variable (W x₀ y₀) in

private abbrev _root_.WeierstrassCurve.VeluOrderTwoAddCompatAt (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) : Prop :=
  ∀ P Q : W.toAffine.Point,
    veluPointMap2 h2 hQ hgy hΔ (P + Q) = veluPointMap2 h2 hQ hgy hΔ P + veluPointMap2 h2 hQ hgy hΔ Q

end Held

end WeierstrassCurve

end PieceAbbrev

section Piece_VeluOrderTwoAddCompatReduce
set_option autoImplicit false


namespace WeierstrassCurve

private theorem veluOrderTwoAddCompatReduce_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

private theorem velu2_kernel_nonsingular (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.toAffine.Nonsingular x₀ y₀ := by
  have _ := veluOrderTwoAddCompatReduce_axiomAnchor
  have ht : W.veluGx x₀ y₀ ≠ 0 := veluGx_ne_zero_of_quotΔ hQ hgy hΔ
  simp only [veluGx] at ht
  refine (Affine.nonsingular_iff ..).mpr ⟨hQ, Or.inl fun hcon => ht ?_⟩
  linear_combination -hcon

variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

include hchar hQ hgy hΔ in

private theorem veluPointMap2_add_of_right_ker {K : W.toAffine.Point}
    (hK : veluPointMap2 hchar hQ hgy hΔ K = 0) (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P + K) = veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := veluOrderTwoAddCompatReduce_axiomAnchor
  have hQns : W.toAffine.Nonsingular x₀ y₀ := velu2_kernel_nonsingular hQ hgy hΔ
  cases K with
  | zero => rw [← Affine.Point.zero_def, add_zero]
  | some x y h =>
    by_cases hx : x = x₀
    ·
      rw [Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hx]
      exact veluPointMap2_add_kernel_gen hchar hQ hgy hΔ hQns P
    ·
      rw [veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx] at hK
      exact absurd hK (Affine.Point.some_ne_zero _)

include hchar hQ hgy hΔ in

private theorem veluPointMap2_add_self (htan : W.VeluOrderTwoTangentCompatAt x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P + P)
      = veluPointMap2 hchar hQ hgy hΔ P + veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := veluOrderTwoAddCompatReduce_axiomAnchor
  have hQns : W.toAffine.Nonsingular x₀ y₀ := velu2_kernel_nonsingular hQ hgy hΔ
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, add_zero, Affine.Point.zero_def, veluPointMap2_zero,
      ← Affine.Point.zero_def, add_zero]
  | some x y h =>
    by_cases hy : y = W.toAffine.negY x y
    ·
      have hPnP : (Affine.Point.some x y h : W.toAffine.Point) = -Affine.Point.some x y h := by
        rw [Affine.Point.neg_some]; exact v2ker_some_congr rfl hy
      have h2P0 : (Affine.Point.some x y h : W.toAffine.Point) + .some x y h = 0 := by
        nth_rw 1 [hPnP]; exact neg_add_cancel _
      have h2φP : veluPointMap2 hchar hQ hgy hΔ (.some x y h)
          + veluPointMap2 hchar hQ hgy hΔ (.some x y h) = 0 := by
        nth_rw 1 [hPnP, veluPointMap2_neg hchar hQ hgy hΔ]; exact neg_add_cancel _
      rw [h2P0, Affine.Point.zero_def, veluPointMap2_zero]
      exact h2φP.symm
    ·
      have hx : x ≠ x₀ := by
        intro hcon
        have hPP₀ : (Affine.Point.some x y h : W.toAffine.Point)
            = Affine.Point.some x₀ y₀ hQns :=
          Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hcon
        rw [Affine.Point.some.injEq] at hPP₀
        exact hy (hcon ▸ hPP₀.2 ▸ (negY_eq_of_veluGy_eq_zero hgy).symm)
      by_cases hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) = x₀
      ·
        have hnsA : W.toAffine.Nonsingular
            (W.toAffine.addX x x (W.toAffine.slope x x y y))
            (W.toAffine.addY x x y (W.toAffine.slope x x y y)) :=
          Affine.nonsingular_add h h fun hxy => hy hxy.2
        have h2P : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h
            = Affine.Point.some x₀ y₀ hQns := by
          rw [Affine.Point.add_self_of_Y_ne hy]
          exact Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns hnsA hx2

        have hφ2P : veluPointMap2 hchar hQ hgy hΔ
            ((Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h) = 0 := by
          rw [h2P]; exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hQns rfl

        have hnegP₀ : -(Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
          rw [Affine.Point.neg_some]
          exact v2ker_some_congr rfl (negY_eq_of_veluGy_eq_zero hgy)
        have hnegP : -(Affine.Point.some x y h : W.toAffine.Point)
            = Affine.Point.some x y h + Affine.Point.some x₀ y₀ hQns := by
          rw [← hnegP₀, ← sub_eq_add_neg, ← h2P]; abel
        have h2φP : veluPointMap2 hchar hQ hgy hΔ (.some x y h)
            + veluPointMap2 hchar hQ hgy hΔ (.some x y h) = 0 :=
          add_eq_zero_iff_eq_neg.mpr <| by
            rw [← veluPointMap2_neg hchar hQ hgy hΔ, hnegP,
              veluPointMap2_add_kernel_gen hchar hQ hgy hΔ hQns]
        rw [hφ2P, h2φP]
      ·
        exact veluPointMap2_add_self_of_tangent hchar hQ hgy hΔ htan h hy hx hx2

include hchar hQ hgy hΔ in

private theorem veluPointMap2_add' (hsec : W.VeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀)
    (htan : W.VeluOrderTwoTangentCompatAt x₀ y₀) (P₁ P₂ : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P₁ + P₂)
      = veluPointMap2 hchar hQ hgy hΔ P₁ + veluPointMap2 hchar hQ hgy hΔ P₂ := by
  have _ := veluOrderTwoAddCompatReduce_axiomAnchor
  have hQns : W.toAffine.Nonsingular x₀ y₀ := velu2_kernel_nonsingular hQ hgy hΔ
  cases P₁ with
  | zero =>
    rw [← Affine.Point.zero_def, zero_add, Affine.Point.zero_def, veluPointMap2_zero,
      ← Affine.Point.zero_def, zero_add]
  | some x₁ y₁ h₁ =>
    cases P₂ with
    | zero =>
      rw [← Affine.Point.zero_def, add_zero, Affine.Point.zero_def, veluPointMap2_zero,
        ← Affine.Point.zero_def, add_zero]
    | some x₂ y₂ h₂ =>

      by_cases hx₂k : x₂ = x₀
      · have hK : veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₂ y₂ h₂) = 0 :=
          veluPointMap2_some_of_eq hchar hQ hgy hΔ h₂ hx₂k
        rw [veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hK, hK, add_zero]
      by_cases hx₁k : x₁ = x₀
      · have hK : veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₁ y₁ h₁) = 0 :=
          veluPointMap2_some_of_eq hchar hQ hgy hΔ h₁ hx₁k
        rw [add_comm, veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hK, hK, zero_add]

      by_cases hx12 : x₁ = x₂
      · rcases (Affine.Point.X_eq_iff (h₁ := h₂) (h₂ := h₁)).mp hx12.symm with hPeq | hPeq
        · rw [hPeq]; exact veluPointMap2_add_self hchar hQ hgy hΔ htan _
        · rw [hPeq, add_neg_cancel, Affine.Point.zero_def, veluPointMap2_zero,
            ← Affine.Point.zero_def, veluPointMap2_neg hchar hQ hgy hΔ, add_neg_cancel]

      by_cases hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) = x₀
      · have hAns : W.toAffine.Nonsingular
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
            (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) :=
          Affine.nonsingular_add h₁ h₂ fun hxy => hx12 hxy.1
        have hK0 : veluPointMap2 hchar hQ hgy hΔ
            ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) = 0 := by
          rw [Affine.Point.add_of_X_ne hx12]
          exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hAns hsp
        have hφ1 : veluPointMap2 hchar hQ hgy hΔ (.some x₁ y₁ h₁)
            = -(veluPointMap2 hchar hQ hgy hΔ (.some x₂ y₂ h₂)) := by
          have heq : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = -(.some x₂ y₂ h₂)
                + ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) := by abel
          rw [heq, veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hK0,
            veluPointMap2_neg hchar hQ hgy hΔ]
        rw [hK0, hφ1, neg_add_cancel]

      by_cases hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
          = x₀
      · have h₂' : W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
          (Affine.nonsingular_neg ..).mpr h₂
        have hDns : W.toAffine.Nonsingular
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
            (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) :=
          Affine.nonsingular_add h₁ h₂' fun hxy => hx12 hxy.1
        have hKD : veluPointMap2 hchar hQ hgy hΔ
            ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) = 0 := by
          rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx12]
          exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hDns hsm

        have hφeq : veluPointMap2 hchar hQ hgy hΔ (.some x₁ y₁ h₁)
            = veluPointMap2 hchar hQ hgy hΔ (.some x₂ y₂ h₂) := by
          have heq : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = (Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point)
                + ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) := by abel
          rw [heq, veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hKD]

        have heq2 : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂
            = ((Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point) + .some x₂ y₂ h₂)
              + ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) := by abel
        rw [heq2, veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hKD,
          veluPointMap2_add_self hchar hQ hgy hΔ htan, hφeq]

      exact veluPointMap2_add_of_secant_diffAvoid hchar hQ hgy hΔ hsec h₁ h₂ hx12 hx₁k
        hx₂k hsp hsm

include hchar hQ hgy hΔ in

private theorem veluOrderTwoAddCompatAt_of_carriers
    (hsec : W.VeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀)
    (htan : W.VeluOrderTwoTangentCompatAt x₀ y₀) :
    W.VeluOrderTwoAddCompatAt x₀ y₀ hchar hQ hgy hΔ :=
  veluPointMap2_add' hchar hQ hgy hΔ hsec htan

end Field

end WeierstrassCurve
end Piece_VeluOrderTwoAddCompatReduce

section Piece_VeluOrderTwoCarrierDischarge
set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

private theorem veluOrderTwoCarrierDischarge_axiomAnchor : True := by
  have _ := veluOrderTwoAddCompatReduce_axiomAnchor
  have _ := veluOrderTwoSecantConjunctOne_axiomAnchor
  have _ := veluOrderTwoSecantAlign_axiomAnchor
  have _ := veluOrderTwoTangentXAlign_axiomAnchor
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (x₀ y₀ : F)

private abbrev _root_.WeierstrassCurve.VeluOrderTwoTangentYAlignAt : Prop :=
  ∀ ⦃x y : F⦄, W.toAffine.Equation x y → y ≠ W.toAffine.negY x y → x ≠ x₀ →
    W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀ →
    W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) →
    W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.addY
          (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))

variable {x₀ y₀}
variable [W.IsElliptic]
variable (hgy : W.veluGy x₀ y₀ = 0) (hQns : W.toAffine.Nonsingular x₀ y₀)

include hgy hQns in

private theorem velu2_tangentCarrier_of_YAlign
    (hYal : W.VeluOrderTwoTangentYAlignAt x₀ y₀) :
    W.VeluOrderTwoTangentCompatAt x₀ y₀ := by
  have _ := veluOrderTwoCarrierDischarge_axiomAnchor
  intro x y hP hy hx hx2
  have hns := (Affine.equation_iff_nonsingular (W := W.toAffine)).mp hP
  have hY := velu2Y_ne_quotNegY_of_tangent hgy hQns hns hy hx hx2
  exact ⟨hY, velu2_tanX_align hP hQns.1 hgy hy hx hx2 hY, hYal hP hy hx hx2 hY⟩

include hgy hQns in

private theorem velu2_secantCarrier :
    W.VeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀ := by
  have _ := veluOrderTwoCarrierDischarge_axiomAnchor
  intro x₁ y₁ x₂ y₂ h₁ h₂ hx12 hx₁ hx₂ hsp hsm
  have hns₁ := (Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₁
  have hns₂ := (Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₂
  have hX12 := velu2X_ne_of_diffAvoid hgy hQns hns₁ hns₂ hx12 hx₁ hx₂ hsp hsm
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  exact ⟨hX12,
    velu2_secX_align h₁ h₂ hQns.1 hord hx12 hx₁ hx₂ hsp hX12,
    velu2_secY_align h₁ h₂ hQns.1 hgy hx12 hx₁ hx₂ hsp hX12⟩

include hgy hQns in

private theorem velu2_addCompatAt_of_YAlign
    (hchar : (2 : F) ≠ 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (hYal : W.VeluOrderTwoTangentYAlignAt x₀ y₀) :
    W.VeluOrderTwoAddCompatAt x₀ y₀ hchar hQns.1 hgy hΔ := by
  have _ := veluOrderTwoCarrierDischarge_axiomAnchor
  exact veluOrderTwoAddCompatAt_of_carriers hchar hQns.1 hgy hΔ
    (velu2_secantCarrier hgy hQns)
    (velu2_tangentCarrier_of_YAlign hgy hQns hYal)

end Field

end WeierstrassCurve

end
end Piece_VeluOrderTwoCarrierDischarge

set_option autoImplicit false


namespace WeierstrassCurve

theorem exists_addMonoidHom_coe_eq_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point,
      ⇑φ = veluPointMap2 h2 hQ hgy hΔ := by
  have hQns : W.toAffine.Nonsingular x₀ y₀ := W.toAffine.equation_iff_nonsingular.mp hQ
  have hadd : W.VeluOrderTwoAddCompatAt x₀ y₀ h2 hQns.1 hgy hΔ :=
    velu2_addCompatAt_of_YAlign hgy hQns h2 hΔ
      (fun _ _ hP hy hx hx2 hY => velu2_tanY_align hP hQns.1 hgy hy hx hx2 hY)
  exact ⟨AddMonoidHom.mk' (veluPointMap2 h2 hQ hgy hΔ) hadd, rfl⟩

end WeierstrassCurve
