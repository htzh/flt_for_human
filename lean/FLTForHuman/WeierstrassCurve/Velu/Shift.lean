/-
Translation normalization for the singleton Vélu identity.

Moving the kernel point `(x₀, y₀)` to the origin by the Weierstrass translation
`x = x' + x₀`, `y = y' + y₀` sends the curve `W` to `W.shiftCurve x₀ y₀`; the
translated curve's `a₆` is `W.qResidual x₀ y₀`, which vanishes exactly when the
point lies on `W`.  On the translated curve the cleared singleton deficit is a
small polynomial identity (52 monomials) whose certificate is a single square,
and the cleared deficit, the `Ψ₃`-cofactor and `Ψ₃` itself are all *invariant*
under the translation.  Hence the general statement follows from the normalized
one by rewriting, with no monomial certificate at all.

The singleton block is `private` in the pin's solution module
`P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
(pinned `aa2d8b3`); the public statement is `velu_singleton_map_equation` in
`Definitions/Def_WeierstrassCurve_VeluPointMap.lean`.
Reference (public mirror):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluPointMap.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Defs

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 8000

noncomputable section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The curve translated so that `(x₀, y₀)` becomes the origin.  This is Mathlib's
admissible change of variables `(u, r, s, t) = (1, x₀, 0, y₀)`, i.e.
`(X, Y) ↦ (X + x₀, Y + y₀)`; since `u = 1` is a unit the transport is division-free
and sound in every characteristic. -/
def shiftCurve (x₀ y₀ : R) : WeierstrassCurve R :=
  VariableChange.mk 1 x₀ 0 y₀ • W

/-- The identification with the Mathlib `VariableChange` action. -/
theorem shiftCurve_def (x₀ y₀ : R) :
    W.shiftCurve x₀ y₀ = VariableChange.mk 1 x₀ 0 y₀ • W := rfl

/-- The `hQ` residual: the translated curve's `a₆`, in Mathlib's `variableChange_a₆`
order. -/
def qResidual (x₀ y₀ : R) : R :=
  W.a₆ + x₀ * W.a₄ + x₀ ^ 2 * W.a₂ + x₀ ^ 3 - y₀ * W.a₃ - y₀ ^ 2 - x₀ * y₀ * W.a₁

/-- The cleared singleton deficit, as a function of the curve and the point. -/
def clr (x₀ y₀ x y : R) : R :=
  W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
    + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
    - (W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
      + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
      + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6)

@[simp] theorem shiftCurve_a₁ (x₀ y₀ : R) : (W.shiftCurve x₀ y₀).a₁ = W.a₁ := by
  simp [shiftCurve, WeierstrassCurve.variableChange_def]

@[simp] theorem shiftCurve_a₂ (x₀ y₀ : R) : (W.shiftCurve x₀ y₀).a₂ = W.a₂ + 3 * x₀ := by
  simp [shiftCurve, WeierstrassCurve.variableChange_def]

@[simp] theorem shiftCurve_a₃ (x₀ y₀ : R) :
    (W.shiftCurve x₀ y₀).a₃ = W.a₃ + x₀ * W.a₁ + 2 * y₀ := by
  simp [shiftCurve, WeierstrassCurve.variableChange_def]

@[simp] theorem shiftCurve_a₄ (x₀ y₀ : R) :
    (W.shiftCurve x₀ y₀).a₄ = W.a₄ + 2 * x₀ * W.a₂ - y₀ * W.a₁ + 3 * x₀ ^ 2 := by
  simp [shiftCurve, WeierstrassCurve.variableChange_def]

@[simp] theorem shiftCurve_a₆ (x₀ y₀ : R) : (W.shiftCurve x₀ y₀).a₆ = W.qResidual x₀ y₀ := by
  simp [shiftCurve, WeierstrassCurve.variableChange_def, qResidual]

private lemma eval_Ψ₃_eq (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [Ψ₃]
  simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, evalEval]

/-! ### Shift lemmas for the Vélu data -/

set_option maxHeartbeats 4000000 in theorem veluT_shift (x₀ y₀ : R) :
    W.veluT x₀ y₀ = (W.shiftCurve x₀ y₀).veluT 0 0 := by
  simp only [veluT, veluGx, veluGy, shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃,
    shiftCurve_a₄, shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluU_shift (x₀ y₀ : R) :
    W.veluU x₀ y₀ = (W.shiftCurve x₀ y₀).veluU 0 0 := by
  simp only [veluU, veluGy, shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃, shiftCurve_a₄,
    shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluGx_shift (x₀ y₀ : R) :
    W.veluGx x₀ y₀ = (W.shiftCurve x₀ y₀).veluGx 0 0 := by
  simp only [veluGx, shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃, shiftCurve_a₄,
    shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluGy_shift (x₀ y₀ : R) :
    W.veluGy x₀ y₀ = (W.shiftCurve x₀ y₀).veluGy 0 0 := by
  simp only [veluGy, shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃, shiftCurve_a₄,
    shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluW_shift (x₀ y₀ : R) :
    W.veluW x₀ y₀ = (W.shiftCurve x₀ y₀).veluW 0 0 + x₀ * W.veluT x₀ y₀ := by
  simp only [veluW, veluT, veluU, veluGx, veluGy, shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃,
    shiftCurve_a₄, shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluXNum_shift (x₀ y₀ u : R) :
    W.veluXNum x₀ y₀ (x₀ + u) = (W.shiftCurve x₀ y₀).veluXNum 0 0 u + x₀ * u ^ 2 := by
  simp only [veluXNum, veluT, veluU, veluGx, veluGy, shiftCurve_a₁, shiftCurve_a₂,
    shiftCurve_a₃, shiftCurve_a₄, shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluYNum_shift (x₀ y₀ u v : R) :
    W.veluYNum x₀ y₀ (x₀ + u) (y₀ + v)
      = (W.shiftCurve x₀ y₀).veluYNum 0 0 u v + y₀ * u ^ 3 := by
  simp only [veluYNum, veluT, veluU, veluGx, veluGy, shiftCurve_a₁, shiftCurve_a₂,
    shiftCurve_a₃, shiftCurve_a₄, shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem veluDeficitPsiCofactorReduced_shift (x₀ y₀ u : R) :
    W.veluDeficitPsiCofactorReduced x₀ (x₀ + u)
      = (W.shiftCurve x₀ y₀).veluDeficitPsiCofactorReduced 0 u := by
  simp only [veluDeficitPsiCofactorReduced, b₂, b₄, b₆, qResidual, shiftCurve_a₁, shiftCurve_a₂,
    shiftCurve_a₃, shiftCurve_a₄, shiftCurve_a₆]; ring

set_option maxHeartbeats 4000000 in theorem Psi₃_eval_shift (x₀ y₀ : R) :
    (W.Ψ₃).eval x₀ = ((W.shiftCurve x₀ y₀).Ψ₃).eval 0 := by
  rw [eval_Ψ₃_eq (W := W) x₀, eval_Ψ₃_eq (W := W.shiftCurve x₀ y₀) 0]
  simp only [b₂, b₄, b₆, b₈, qResidual, shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃,
    shiftCurve_a₄, shiftCurve_a₆]; ring

-- The cleared singleton deficit is invariant under translating the kernel point to
-- the origin.
set_option maxHeartbeats 4000000 in theorem clr_shift (x₀ y₀ u v : R) :
    W.clr x₀ y₀ (x₀ + u) (y₀ + v) = (W.shiftCurve x₀ y₀).clr 0 0 u v := by
  simp only [clr, veluXNum, veluYNum, veluT, veluU, veluW, veluGx, veluGy, b₂, qResidual,
    shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃, shiftCurve_a₄, shiftCurve_a₆]; ring

/-- `clr_shift` in the original coordinates. -/
theorem clr_shift_sub (x₀ y₀ x y : R) :
    W.clr x₀ y₀ x y = (W.shiftCurve x₀ y₀).clr 0 0 (x - x₀) (y - y₀) := by
  have hx : x₀ + (x - x₀) = x := by ring
  have hy : y₀ + (y - y₀) = y := by ring
  simpa only [hx, hy] using clr_shift (W := W) x₀ y₀ (x - x₀) (y - y₀)

/-- `veluDeficitPsiCofactorReduced_shift` in the original coordinates. -/
theorem veluDeficitPsiCofactorReduced_shift_sub (x₀ y₀ x : R) :
    W.veluDeficitPsiCofactorReduced x₀ x
      = (W.shiftCurve x₀ y₀).veluDeficitPsiCofactorReduced 0 (x - x₀) := by
  have hx : x₀ + (x - x₀) = x := by ring
  simpa only [hx] using veluDeficitPsiCofactorReduced_shift (W := W) x₀ y₀ (x - x₀)

/-- `(x - x₀, y - y₀)` lies on the translated curve whenever `(x, y)` and
`(x₀, y₀)` lie on `W`. -/
theorem shiftCurve_equation {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    (W.shiftCurve x₀ y₀).toAffine.Equation (x - x₀) (y - y₀) := by
  have hq : W.qResidual x₀ y₀ = 0 := by
    have hQc := hQ
    rw [Affine.equation_iff] at hQc
    rw [qResidual]
    linear_combination -hQc
  rw [Affine.equation_iff] at hP hQ
  rw [Affine.equation_iff]
  rw [shiftCurve_a₁, shiftCurve_a₂, shiftCurve_a₃, shiftCurve_a₄, shiftCurve_a₆, hq]
  linear_combination hP - hQ

-- The normalized singleton identity: with the kernel point at the origin the
-- certificate is the single square `(u³ - a₁a₃u - 2a₃² - 2a₄u)²`.
set_option maxHeartbeats 4000000 in
theorem velu_singleton_deficit_cleared_normalized {u v : R}
    (ha₆ : W.a₆ = 0) (hP : W.toAffine.Equation u v) :
    W.clr 0 0 u v = u ^ 2 * W.veluDeficitPsiCofactorReduced 0 u * (W.Ψ₃).eval 0 := by
  simp only [clr, sub_zero]
  rw [Affine.equation_iff] at hP
  rw [ha₆] at hP
  rw [eval_Ψ₃_eq]
  simp only [veluDeficitPsiCofactorReduced, b₂, b₄, b₆, b₈, veluXNum, veluYNum, veluT, veluU,
    veluW, veluGx, veluGy, ha₆]
  linear_combination (u ^ 3 - W.a₁ * W.a₃ * u - 2 * W.a₃ ^ 2 - 2 * W.a₄ * u) ^ 2 * hP

/-- The general singleton identity: the cleared map equation differs from the
quotient curve equation by `(x - x₀) ^ 2 * veluDeficitPsiCofactorReduced x₀ x` times
`(W.Ψ₃).eval x₀`.  This is
the pin's `velu_singleton_deficit_cleared_eq_psi` (private in the P2M solution). -/
theorem velu_singleton_deficit_cleared_eq_psi {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      - (W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6)
      = (x - x₀) ^ 2 * W.veluDeficitPsiCofactorReduced x₀ x * (W.Ψ₃).eval x₀ := by
  change W.clr x₀ y₀ x y
    = (x - x₀) ^ 2 * W.veluDeficitPsiCofactorReduced x₀ x * (W.Ψ₃).eval x₀
  have hq : W.qResidual x₀ y₀ = 0 := by
    have hQc := hQ
    rw [Affine.equation_iff] at hQc
    rw [qResidual]
    linear_combination -hQc
  have hq' : (W.shiftCurve x₀ y₀).a₆ = 0 := by rwa [shiftCurve_a₆]
  have hP' := W.shiftCurve_equation hP hQ
  have hnorm := velu_singleton_deficit_cleared_normalized (W := W.shiftCurve x₀ y₀) hq' hP'
  rw [clr_shift_sub, veluDeficitPsiCofactorReduced_shift_sub, Psi₃_eval_shift]
  exact hnorm

theorem velu_singleton_equation_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      = W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6 := by
  have h := W.velu_singleton_deficit_cleared_eq_psi hP hQ
  rw [hΨ, mul_zero] at h
  exact sub_eq_zero.mp h

section PointMapField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem velu_singleton_map_equation {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) (hx : x ≠ x₀) :
    (W.veluQuotient {(x₀, y₀)}).toAffine.Equation
      (W.veluX {(x₀, y₀)} x) (W.veluY {(x₀, y₀)} x y) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_singleton_equation_cleared hP hQ hΨ
  rw [Affine.equation_iff, W.veluX_singleton x₀ y₀ hx, W.veluY_singleton x₀ y₀ y hx]
  simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆, veluTSum, veluWSum, Finset.sum_singleton]
  field_simp
  linear_combination key

end PointMapField

end WeierstrassCurve
