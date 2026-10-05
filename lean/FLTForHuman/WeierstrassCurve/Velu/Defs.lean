/-
The Vélu vocabulary: the `n`-isogeny data attached to a finite Weierstrass set
`S`, transcribed verbatim from the pinned FLT definition modules

* `Definitions/Def_WeierstrassCurve_Velu.lean` (`veluGx`, `veluGy`, `veluT`,
  `veluU`, `veluW`, `veluTSum`, `veluWSum`, `veluQuotient`, `IsVeluSet`, …),
* `Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean` (`IsOddVeluSet`,
  `veluQuotient_singleton_negY`, `veluX`, `veluQuotient_Δ`),
* `Definitions/Def_WeierstrassCurve_VeluPointMap.lean` (`veluXNum`, `veluYNum`,
  `velu_singleton_equation_cleared`, `veluY`, `veluX_singleton`,
  `veluY_singleton`, `velu_singleton_map_equation`),
* `Definitions/Def_WeierstrassCurve_OddOrderSummingSet.lean` (`coordsOrZero`,
  `oddOrderSummingSet`, `mem_oddOrderSummingSet`).

The pin's `import Mathlib` is replaced by the two specific mathlib modules that
carry `Ψ₂Sq`/`Ψ₃` (`...DivisionPolynomial.Basic` and `...Affine.Formula`), as the
work order prescribes; the declarations themselves are unchanged. Only proof
bodies are adapted to mathlib `v4.34.0`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean>
-/
import FLTForHuman.WeierstrassCurve.Place.Dictionary
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Polynomial

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluGx (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

def veluGy (x y : R) : R := -(2 * y + W.a₁ * x + W.a₃)

def veluT (x y : R) : R := 2 * W.veluGx x y - W.a₁ * W.veluGy x y

def veluU (x y : R) : R := W.veluGy x y ^ 2

def veluW (x y : R) : R := W.veluU x y + x * W.veluT x y

lemma veluT_eq (x y : R) : W.veluT x y = 6 * x ^ 2 + W.b₂ * x + W.b₄ := by
  simp only [veluT, veluGx, veluGy, b₂, b₄]; ring

lemma veluU_eq_Ψ₂Sq_eval {x y : R} (h : W.toAffine.Equation x y) :
    W.veluU x y = W.Ψ₂Sq.eval x := by
  rw [Affine.equation_iff] at h
  simp only [veluU, veluGy, Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * h

lemma veluGy_negY (x y : R) : W.veluGy x (W.toAffine.negY x y) = -W.veluGy x y := by
  simp only [veluGy, Affine.negY]; ring

lemma veluT_negY (x y : R) : W.veluT x (W.toAffine.negY x y) = W.veluT x y := by
  simp only [veluT_eq]

lemma veluU_negY (x y : R) : W.veluU x (W.toAffine.negY x y) = W.veluU x y := by
  simp only [veluU, veluGy, Affine.negY]; ring

lemma veluW_negY (x y : R) : W.veluW x (W.toAffine.negY x y) = W.veluW x y := by
  simp only [veluW, veluU_negY, veluT_negY]

lemma veluGy_eq_zero_of_negY_eq {x y : R} (h : W.toAffine.negY x y = y) :
    W.veluGy x y = 0 := by
  have : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have := h
    simp only [Affine.negY] at this
    linear_combination -this
  simp [veluGy, this]

variable (S : Finset (R × R))

def veluTSum : R := ∑ P ∈ S, W.veluT P.1 P.2

def veluWSum : R := ∑ P ∈ S, W.veluW P.1 P.2

@[simp] lemma veluTSum_empty : W.veluTSum ∅ = 0 := by simp [veluTSum]

@[simp] lemma veluWSum_empty : W.veluWSum ∅ = 0 := by simp [veluWSum]

def veluQuotient : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluTSum S
  a₆ := W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S

@[simp] lemma veluQuotient_a₁ : (W.veluQuotient S).a₁ = W.a₁ := rfl
@[simp] lemma veluQuotient_a₂ : (W.veluQuotient S).a₂ = W.a₂ := rfl
@[simp] lemma veluQuotient_a₃ : (W.veluQuotient S).a₃ = W.a₃ := rfl
lemma veluQuotient_a₄ : (W.veluQuotient S).a₄ = W.a₄ - 5 * W.veluTSum S := rfl
lemma veluQuotient_a₆ :
    (W.veluQuotient S).a₆ = W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S := rfl

@[simp] lemma veluQuotient_empty : W.veluQuotient ∅ = W := by
  ext <;> simp [veluQuotient]

lemma veluQuotient_b₂ : (W.veluQuotient S).b₂ = W.b₂ := by
  simp [b₂]

lemma veluQuotient_b₄ : (W.veluQuotient S).b₄ = W.b₄ - 10 * W.veluTSum S := by
  simp only [b₄, veluQuotient_a₃, veluQuotient_a₁, veluQuotient_a₄]; ring

lemma veluQuotient_b₆ :
    (W.veluQuotient S).b₆ = W.b₆ - 4 * W.b₂ * W.veluTSum S - 28 * W.veluWSum S := by
  simp only [b₆, b₂, veluQuotient_a₃, veluQuotient_a₆]; ring

lemma veluQuotient_b₈ :
    (W.veluQuotient S).b₈ = W.b₈ + (5 * W.b₄ - W.b₂ ^ 2) * W.veluTSum S
      - 7 * W.b₂ * W.veluWSum S - 25 * W.veluTSum S ^ 2 := by
  simp only [b₈, b₂, b₄, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆]
  ring

structure IsVeluSet : Prop where
  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2

lemma isVeluSet_empty : W.IsVeluSet ∅ := ⟨by simp⟩

structure IsOddVeluSet (S : Finset (R × R)) : Prop where

  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2

  gy_ne_zero : ∀ P ∈ S, W.veluGy P.1 P.2 ≠ 0

  x_injOn : ∀ P ∈ S, ∀ P' ∈ S, P.1 = P'.1 → P = P'

lemma IsOddVeluSet.isVeluSet {S : Finset (R × R)} (h : W.IsOddVeluSet S) : W.IsVeluSet S :=
  ⟨h.equation⟩

lemma isOddVeluSet_empty : W.IsOddVeluSet ∅ where
  equation := by simp
  gy_ne_zero := by simp
  x_injOn := by simp

lemma isOddVeluSet_singleton {x y : R} (h : W.toAffine.Equation x y)
    (h2 : W.veluGy x y ≠ 0) : W.IsOddVeluSet {(x, y)} where
  equation := by simpa using h
  gy_ne_zero := by simpa using h2
  x_injOn := by simp

lemma veluQuotient_singleton_negY (x y : R) :
    W.veluQuotient {(x, W.toAffine.negY x y)} = W.veluQuotient {(x, y)} := by
  have ht : W.veluTSum {(x, W.toAffine.negY x y)} = W.veluTSum {(x, y)} := by
    simp only [veluTSum, Finset.sum_singleton]
    exact W.veluT_negY x y
  have hw : W.veluWSum {(x, W.toAffine.negY x y)} = W.veluWSum {(x, y)} := by
    simp only [veluWSum, Finset.sum_singleton]
    exact W.veluW_negY x y
  ext <;> simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆, ht, hw]

section QuotientMap

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def veluX (S : Finset (F × F)) (x : F) : F :=
  x + ∑ Q ∈ S, (W.veluT Q.1 Q.2 / (x - Q.1) + W.veluU Q.1 Q.2 / (x - Q.1) ^ 2)

@[simp] lemma veluX_empty (x : F) : W.veluX ∅ x = x := by simp [veluX]

lemma veluX_def_of_ne (S : Finset (F × F)) {x : F} (hx : ∀ Q ∈ S, x ≠ Q.1) :
    W.veluX S x = x + ∑ Q ∈ S, (W.veluT Q.1 Q.2 * (x - Q.1) + W.veluU Q.1 Q.2)
      / (x - Q.1) ^ 2 := by
  unfold veluX
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have h0 : x - Q.1 ≠ 0 := sub_ne_zero.mpr (hx Q hQ)
  field_simp

end QuotientMap

lemma veluQuotient_Δ (S : Finset (R × R)) :
    (W.veluQuotient S).Δ = W.Δ +
      (W.b₂ ^ 4 * W.veluTSum S + 7 * W.b₂ ^ 3 * W.veluWSum S
        - 41 * W.b₂ ^ 2 * W.b₄ * W.veluTSum S - 47 * W.b₂ ^ 2 * W.veluTSum S ^ 2
        - 252 * W.b₂ * W.b₄ * W.veluWSum S + 126 * W.b₂ * W.b₆ * W.veluTSum S
        - 3528 * W.b₂ * W.veluTSum S * W.veluWSum S + 240 * W.b₄ ^ 2 * W.veluTSum S
        - 2400 * W.b₄ * W.veluTSum S ^ 2 + 1512 * W.b₆ * W.veluWSum S
        + 8000 * W.veluTSum S ^ 3 - 21168 * W.veluWSum S ^ 2) := by
  simp only [Δ, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆, veluQuotient_b₈]
  ring

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval_ofNat, evalEval])

section PointMap

private lemma eval_Ψ₃_eq (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [Ψ₃]; eval_simp

def veluXNum (x₀ y₀ x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀

def veluYNum (x₀ y₀ x y : R) : R :=
  y * (x - x₀) ^ 3 - (W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
    + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
    + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀))

theorem velu_singleton_equation_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      = W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6 := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq] at hΨ
  simp only [b₂, b₄, b₆, b₈] at hΨ
  simp only [veluXNum, veluYNum, veluT, veluU, veluW, veluGx, veluGy, b₂]
  linear_combination
    (W.a₁^4*x^2*x₀^2 + 2*W.a₁^4*x*x₀^3 + W.a₁^4*x₀^4 + 2*W.a₁^3*W.a₃*x^2*x₀ + 8*W.a₁^3*W.a₃*x*x₀^2 + 6*W.a₁^3*W.a₃*x₀^3 + 16*W.a₁^3*x*x₀^2*y₀ + 16*W.a₁^3*x₀^3*y₀ + 8*W.a₁^2*W.a₂*x^2*x₀^2 - 8*W.a₁^2*W.a₂*x₀^4 + W.a₁^2*W.a₃^2*x^2 + 10*W.a₁^2*W.a₃^2*x*x₀ + 13*W.a₁^2*W.a₃^2*x₀^2 + 32*W.a₁^2*W.a₃*x*x₀*y₀ + 64*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^2*x₀ - 4*W.a₁^2*W.a₄*x₀^3 - 2*W.a₁^2*x^4*x₀ + 4*W.a₁^2*x^3*x₀^2 + 12*W.a₁^2*x^2*x₀^3 - 4*W.a₁^2*x*x₀^4 + 16*W.a₁^2*x*x₀*y₀^2 - 10*W.a₁^2*x₀^5 + 80*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^2*x₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2 - 24*W.a₁*W.a₂*W.a₃*x₀^3 + 64*W.a₁*W.a₂*x*x₀^2*y₀ - 64*W.a₁*W.a₂*x₀^3*y₀ + 4*W.a₁*W.a₃^3*x + 12*W.a₁*W.a₃^3*x₀ + 16*W.a₁*W.a₃^2*x*y₀ + 80*W.a₁*W.a₃^2*x₀*y₀ + 4*W.a₁*W.a₃*W.a₄*x^2 + 8*W.a₁*W.a₃*W.a₄*x*x₀ - 12*W.a₁*W.a₃*W.a₄*x₀^2 - 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^2*x₀^2 + 8*W.a₁*W.a₃*x*x₀^3 + 16*W.a₁*W.a₃*x*y₀^2 - 30*W.a₁*W.a₃*x₀^4 + 176*W.a₁*W.a₃*x₀*y₀^2 + 32*W.a₁*W.a₄*x*x₀*y₀ - 32*W.a₁*W.a₄*x₀^2*y₀ - 16*W.a₁*x^3*x₀*y₀ + 48*W.a₁*x^2*x₀^2*y₀ + 48*W.a₁*x*x₀^3*y₀ - 80*W.a₁*x₀^4*y₀ + 128*W.a₁*x₀*y₀^3 + 16*W.a₂^2*x^2*x₀^2 - 32*W.a₂^2*x*x₀^3 + 16*W.a₂^2*x₀^4 + 16*W.a₂*W.a₃^2*x*x₀ - 16*W.a₂*W.a₃^2*x₀^2 + 64*W.a₂*W.a₃*x*x₀*y₀ - 64*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^2*x₀ - 32*W.a₂*W.a₄*x*x₀^2 + 16*W.a₂*W.a₄*x₀^3 - 8*W.a₂*x^4*x₀ + 32*W.a₂*x^3*x₀^2 - 64*W.a₂*x*x₀^4 + 64*W.a₂*x*x₀*y₀^2 + 40*W.a₂*x₀^5 - 64*W.a₂*x₀^2*y₀^2 + 4*W.a₃^4 + 32*W.a₃^3*y₀ + 8*W.a₃^2*W.a₄*x - 8*W.a₃^2*W.a₄*x₀ - 4*W.a₃^2*x^3 + 12*W.a₃^2*x^2*x₀ + 12*W.a₃^2*x*x₀^2 - 20*W.a₃^2*x₀^3 + 96*W.a₃^2*y₀^2 + 32*W.a₃*W.a₄*x*y₀ - 32*W.a₃*W.a₄*x₀*y₀ - 16*W.a₃*x^3*y₀ + 48*W.a₃*x^2*x₀*y₀ + 48*W.a₃*x*x₀^2*y₀ - 80*W.a₃*x₀^3*y₀ + 128*W.a₃*y₀^3 + 4*W.a₄^2*x^2 - 8*W.a₄^2*x*x₀ + 4*W.a₄^2*x₀^2 - 4*W.a₄*x^4 + 16*W.a₄*x^3*x₀ - 32*W.a₄*x*x₀^3 + 32*W.a₄*x*y₀^2 + 20*W.a₄*x₀^4 - 32*W.a₄*x₀*y₀^2 + x^6 - 6*x^5*x₀ + 3*x^4*x₀^2 + 28*x^3*x₀^3 - 16*x^3*y₀^2 - 21*x^2*x₀^4 + 48*x^2*x₀*y₀^2 - 30*x*x₀^5 + 48*x*x₀^2*y₀^2 + 25*x₀^6 - 80*x₀^3*y₀^2 + 64*y₀^4) * hP
    + (2*W.a₁^4*x^3*x₀ - 4*W.a₁^4*x^2*x₀^2 - 2*W.a₁^4*x*x₀^3 + 2*W.a₁^3*W.a₃*x^3 - 2*W.a₁^3*W.a₃*x^2*x₀ - 14*W.a₁^3*W.a₃*x*x₀^2 - 2*W.a₁^3*W.a₃*x₀^3 + 12*W.a₁^3*x^2*x₀*y₀ - 40*W.a₁^3*x*x₀^2*y₀ - 4*W.a₁^3*x₀^3*y₀ + 16*W.a₁^2*W.a₂*x^3*x₀ - 44*W.a₁^2*W.a₂*x^2*x₀^2 + 24*W.a₁^2*W.a₂*x*x₀^3 + 4*W.a₁^2*W.a₂*x₀^4 + 2*W.a₁^2*W.a₃^2*x^2 - 16*W.a₁^2*W.a₃^2*x*x₀ - 10*W.a₁^2*W.a₃^2*x₀^2 + 12*W.a₁^2*W.a₃*x^2*y₀ - 56*W.a₁^2*W.a₃*x*x₀*y₀ - 52*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^3 - 16*W.a₁^2*W.a₄*x^2*x₀ + 12*W.a₁^2*W.a₄*x*x₀^2 + 12*W.a₁^2*W.a₆*x^2 - 24*W.a₁^2*W.a₆*x*x₀ + 12*W.a₁^2*W.a₆*x₀^2 - 6*W.a₁^2*x^5 + 32*W.a₁^2*x^4*x₀ - 28*W.a₁^2*x^3*x₀^2 - 12*W.a₁^2*x^2*x₀^3 + 12*W.a₁^2*x^2*y₀^2 - 14*W.a₁^2*x*x₀^4 - 40*W.a₁^2*x*x₀*y₀^2 + 28*W.a₁^2*x₀^5 - 68*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^3 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀ - 40*W.a₁*W.a₂*W.a₃*x*x₀^2 + 40*W.a₁*W.a₂*W.a₃*x₀^3 + 48*W.a₁*W.a₂*x^2*x₀*y₀ - 160*W.a₁*W.a₂*x*x₀^2*y₀ + 112*W.a₁*W.a₂*x₀^3*y₀ - 4*W.a₁*W.a₃^3*x - 12*W.a₁*W.a₃^3*x₀ - 16*W.a₁*W.a₃^2*x*y₀ - 80*W.a₁*W.a₃^2*x₀*y₀ - 16*W.a₁*W.a₃*W.a₄*x^2 + 16*W.a₁*W.a₃*W.a₄*x*x₀ + 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^3*x₀ + 12*W.a₁*W.a₃*x^2*x₀^2 - 152*W.a₁*W.a₃*x*x₀^3 - 16*W.a₁*W.a₃*x*y₀^2 + 114*W.a₁*W.a₃*x₀^4 - 176*W.a₁*W.a₃*x₀*y₀^2 - 32*W.a₁*W.a₄*x*x₀*y₀ + 32*W.a₁*W.a₄*x₀^2*y₀ + 16*W.a₁*x^3*x₀*y₀ + 96*W.a₁*x^2*x₀^2*y₀ - 336*W.a₁*x*x₀^3*y₀ + 224*W.a₁*x₀^4*y₀ - 128*W.a₁*x₀*y₀^3 + 32*W.a₂^2*x^3*x₀ - 112*W.a₂^2*x^2*x₀^2 + 128*W.a₂^2*x*x₀^3 - 48*W.a₂^2*x₀^4 + 24*W.a₂*W.a₃^2*x^2 - 64*W.a₂*W.a₃^2*x*x₀ + 40*W.a₂*W.a₃^2*x₀^2 + 48*W.a₂*W.a₃*x^2*y₀ - 160*W.a₂*W.a₃*x*x₀*y₀ + 112*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^3 - 64*W.a₂*W.a₄*x^2*x₀ + 80*W.a₂*W.a₄*x*x₀^2 - 32*W.a₂*W.a₄*x₀^3 + 48*W.a₂*W.a₆*x^2 - 96*W.a₂*W.a₆*x*x₀ + 48*W.a₂*W.a₆*x₀^2 - 24*W.a₂*x^5 + 128*W.a₂*x^4*x₀ - 128*W.a₂*x^3*x₀^2 - 144*W.a₂*x^2*x₀^3 + 48*W.a₂*x^2*y₀^2 + 280*W.a₂*x*x₀^4 - 160*W.a₂*x*x₀*y₀^2 - 112*W.a₂*x₀^5 + 112*W.a₂*x₀^2*y₀^2 - 4*W.a₃^4 - 32*W.a₃^3*y₀ - 8*W.a₃^2*W.a₄*x + 8*W.a₃^2*W.a₄*x₀ + 4*W.a₃^2*x^3 + 60*W.a₃^2*x^2*x₀ - 156*W.a₃^2*x*x₀^2 + 92*W.a₃^2*x₀^3 - 96*W.a₃^2*y₀^2 - 32*W.a₃*W.a₄*x*y₀ + 32*W.a₃*W.a₄*x₀*y₀ + 16*W.a₃*x^3*y₀ + 96*W.a₃*x^2*x₀*y₀ - 336*W.a₃*x*x₀^2*y₀ + 224*W.a₃*x₀^3*y₀ - 128*W.a₃*y₀^3 - 16*W.a₄^2*x^2 + 32*W.a₄^2*x*x₀ - 16*W.a₄^2*x₀^2 + 4*W.a₄*x^4 + 32*W.a₄*x^3*x₀ - 72*W.a₄*x^2*x₀^2 + 32*W.a₄*x*x₀^3 - 32*W.a₄*x*y₀^2 + 4*W.a₄*x₀^4 + 32*W.a₄*x₀*y₀^2 + 144*W.a₆*x^2*x₀ - 288*W.a₆*x*x₀^2 + 144*W.a₆*x₀^3 - 72*x^5*x₀ + 372*x^4*x₀^2 - 624*x^3*x₀^3 + 16*x^3*y₀^2 + 360*x^2*x₀^4 + 96*x^2*x₀*y₀^2 + 24*x*x₀^5 - 336*x*x₀^2*y₀^2 - 60*x₀^6 + 224*x₀^3*y₀^2 - 64*y₀^4) * hQ
    + (2*W.a₁^2*x^3*x₀ - 3*W.a₁^2*x^2*x₀^2 + W.a₁^2*x₀^4 + 2*W.a₁*W.a₃*x^3 - 6*W.a₁*W.a₃*x*x₀^2 + 4*W.a₁*W.a₃*x₀^3 + 8*W.a₂*x^3*x₀ - 12*W.a₂*x^2*x₀^2 + 4*W.a₂*x₀^4 + 3*W.a₃^2*x^2 - 6*W.a₃^2*x*x₀ + 3*W.a₃^2*x₀^2 + 4*W.a₄*x^3 - 12*W.a₄*x*x₀^2 + 8*W.a₄*x₀^3 + 12*W.a₆*x^2 - 24*W.a₆*x*x₀ + 12*W.a₆*x₀^2 - 6*x^5 + 30*x^4*x₀ - 48*x^3*x₀^2 + 36*x^2*x₀^3 - 18*x*x₀^4 + 6*x₀^5) * hΨ

end PointMap

section PointMapField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def veluY (S : Finset (F × F)) (x y : F) : F :=
  y - ∑ Q ∈ S, (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
    + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) / (x - Q.1) ^ 2
    + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2)

@[simp] lemma veluY_empty (x y : F) : W.veluY ∅ x y = y := by simp [veluY]

lemma veluX_singleton (x₀ y₀ : F) {x : F} (hx : x ≠ x₀) :
    W.veluX {(x₀, y₀)} x = W.veluXNum x₀ y₀ x / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [veluX, Finset.sum_singleton, veluXNum]
  field_simp
  ring

lemma veluY_singleton (x₀ y₀ : F) {x : F} (y : F) (hx : x ≠ x₀) :
    W.veluY {(x₀, y₀)} x y = W.veluYNum x₀ y₀ x y / (x - x₀) ^ 3 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [veluY, Finset.sum_singleton, veluYNum]
  field_simp

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

namespace WeierstrassCurve

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : Affine R}

def coordsOrZero : W.Point → R × R
  | .zero => (0, 0)
  | .some x y _ => (x, y)

@[simp] lemma coordsOrZero_zero : ((.zero : W.Point)).coordsOrZero = (0, 0) := rfl

@[simp] lemma coordsOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).coordsOrZero = (x, y) := rfl

end Affine.Point

section SummingSet

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) : Finset (F × F) :=
  (Finset.Icc 1 n).image fun k => (k • Q).coordsOrZero

lemma mem_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ} {P : F × F} :
    P ∈ W.oddOrderSummingSet Q n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ (k • Q).coordsOrZero = P := by
  simp only [oddOrderSummingSet, Finset.mem_image, Finset.mem_Icc]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, h3⟩ => ⟨k, h1, h2, h3⟩, fun ⟨k, h1, h2, h3⟩ => ⟨k, ⟨h1, h2⟩, h3⟩⟩

end SummingSet

end WeierstrassCurve
