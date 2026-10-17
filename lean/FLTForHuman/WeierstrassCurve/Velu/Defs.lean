/-
The Vélu vocabulary: the `n`-isogeny data attached to a finite Weierstrass set
`S`, transcribed verbatim from the pinned FLT definition modules

* `Definitions/Def_WeierstrassCurve_Velu.lean` (`veluGx`, `veluGy`, `veluT`,
  `veluU`, `veluW`, `veluTSum`, `veluWSum`, `veluQuotient`, `IsVeluSet`, …),
* `Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean` (`IsOddVeluSet`,
  `veluQuotient_singleton_negY`, `veluX`, `veluQuotient_Δ`),
* `Definitions/Def_WeierstrassCurve_VeluPointMap.lean` (`veluXNum`, `veluYNum`,
  `veluY`, `veluX_singleton`, `veluY_singleton`; the singleton identities
  `velu_singleton_equation_cleared` and `velu_singleton_map_equation` live in
  `Velu/Shift.lean`, which proves them by translating the kernel point to the
  origin),
* the P2M singleton-deficit block (`veluDeficitPsiCofactorReduced`, `private` in the
  pin's `P2M/Sol/` proofs): the reduced cofactor is homed here; the general identity
  `velu_singleton_deficit_cleared_eq_psi` that consumes it lives in `Velu/Shift.lean`,
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

section PointMap

def veluXNum (x₀ y₀ x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀

def veluYNum (x₀ y₀ x y : R) : R :=
  y * (x - x₀) ^ 3 - (W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
    + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
    + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀))

/-- The reduced `Ψ₃`-cofactor of the singleton deficit: the full cofactor is
`(x - x₀)^2` times this.  The pin keeps the cofactor, and the general identity
`velu_singleton_deficit_cleared_eq_psi`, `private` in its `P2M/Sol/` block; it is
re-homed here, upstream of `Velu/Shift.lean` and `Velu/Formula.lean`. -/
def veluDeficitPsiCofactorReduced (x₀ x : R) : R :=
  -6 * x ^ 3 + 18 * x₀ * x ^ 2 + (2 * W.b₂ * x₀ + 2 * W.b₄ - 6 * x₀ ^ 2) * x
    + (6 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 4 * W.b₄ * x₀ + 3 * W.b₆)

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
