/-
The explicit-Vélu formulas and the deficit-expansion algebra: base change of the
Vélu data (`map_veluGx` … `map_veluQuotient`), the corrected quotient-map
coordinates (`veluXCorr`, `veluYCorr`, `veluX_sub_self_mul_r`), the deficit
`veluDeficit` with its equation/constancy predicates, the singleton orbit sums,
the Laurent/linear/bracket split (`veluDeficitLinearTerm`, `veluDeficitBracket`,
`veluDeficit_eq_laurentSum_add_bracket`), the `Ψ₃`-cofactor
(`veluDeficitPsiCofactor` and its reduced form), and the lin/quad/cross-quad
decomposition.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` map file
`P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
(the B/C/D clusters); the proof bodies are taken from the corresponding res file
`P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean`,
adapted to mathlib `v4.34.0`.

`exists_some_of_ne_zero` is public here: the pin's `IsOddVeluSet`-block copy was
transcribed `private` by SET-1 and duplicated `public` in `Velu/OddOrder.lean`;
the H5r refactor round folded the two copies back to this one.

Deferred (not in this module, because their proofs consume the function-field /
`kwVelu` engine that SET-1 does not bring): `veluDeficitBracket_genericPoint_mem_of_not_isFinitePlace`,
`coordsOrZero_ratPointMap` and the four headline theorems.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false

noncomputable section

open Polynomial Finset

namespace WeierstrassCurve

open WeierstrassCurve.Affine

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : Affine R}

/-- The `x`-coordinate of a point, `0` at the origin. The pin declares this
`private` and re-exports it by name-mangling (`p2m_export`); the port promotes it
publicly so the odd-order layer (`Velu/OddOrder.lean`, whose
`kw_veluX_xOrZero_add_gen_odd` statement names `(P + Q).xOrZero`) can use it. -/
def xOrZero : W.Point → R
  | .zero => 0
  | .some x _ _ => x

@[scoped simp] lemma xOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).xOrZero = x := rfl

lemma coordsOrZero_fst (P : W.Point) : P.coordsOrZero.1 = P.xOrZero := by
  cases P <;> rfl

end Affine.Point

section BaseChange

variable {R : Type*} {A : Type*} [CommRing R] [CommRing A] (W : WeierstrassCurve R) (f : R →+* A)

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, _root_.map_neg, map_add, map_sub, map_mul, map_pow])

@[scoped simp] lemma map_veluGx (x y : R) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, map_a₁, map_a₂, map_a₄]
  map_simp

@[scoped simp] lemma map_veluGy (x y : R) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [veluGy, map_a₁, map_a₃]
  map_simp

@[scoped simp] lemma map_veluT (x y : R) :
    (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp only [veluT_eq, map_b₂, map_b₄]
  map_simp

@[scoped simp] lemma map_veluU (x y : R) :
    (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp only [veluU, map_veluGy, map_pow]

@[scoped simp] lemma map_veluW (x y : R) :
    (W.map f).veluW (f x) (f y) = f (W.veluW x y) := by
  simp only [veluW, map_veluU, map_veluT, map_add, map_mul]

lemma map_veluTSum (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluTSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluTSum S) := by
  rw [veluTSum, veluTSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT]

lemma map_veluWSum (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluWSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluWSum S) := by
  rw [veluWSum, veluWSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluW]

lemma map_veluQuotient (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluQuotient (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = (W.veluQuotient S).map f := by
  ext
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp only [veluQuotient_a₄, map_a₄, map_veluTSum _ _ S hf]
    map_simp
  · simp only [veluQuotient_a₆, map_a₆, map_b₂, map_veluTSum _ _ S hf, map_veluWSum _ _ S hf]
    map_simp

end BaseChange

section NegY

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma veluY_summand_negY (x y : F) (Q : F × F) :
    W.veluU Q.1 Q.2 * (2 * W.toAffine.negY x y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
      + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + W.toAffine.negY x y - Q.2) / (x - Q.1) ^ 2
      + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2
    = W.a₁ * (W.veluT Q.1 Q.2 / (x - Q.1) + W.veluU Q.1 Q.2 / (x - Q.1) ^ 2)
      - (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
        + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) / (x - Q.1) ^ 2
        + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2) := by
  rcases eq_or_ne x Q.1 with h | h
  · simp [h, sub_self]
  · have hd : x - Q.1 ≠ 0 := sub_ne_zero.mpr h
    simp only [veluT, veluU, veluGx, veluGy, Affine.negY]
    field_simp
    ring

lemma veluY_negY (S : Finset (F × F)) (x y : F) :
    W.veluY S x (W.toAffine.negY x y)
      = (W.veluQuotient S).toAffine.negY (W.veluX S x) (W.veluY S x y) := by
  simp only [veluY, veluX]
  rw [Finset.sum_congr rfl fun Q _ => W.veluY_summand_negY x y Q,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Affine.negY, veluQuotient_a₁, veluQuotient_a₃]
  ring

end NegY

section Corrections

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluXCorr (x₀ y₀ r : F) : F :=
  W.veluT x₀ y₀ / (r - x₀) + W.veluU x₀ y₀ / (r - x₀) ^ 2

def veluYCorr (x₀ y₀ r s : F) : F :=
  -(W.veluU x₀ y₀ * (2 * s + W.a₁ * r + W.a₃) / (r - x₀) ^ 3
    + W.veluT x₀ y₀ * (W.a₁ * (r - x₀) + s - y₀) / (r - x₀) ^ 2
    + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (r - x₀) ^ 2)

theorem veluX_sub_self_eq_sum_veluXCorr (S : Finset (F × F)) (r : F) :
    W.veluX S r - r = ∑ Q ∈ S, W.veluXCorr Q.1 Q.2 r := by
  simp only [veluX, veluXCorr, add_sub_cancel_left]

theorem veluY_sub_self_eq_sum_veluYCorr (S : Finset (F × F)) (r s : F) :
    W.veluY S r s - s = ∑ Q ∈ S, W.veluYCorr Q.1 Q.2 r s := by
  unfold veluY veluYCorr
  rw [sub_sub_cancel_left, ← Finset.sum_neg_distrib]

theorem veluXCorr_mul_r (x₀ y₀ : F) {r : F} (hr : r ≠ x₀) :
    W.veluXCorr x₀ y₀ r * r
      = W.veluT x₀ y₀ + W.veluW x₀ y₀ / (r - x₀) + W.veluU x₀ y₀ * x₀ / (r - x₀) ^ 2 := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  simp only [veluXCorr, veluW]
  field_simp
  ring

theorem veluX_sub_self_mul_r (S : Finset (F × F)) {r : F} (hr : ∀ A ∈ S, r ≠ A.1) :
    (W.veluX S r - r) * r
      = W.veluTSum S
        + ∑ Q ∈ S, (W.veluW Q.1 Q.2 / (r - Q.1) + W.veluU Q.1 Q.2 * Q.1 / (r - Q.1) ^ 2) := by
  rw [W.veluX_sub_self_eq_sum_veluXCorr, Finset.sum_mul, veluTSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun Q hQ => by
    rw [W.veluXCorr_mul_r Q.1 Q.2 (hr Q hQ)]; ring

end Corrections

section Deficit

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficit (S : Finset (F × F)) (r s : F) : F :=
  (W.veluY S r s) ^ 2 + W.a₁ * (W.veluX S r) * (W.veluY S r s) + W.a₃ * (W.veluY S r s)
    - ((W.veluX S r) ^ 3 + W.a₂ * (W.veluX S r) ^ 2
        + (W.veluQuotient S).a₄ * (W.veluX S r) + (W.veluQuotient S).a₆)

theorem veluQuotient_equation_iff_veluDeficit_eq_zero (S : Finset (F × F)) (r s : F) :
    (W.veluQuotient S).toAffine.Equation (W.veluX S r) (W.veluY S r s)
      ↔ W.veluDeficit S r s = 0 := by
  rw [Affine.equation_iff, veluDeficit, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃,
    sub_eq_zero]

theorem veluDeficit_eq_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficit S r s
      = -(W.veluY S r s - s) * W.veluGy r s - (W.veluX S r - r) * W.veluGx r s
        + ((W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s)
            - (3 * r + W.a₂) * (W.veluX S r - r) ^ 2 - (W.veluX S r - r) ^ 3)
        + 5 * W.veluTSum S * W.veluX S r + W.b₂ * W.veluTSum S + 7 * W.veluWSum S := by
  rw [Affine.equation_iff] at hP
  simp only [veluDeficit, veluGx, veluGy, veluQuotient_a₄, veluQuotient_a₆]
  linear_combination hP

theorem veluDeficit_congr {S : Finset (F × F)} {r s r' s' : F}
    (hX : W.veluX S r = W.veluX S r') (hY : W.veluY S r s = W.veluY S r' s') :
    W.veluDeficit S r s = W.veluDeficit S r' s' := by
  unfold veluDeficit; rw [hX, hY]

end Deficit

section ConstancyCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitConstancyAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = 0

end ConstancyCarrier

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem velu_orbitSumX_singleton_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluXNum x₀ y₀ x
      = (x - 2 * x₀) * (x - x₀) ^ 2
        + ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
        + ((y - (-y₀ - W.a₁ * x₀ - W.a₃)) ^ 2
            + W.a₁ * (y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluXNum, veluT, veluU, veluGx, veluGy]
  linear_combination (-2 : R) * hP + 2 * hQ

theorem velu_orbitSumY_singleton_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluYNum x₀ y₀ x y
      = y * (x - x₀) ^ 3
        + (-(y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) - x * (x - x₀) ^ 2)
            - y * (x - x₀) ^ 3
            - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
            - W.a₃ * (x - x₀) ^ 3)
        + (-(y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (((y - (-y₀ - W.a₁ * x₀ - W.a₃)) ^ 2
              + W.a₁ * (y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) - x * (x - x₀) ^ 2)
            - y * (x - x₀) ^ 3
            - W.a₁ * ((y - (-y₀ - W.a₁ * x₀ - W.a₃)) ^ 2
              + W.a₁ * (y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
            - W.a₃ * (x - x₀) ^ 3)
        + (W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3 := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluYNum, veluT, veluU, veluGx, veluGy]
  linear_combination (2 * W.a₁ * x - W.a₁ * x₀ + W.a₃ + 2 * y) * hP
    + (-2 * W.a₁ * x + W.a₁ * x₀ - W.a₃ - 2 * y) * hQ

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluX_singleton_eq_orbitSum [DecidableEq F] {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) (hx : x ≠ x₀) :
    W.veluX {(x₀, y₀)} x
      = x + W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀)
          + W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y (W.toAffine.negY x₀ y₀))
          - 2 * x₀ := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_orbitSumX_singleton_cleared hP hQ
  rw [W.veluX_singleton x₀ y₀ hx]
  simp only [Affine.slope_of_X_ne hx, Affine.addX, Affine.negY]
  field_simp
  linear_combination key

theorem veluY_singleton_eq_orbitSum [DecidableEq F] {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) (hx : x ≠ x₀) :
    W.veluY {(x₀, y₀)} x y
      = y + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)
          + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y (W.toAffine.negY x₀ y₀))
          - y₀ - W.toAffine.negY x₀ y₀ := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_orbitSumY_singleton_cleared hP hQ
  rw [W.veluY_singleton x₀ y₀ y hx]
  simp only [Affine.slope_of_X_ne hx, Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  linear_combination key

end Field

section GeneralOrbitSum

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluY_eq_add_sum_singleton (S : Finset (F × F)) (x y : F) :
    W.veluY S x y = y + ∑ P ∈ S, (W.veluY {P} x y - y) := by
  simp only [veluY, Finset.sum_singleton, sub_sub_cancel_left, Finset.sum_neg_distrib]
  ring

theorem veluY_eq_orbitSum_fieldRed {S : Finset (F × F)} {x y : F} (hP : W.toAffine.Equation x y)
    (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2) (hx : ∀ A ∈ S, x ≠ A.1) :
    W.veluY S x y = y + ∑ A ∈ S,
      (W.toAffine.addY x A.1 y (W.toAffine.slope x A.1 y A.2)
        + W.toAffine.addY x A.1 y (W.toAffine.slope x A.1 y (W.toAffine.negY A.1 A.2))
        - A.2 - W.toAffine.negY A.1 A.2) := by
  rw [veluY_eq_add_sum_singleton]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have key := W.veluY_singleton_eq_orbitSum (x₀ := A.1) (y₀ := A.2) hP (hSeq A hA) (hx A hA)
  rw [show ({(A.1, A.2)} : Finset (F × F)) = {A} from by simp] at key
  linear_combination key

omit [DecidableEq F] in

theorem veluX_eq_add_sum_singleton (S : Finset (F × F)) (x : F) :
    W.veluX S x = x + ∑ P ∈ S, (W.veluX {P} x - x) := by
  simp only [veluX, Finset.sum_singleton, add_sub_cancel_left]

theorem veluX_eq_orbitSum {S : Finset (F × F)} {x y : F} (hP : W.toAffine.Equation x y)
    (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2) (hx : ∀ A ∈ S, x ≠ A.1) :
    W.veluX S x = x + ∑ A ∈ S,
      (W.toAffine.addX x A.1 (W.toAffine.slope x A.1 y A.2)
        + W.toAffine.addX x A.1 (W.toAffine.slope x A.1 y (W.toAffine.negY A.1 A.2))
        - 2 * A.1) := by
  rw [veluX_eq_add_sum_singleton]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have key := W.veluX_singleton_eq_orbitSum (x₀ := A.1) (y₀ := A.2) hP (hSeq A hA) (hx A hA)
  rw [show ({(A.1, A.2)} : Finset (F × F)) = {A} from by simp] at key
  linear_combination key

end GeneralOrbitSum

section FullPeriod

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {p : ℕ}

theorem not_mem_zmultiples_add {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) {K : W.toAffine.Point}
    (hK : K ∈ AddSubgroup.zmultiples Q) : P + K ∉ AddSubgroup.zmultiples Q := fun hmem =>
  hPmem (by simpa using AddSubgroup.sub_mem _ hmem hK)

theorem add_ne_zero_of_not_mem_zmultiples {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) {K : W.toAffine.Point}
    (hK : K ∈ AddSubgroup.zmultiples Q) : P + K ≠ 0 := fun h =>
  hPmem (by rw [add_eq_zero_iff_eq_neg] at h; exact h ▸ AddSubgroup.neg_mem _ hK)

omit [DecidableEq F] in
lemma exists_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ (x y : F) (h : W.toAffine.Nonsingular x y), P = Point.some x y h ∧
      P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

theorem xOrZero_ne_of_not_mem_zmultiples {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) (hP0 : P ≠ 0) {x y : F}
    {h : W.toAffine.Nonsingular x y} (hkQ : Point.some x y h ∈ AddSubgroup.zmultiples Q) :
    P.xOrZero ≠ x := by
  obtain ⟨a, b, hns, rfl, -⟩ := exists_some_of_ne_zero (F := F) (W := W) hP0
  intro hx
  rcases (Point.X_eq_iff (h₁ := hns) (h₂ := h)).mp hx with hPP | hPP
  · exact hPmem (hPP ▸ hkQ)
  · exact hPmem (hPP ▸ AddSubgroup.neg_mem _ hkQ)

theorem sum_range_addOrderOf_shift_invariant {G : Type*} [AddCommGroup G] {Q : G}
    {p : ℕ} (hord : addOrderOf Q = p) {M : Type*} [AddCommMonoid M] (f : G → M) (R : G) :
    ∑ j ∈ Finset.range p, f (R + Q + j • Q) = ∑ j ∈ Finset.range p, f (R + j • Q) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp
  have hpQ : p • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q

  have hLHS : ∑ j ∈ Finset.range p, f (R + Q + j • Q)
      = ∑ k ∈ Finset.Ico 1 (p + 1), f (R + k • Q) := by
    rw [show Finset.Ico 1 (p + 1) = (Finset.range p).map ⟨(· + 1), add_left_injective 1⟩ from by
      ext k; simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk]
      constructor
      · exact fun ⟨h1, h2⟩ => ⟨k - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega]
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Function.Embedding.coeFn_mk]; rw [succ_nsmul', ← add_assoc]

  have hRHS : ∑ j ∈ Finset.range p, f (R + j • Q)
      = f (R + 0 • Q) + ∑ k ∈ Finset.Ico 1 p, f (R + k • Q) := by
    rw [show Finset.range p = insert 0 (Finset.Ico 1 p) from by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega]
    rw [Finset.sum_insert (by simp)]
  rw [hLHS, hRHS]

  have hIco_split : Finset.Ico 1 (p + 1) = insert p (Finset.Ico 1 p) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hIco_split, Finset.sum_insert (by simp), hpQ, zero_nsmul]

end FullPeriod

section PsiEval

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

lemma eval_Ψ₃_eq_b' (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp only [Ψ₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]

end PsiEval

section LinearTerm

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitLinearTerm (x₀ y₀ r s : F) : F :=
  -(W.veluY {(x₀, y₀)} r s - s) * W.veluGy r s
    - (W.veluX {(x₀, y₀)} r - r) * W.veluGx r s
    + 5 * W.veluT x₀ y₀ * r + W.b₂ * W.veluT x₀ y₀ + 7 * W.veluW x₀ y₀

end LinearTerm

section ClearedIdentity

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem veluDeficitLinearTerm_mul_cube_eq {x₀ y₀ r s : R}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) :
    -(W.veluU x₀ y₀ * W.veluGy r s
        - W.veluT x₀ y₀ * (W.a₁ * (r - x₀) + s - y₀) * (r - x₀)
        - (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (r - x₀)) * W.veluGy r s
      - (W.veluT x₀ y₀ * (r - x₀) + W.veluU x₀ y₀) * W.veluGx r s * (r - x₀)
      + (5 * W.veluT x₀ y₀ * r + W.b₂ * W.veluT x₀ y₀ + 7 * W.veluW x₀ y₀) * (r - x₀) ^ 3
      = -(W.veluU x₀ y₀) ^ 2 - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ * (r - x₀)
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) * (r - x₀) ^ 2 := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq_b']
  simp only [veluT, veluU, veluW, veluGx, veluGy, b₂, b₄, b₆, b₈]
  linear_combination
    (-2*W.a₁^2*r*x₀ - 2*W.a₁^2*x₀^2 - 2*W.a₁*W.a₃*r - 6*W.a₁*W.a₃*x₀ - 16*W.a₁*x₀*y₀
        - 8*W.a₂*r*x₀ + 8*W.a₂*x₀^2 - 4*W.a₃^2 - 16*W.a₃*y₀ - 4*W.a₄*r + 4*W.a₄*x₀
        - 12*r*x₀^2 + 12*x₀^3 - 16*y₀^2) * hP
    + (-6*W.a₁^2*r^2 + 14*W.a₁^2*r*x₀ - 4*W.a₁^2*x₀^2 + 2*W.a₁*W.a₃*r + 6*W.a₁*W.a₃*x₀
        + 16*W.a₁*x₀*y₀ - 24*W.a₂*r^2 + 56*W.a₂*r*x₀ - 32*W.a₂*x₀^2 + 4*W.a₃^2 + 16*W.a₃*y₀
        + 4*W.a₄*r - 4*W.a₄*x₀ - 72*r^2*x₀ + 156*r*x₀^2 - 84*x₀^3 + 16*y₀^2) * hQ

end ClearedIdentity

section FieldLaurent

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma veluDeficitLinearTerm_mul_cube {x₀ y₀ r s : F} (hr : r ≠ x₀) :
    W.veluDeficitLinearTerm x₀ y₀ r s * (r - x₀) ^ 3
      = -(W.veluU x₀ y₀ * W.veluGy r s
          - W.veluT x₀ y₀ * (W.a₁ * (r - x₀) + s - y₀) * (r - x₀)
          - (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (r - x₀)) * W.veluGy r s
        - (W.veluT x₀ y₀ * (r - x₀) + W.veluU x₀ y₀) * W.veluGx r s * (r - x₀)
        + (5 * W.veluT x₀ y₀ * r + W.b₂ * W.veluT x₀ y₀ + 7 * W.veluW x₀ y₀) * (r - x₀) ^ 3 := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  unfold veluDeficitLinearTerm
  simp only [veluX, veluY, veluGy, Finset.sum_singleton]
  field_simp
  ring

theorem veluDeficitLinearTerm_eq {x₀ y₀ r s : F}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) (hr : r ≠ x₀) :
    W.veluDeficitLinearTerm x₀ y₀ r s
      = -(W.veluU x₀ y₀) ^ 2 / (r - x₀) ^ 3
        - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ / (r - x₀) ^ 2
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) / (r - x₀) := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  have hd3 : (r - x₀) ^ 3 ≠ 0 := pow_ne_zero 3 hd
  have hLHS := W.veluDeficitLinearTerm_mul_cube (x₀ := x₀) (y₀ := y₀) (s := s) hr
  have key := W.veluDeficitLinearTerm_mul_cube_eq hP hQ
  have hRHS : (-(W.veluU x₀ y₀) ^ 2 / (r - x₀) ^ 3
        - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ / (r - x₀) ^ 2
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) / (r - x₀)) * (r - x₀) ^ 3
      = -(W.veluU x₀ y₀) ^ 2 - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ * (r - x₀)
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) * (r - x₀) ^ 2 := by
    have hd2 : (r - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hd3,
      show (r - x₀) ^ 3 = (r - x₀) ^ 2 * (r - x₀) from by ring, ← mul_assoc,
      div_mul_cancel₀ _ hd2, show (r - x₀) ^ 2 * (r - x₀) = (r - x₀) * (r - x₀) ^ 2 from by ring,
      ← mul_assoc, div_mul_cancel₀ _ hd]
  exact mul_right_cancel₀ hd3 (by rw [hLHS, key, ← hRHS])

end FieldLaurent

section SumDecomposition

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_linearPart_eq_sum (S : Finset (F × F)) (r s : F) :
    -(W.veluY S r s - s) * W.veluGy r s - (W.veluX S r - r) * W.veluGx r s
        + 5 * W.veluTSum S * r + W.b₂ * W.veluTSum S + 7 * W.veluWSum S
      = ∑ Q ∈ S, W.veluDeficitLinearTerm Q.1 Q.2 r s := by
  simp only [veluDeficitLinearTerm, veluX, veluY, veluTSum, veluWSum, Finset.sum_singleton,
    add_sub_cancel_left, sub_sub_cancel_left, neg_neg, Finset.sum_mul, Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun Q _ => by ring

end SumDecomposition

section FullExpansion

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitBracket (S : Finset (F × F)) (r s : F) : F :=
  ((W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s)
      - (3 * r + W.a₂) * (W.veluX S r - r) ^ 2 - (W.veluX S r - r) ^ 3)
    + 5 * W.veluTSum S * (W.veluX S r - r)

theorem veluDeficit_eq_laurentSum_add_bracket {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (hr : ∀ A ∈ S, r ≠ A.1) :
    W.veluDeficit S r s
      = (∑ Q ∈ S, (-(W.veluU Q.1 Q.2) ^ 2 / (r - Q.1) ^ 3
          - 3 * W.veluT Q.1 Q.2 * W.veluU Q.1 Q.2 / (r - Q.1) ^ 2
          - (3 * (W.veluT Q.1 Q.2) ^ 2 + 6 * (W.Ψ₃).eval Q.1) / (r - Q.1)))
        + W.veluDeficitBracket S r s := by
  have hsum : ∑ Q ∈ S, W.veluDeficitLinearTerm Q.1 Q.2 r s
      = ∑ Q ∈ S, (-(W.veluU Q.1 Q.2) ^ 2 / (r - Q.1) ^ 3
          - 3 * W.veluT Q.1 Q.2 * W.veluU Q.1 Q.2 / (r - Q.1) ^ 2
          - (3 * (W.veluT Q.1 Q.2) ^ 2 + 6 * (W.Ψ₃).eval Q.1) / (r - Q.1)) :=
    Finset.sum_congr rfl fun Q hQmem =>
      W.veluDeficitLinearTerm_eq hP (hSeq Q hQmem) (hr Q hQmem)
  rw [← hsum, ← W.veluDeficit_linearPart_eq_sum, W.veluDeficit_eq_of_equation hP,
    veluDeficitBracket]
  ring

end FullExpansion

section PsiCofactor

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluDeficitPsiCofactor (x₀ x : R) : R :=
  2*W.a₁^2*x^3*x₀ - 3*W.a₁^2*x^2*x₀^2 + W.a₁^2*x₀^4 + 2*W.a₁*W.a₃*x^3 - 6*W.a₁*W.a₃*x*x₀^2
    + 4*W.a₁*W.a₃*x₀^3 + 8*W.a₂*x^3*x₀ - 12*W.a₂*x^2*x₀^2 + 4*W.a₂*x₀^4 + 3*W.a₃^2*x^2
    - 6*W.a₃^2*x*x₀ + 3*W.a₃^2*x₀^2 + 4*W.a₄*x^3 - 12*W.a₄*x*x₀^2 + 8*W.a₄*x₀^3 + 12*W.a₆*x^2
    - 24*W.a₆*x*x₀ + 12*W.a₆*x₀^2 - 6*x^5 + 30*x^4*x₀ - 48*x^3*x₀^2 + 36*x^2*x₀^3 - 18*x*x₀^4
    + 6*x₀^5

lemma eval_Ψ₃_eq' (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [Ψ₃]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow, eval_ofNat]

end PsiCofactor

section PsiCofactorCleared

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem velu_singleton_deficit_cleared_eq_psi {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      - (W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6)
      = W.veluDeficitPsiCofactor x₀ x * (W.Ψ₃).eval x₀ := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq']
  simp only [veluDeficitPsiCofactor, b₂, b₄, b₆, b₈, veluXNum, veluYNum, veluT, veluU, veluW,
    veluGx, veluGy]
  linear_combination
    (W.a₁^4*x^2*x₀^2 + 2*W.a₁^4*x*x₀^3 + W.a₁^4*x₀^4 + 2*W.a₁^3*W.a₃*x^2*x₀ + 8*W.a₁^3*W.a₃*x*x₀^2 + 6*W.a₁^3*W.a₃*x₀^3 + 16*W.a₁^3*x*x₀^2*y₀ + 16*W.a₁^3*x₀^3*y₀ + 8*W.a₁^2*W.a₂*x^2*x₀^2 - 8*W.a₁^2*W.a₂*x₀^4 + W.a₁^2*W.a₃^2*x^2 + 10*W.a₁^2*W.a₃^2*x*x₀ + 13*W.a₁^2*W.a₃^2*x₀^2 + 32*W.a₁^2*W.a₃*x*x₀*y₀ + 64*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^2*x₀ - 4*W.a₁^2*W.a₄*x₀^3 - 2*W.a₁^2*x^4*x₀ + 4*W.a₁^2*x^3*x₀^2 + 12*W.a₁^2*x^2*x₀^3 - 4*W.a₁^2*x*x₀^4 + 16*W.a₁^2*x*x₀*y₀^2 - 10*W.a₁^2*x₀^5 + 80*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^2*x₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2 - 24*W.a₁*W.a₂*W.a₃*x₀^3 + 64*W.a₁*W.a₂*x*x₀^2*y₀ - 64*W.a₁*W.a₂*x₀^3*y₀ + 4*W.a₁*W.a₃^3*x + 12*W.a₁*W.a₃^3*x₀ + 16*W.a₁*W.a₃^2*x*y₀ + 80*W.a₁*W.a₃^2*x₀*y₀ + 4*W.a₁*W.a₃*W.a₄*x^2 + 8*W.a₁*W.a₃*W.a₄*x*x₀ - 12*W.a₁*W.a₃*W.a₄*x₀^2 - 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^2*x₀^2 + 8*W.a₁*W.a₃*x*x₀^3 + 16*W.a₁*W.a₃*x*y₀^2 - 30*W.a₁*W.a₃*x₀^4 + 176*W.a₁*W.a₃*x₀*y₀^2 + 32*W.a₁*W.a₄*x*x₀*y₀ - 32*W.a₁*W.a₄*x₀^2*y₀ - 16*W.a₁*x^3*x₀*y₀ + 48*W.a₁*x^2*x₀^2*y₀ + 48*W.a₁*x*x₀^3*y₀ - 80*W.a₁*x₀^4*y₀ + 128*W.a₁*x₀*y₀^3 + 16*W.a₂^2*x^2*x₀^2 - 32*W.a₂^2*x*x₀^3 + 16*W.a₂^2*x₀^4 + 16*W.a₂*W.a₃^2*x*x₀ - 16*W.a₂*W.a₃^2*x₀^2 + 64*W.a₂*W.a₃*x*x₀*y₀ - 64*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^2*x₀ - 32*W.a₂*W.a₄*x*x₀^2 + 16*W.a₂*W.a₄*x₀^3 - 8*W.a₂*x^4*x₀ + 32*W.a₂*x^3*x₀^2 - 64*W.a₂*x*x₀^4 + 64*W.a₂*x*x₀*y₀^2 + 40*W.a₂*x₀^5 - 64*W.a₂*x₀^2*y₀^2 + 4*W.a₃^4 + 32*W.a₃^3*y₀ + 8*W.a₃^2*W.a₄*x - 8*W.a₃^2*W.a₄*x₀ - 4*W.a₃^2*x^3 + 12*W.a₃^2*x^2*x₀ + 12*W.a₃^2*x*x₀^2 - 20*W.a₃^2*x₀^3 + 96*W.a₃^2*y₀^2 + 32*W.a₃*W.a₄*x*y₀ - 32*W.a₃*W.a₄*x₀*y₀ - 16*W.a₃*x^3*y₀ + 48*W.a₃*x^2*x₀*y₀ + 48*W.a₃*x*x₀^2*y₀ - 80*W.a₃*x₀^3*y₀ + 128*W.a₃*y₀^3 + 4*W.a₄^2*x^2 - 8*W.a₄^2*x*x₀ + 4*W.a₄^2*x₀^2 - 4*W.a₄*x^4 + 16*W.a₄*x^3*x₀ - 32*W.a₄*x*x₀^3 + 32*W.a₄*x*y₀^2 + 20*W.a₄*x₀^4 - 32*W.a₄*x₀*y₀^2 + x^6 - 6*x^5*x₀ + 3*x^4*x₀^2 + 28*x^3*x₀^3 - 16*x^3*y₀^2 - 21*x^2*x₀^4 + 48*x^2*x₀*y₀^2 - 30*x*x₀^5 + 48*x*x₀^2*y₀^2 + 25*x₀^6 - 80*x₀^3*y₀^2 + 64*y₀^4) * hP
    + (2*W.a₁^4*x^3*x₀ - 4*W.a₁^4*x^2*x₀^2 - 2*W.a₁^4*x*x₀^3 + 2*W.a₁^3*W.a₃*x^3 - 2*W.a₁^3*W.a₃*x^2*x₀ - 14*W.a₁^3*W.a₃*x*x₀^2 - 2*W.a₁^3*W.a₃*x₀^3 + 12*W.a₁^3*x^2*x₀*y₀ - 40*W.a₁^3*x*x₀^2*y₀ - 4*W.a₁^3*x₀^3*y₀ + 16*W.a₁^2*W.a₂*x^3*x₀ - 44*W.a₁^2*W.a₂*x^2*x₀^2 + 24*W.a₁^2*W.a₂*x*x₀^3 + 4*W.a₁^2*W.a₂*x₀^4 + 2*W.a₁^2*W.a₃^2*x^2 - 16*W.a₁^2*W.a₃^2*x*x₀ - 10*W.a₁^2*W.a₃^2*x₀^2 + 12*W.a₁^2*W.a₃*x^2*y₀ - 56*W.a₁^2*W.a₃*x*x₀*y₀ - 52*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^3 - 16*W.a₁^2*W.a₄*x^2*x₀ + 12*W.a₁^2*W.a₄*x*x₀^2 + 12*W.a₁^2*W.a₆*x^2 - 24*W.a₁^2*W.a₆*x*x₀ + 12*W.a₁^2*W.a₆*x₀^2 - 6*W.a₁^2*x^5 + 32*W.a₁^2*x^4*x₀ - 28*W.a₁^2*x^3*x₀^2 - 12*W.a₁^2*x^2*x₀^3 + 12*W.a₁^2*x^2*y₀^2 - 14*W.a₁^2*x*x₀^4 - 40*W.a₁^2*x*x₀*y₀^2 + 28*W.a₁^2*x₀^5 - 68*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^3 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀ - 40*W.a₁*W.a₂*W.a₃*x*x₀^2 + 40*W.a₁*W.a₂*W.a₃*x₀^3 + 48*W.a₁*W.a₂*x^2*x₀*y₀ - 160*W.a₁*W.a₂*x*x₀^2*y₀ + 112*W.a₁*W.a₂*x₀^3*y₀ - 4*W.a₁*W.a₃^3*x - 12*W.a₁*W.a₃^3*x₀ - 16*W.a₁*W.a₃^2*x*y₀ - 80*W.a₁*W.a₃^2*x₀*y₀ - 16*W.a₁*W.a₃*W.a₄*x^2 + 16*W.a₁*W.a₃*W.a₄*x*x₀ + 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^3*x₀ + 12*W.a₁*W.a₃*x^2*x₀^2 - 152*W.a₁*W.a₃*x*x₀^3 - 16*W.a₁*W.a₃*x*y₀^2 + 114*W.a₁*W.a₃*x₀^4 - 176*W.a₁*W.a₃*x₀*y₀^2 - 32*W.a₁*W.a₄*x*x₀*y₀ + 32*W.a₁*W.a₄*x₀^2*y₀ + 16*W.a₁*x^3*x₀*y₀ + 96*W.a₁*x^2*x₀^2*y₀ - 336*W.a₁*x*x₀^3*y₀ + 224*W.a₁*x₀^4*y₀ - 128*W.a₁*x₀*y₀^3 + 32*W.a₂^2*x^3*x₀ - 112*W.a₂^2*x^2*x₀^2 + 128*W.a₂^2*x*x₀^3 - 48*W.a₂^2*x₀^4 + 24*W.a₂*W.a₃^2*x^2 - 64*W.a₂*W.a₃^2*x*x₀ + 40*W.a₂*W.a₃^2*x₀^2 + 48*W.a₂*W.a₃*x^2*y₀ - 160*W.a₂*W.a₃*x*x₀*y₀ + 112*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^3 - 64*W.a₂*W.a₄*x^2*x₀ + 80*W.a₂*W.a₄*x*x₀^2 - 32*W.a₂*W.a₄*x₀^3 + 48*W.a₂*W.a₆*x^2 - 96*W.a₂*W.a₆*x*x₀ + 48*W.a₂*W.a₆*x₀^2 - 24*W.a₂*x^5 + 128*W.a₂*x^4*x₀ - 128*W.a₂*x^3*x₀^2 - 144*W.a₂*x^2*x₀^3 + 48*W.a₂*x^2*y₀^2 + 280*W.a₂*x*x₀^4 - 160*W.a₂*x*x₀*y₀^2 - 112*W.a₂*x₀^5 + 112*W.a₂*x₀^2*y₀^2 - 4*W.a₃^4 - 32*W.a₃^3*y₀ - 8*W.a₃^2*W.a₄*x + 8*W.a₃^2*W.a₄*x₀ + 4*W.a₃^2*x^3 + 60*W.a₃^2*x^2*x₀ - 156*W.a₃^2*x*x₀^2 + 92*W.a₃^2*x₀^3 - 96*W.a₃^2*y₀^2 - 32*W.a₃*W.a₄*x*y₀ + 32*W.a₃*W.a₄*x₀*y₀ + 16*W.a₃*x^3*y₀ + 96*W.a₃*x^2*x₀*y₀ - 336*W.a₃*x*x₀^2*y₀ + 224*W.a₃*x₀^3*y₀ - 128*W.a₃*y₀^3 - 16*W.a₄^2*x^2 + 32*W.a₄^2*x*x₀ - 16*W.a₄^2*x₀^2 + 4*W.a₄*x^4 + 32*W.a₄*x^3*x₀ - 72*W.a₄*x^2*x₀^2 + 32*W.a₄*x*x₀^3 - 32*W.a₄*x*y₀^2 + 4*W.a₄*x₀^4 + 32*W.a₄*x₀*y₀^2 + 144*W.a₆*x^2*x₀ - 288*W.a₆*x*x₀^2 + 144*W.a₆*x₀^3 - 72*x^5*x₀ + 372*x^4*x₀^2 - 624*x^3*x₀^3 + 16*x^3*y₀^2 + 360*x^2*x₀^4 + 96*x^2*x₀*y₀^2 + 24*x*x₀^5 - 336*x*x₀^2*y₀^2 - 60*x₀^6 + 224*x₀^3*y₀^2 - 64*y₀^4) * hQ

end PsiCofactorCleared

section PsiField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_singleton_mul_pow_eq_psi {x₀ y₀ r s : F}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) (hr : r ≠ x₀) :
    W.veluDeficit {(x₀, y₀)} r s * (r - x₀) ^ 6
      = W.veluDeficitPsiCofactor x₀ r * (W.Ψ₃).eval x₀ := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  rw [← W.velu_singleton_deficit_cleared_eq_psi hP hQ, veluDeficit,
    W.veluX_singleton x₀ y₀ hr, W.veluY_singleton x₀ y₀ s hr, veluQuotient_a₄, veluQuotient_a₆,
    veluTSum, veluWSum, Finset.sum_singleton, Finset.sum_singleton]
  field_simp

end PsiField

section LinQuad

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitLin (S : Finset (F × F)) (r s : F) : F :=
  -(W.veluY S r s - s) * W.veluGy r s - (W.veluX S r - r) * W.veluGx r s
    + 5 * W.veluTSum S * r + W.b₂ * W.veluTSum S + 7 * W.veluWSum S

def veluDeficitQuad (S : Finset (F × F)) (r s : F) : F :=
  (W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s)
    - (3 * r + W.a₂) * (W.veluX S r - r) ^ 2 - (W.veluX S r - r) ^ 3
    + 5 * W.veluTSum S * (W.veluX S r - r)

theorem veluDeficit_eq_lin_add_quad_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficit S r s = W.veluDeficitLin S r s + W.veluDeficitQuad S r s := by
  rw [W.veluDeficit_eq_of_equation hP, veluDeficitLin, veluDeficitQuad]
  ring

@[scoped simp] lemma veluDeficitLin_empty (r s : F) : W.veluDeficitLin ∅ r s = 0 := by
  simp [veluDeficitLin]

theorem veluDeficitLin_eq_sum_singleton (S : Finset (F × F)) (r s : F) :
    W.veluDeficitLin S r s = ∑ A ∈ S, W.veluDeficitLin {A} r s := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert A S hA ih =>
    rw [Finset.sum_insert hA, ← ih]
    simp only [veluDeficitLin, veluTSum, veluWSum, veluX, veluY, Finset.sum_insert hA,
      Finset.sum_singleton]
    ring

def veluDeficitCrossQuad (S : Finset (F × F)) (r s : F) : F :=
  W.veluDeficitQuad S r s - ∑ A ∈ S, W.veluDeficitQuad {A} r s

theorem veluDeficit_eq_sum_singleton_add_crossQuad {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficit S r s
      = (∑ A ∈ S, W.veluDeficit {A} r s) + W.veluDeficitCrossQuad S r s := by
  rw [W.veluDeficit_eq_lin_add_quad_of_equation hP, veluDeficitCrossQuad,
    W.veluDeficitLin_eq_sum_singleton,
    show (∑ A ∈ S, W.veluDeficit {A} r s)
        = ∑ A ∈ S, (W.veluDeficitLin {A} r s + W.veluDeficitQuad {A} r s) from
      Finset.sum_congr rfl fun A _ => W.veluDeficit_eq_lin_add_quad_of_equation hP,
    Finset.sum_add_distrib]
  ring

end LinQuad

section ReducedCofactor

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluDeficitPsiCofactorReduced (x₀ x : R) : R :=
  -6 * x ^ 3 + 18 * x₀ * x ^ 2 + (2 * W.b₂ * x₀ + 2 * W.b₄ - 6 * x₀ ^ 2) * x
    + (6 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 4 * W.b₄ * x₀ + 3 * W.b₆)

theorem veluDeficitPsiCofactor_eq_sq_mul_reduced (x₀ x : R) :
    W.veluDeficitPsiCofactor x₀ x = (x - x₀) ^ 2 * W.veluDeficitPsiCofactorReduced x₀ x := by
  simp only [veluDeficitPsiCofactor, veluDeficitPsiCofactorReduced, b₂, b₄, b₆]
  ring

def veluDeficitPsiCofactorReducedPoly (x₀ : R) : R[X] :=
  C (-6) * X ^ 3 + C (18 * x₀) * X ^ 2 + C (2 * W.b₂ * x₀ + 2 * W.b₄ - 6 * x₀ ^ 2) * X
    + C (6 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 4 * W.b₄ * x₀ + 3 * W.b₆)

@[scoped simp] lemma eval_veluDeficitPsiCofactorReducedPoly (x₀ x : R) :
    (W.veluDeficitPsiCofactorReducedPoly x₀).eval x = W.veluDeficitPsiCofactorReduced x₀ x := by
  simp [veluDeficitPsiCofactorReducedPoly, veluDeficitPsiCofactorReduced]

lemma veluDeficitPsiCofactorReducedPoly_natDegree_le (x₀ : R) :
    (W.veluDeficitPsiCofactorReducedPoly x₀).natDegree ≤ 3 := by
  unfold veluDeficitPsiCofactorReducedPoly
  compute_degree

end ReducedCofactor

section ReducedField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_singleton_mul_pow_four_eq {x₀ y₀ r s : F}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) (hr : r ≠ x₀) :
    W.veluDeficit {(x₀, y₀)} r s * (r - x₀) ^ 4
      = W.veluDeficitPsiCofactorReduced x₀ r * (W.Ψ₃).eval x₀ := by
  have hd : (r - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hr)
  have key := W.veluDeficit_singleton_mul_pow_eq_psi hP hQ hr
  rw [W.veluDeficitPsiCofactor_eq_sq_mul_reduced] at key
  have h64 : (r - x₀) ^ 6 = (r - x₀) ^ 4 * (r - x₀) ^ 2 := by ring
  rw [h64, ← mul_assoc] at key
  exact mul_right_cancel₀ hd (by linear_combination key)

end ReducedField

section RRCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitIsConstantAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ c : F, ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = c

end RRCarrier

section ConstantZero

variable {F : Type*} [Field F]

variable (F)
variable [DecidableEq F]

def VeluDeficitConstantIsZeroAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ c : F, (∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = c) →
          c = 0

theorem veluDeficitConstancyAt_of_isConstant_of_constantZero {p : ℕ}
    (hC : VeluDeficitIsConstantAt F p) (hZ : VeluDeficitConstantIsZeroAt F p) :
    VeluDeficitConstancyAt F p := by
  intro W hΔ x₀ y₀ h₀ hord r s hrs hav
  obtain ⟨c, hc⟩ := hC W hΔ x₀ y₀ h₀ hord
  rw [hc hrs hav, hZ W hΔ x₀ y₀ h₀ hord c hc]

end ConstantZero

section Parity

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_negY (S : Finset (F × F)) (r s : F) :
    W.veluDeficit S r (W.toAffine.negY r s) = W.veluDeficit S r s := by
  unfold veluDeficit
  rw [W.veluY_negY]
  simp only [Affine.negY, veluQuotient_a₁, veluQuotient_a₃]
  ring

theorem veluDeficit_sum_singleton_negY (S : Finset (F × F)) (r s : F) :
    (∑ A ∈ S, W.veluDeficit {A} r (W.toAffine.negY r s))
      = ∑ A ∈ S, W.veluDeficit {A} r s :=
  Finset.sum_congr rfl fun A _ => W.veluDeficit_negY {A} r s

theorem veluDeficitCrossQuad_negY_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficitCrossQuad S r (W.toAffine.negY r s) = W.veluDeficitCrossQuad S r s := by
  have hP' : W.toAffine.Equation r (W.toAffine.negY r s) := (Affine.equation_neg r s).mpr hP
  have key := W.veluDeficit_eq_sum_singleton_add_crossQuad (S := S) hP'
  rw [W.veluDeficit_negY, W.veluDeficit_sum_singleton_negY,
    W.veluDeficit_eq_sum_singleton_add_crossQuad hP] at key
  exact (add_left_cancel key).symm

end Parity

section AlphaSqCross

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaSq (S : Finset (F × F)) (r : F) : F :=
  (-(3 * r + W.a₂) * (W.veluX S r - r) ^ 2 + 5 * W.veluTSum S * (W.veluX S r - r))
    - ∑ A ∈ S, (-(3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2
        + 5 * W.veluTSum {A} * (W.veluX {A} r - r))

def veluDeficitCrossQuadCubeBeta (S : Finset (F × F)) (r s : F) : F :=
  W.veluDeficitCrossQuad S r s - W.veluDeficitCrossQuadAlphaSq S r

lemma veluDeficitCrossQuad_eq_alphaSq_add_cubeBeta (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuad S r s
      = W.veluDeficitCrossQuadAlphaSq S r + W.veluDeficitCrossQuadCubeBeta S r s := by
  unfold veluDeficitCrossQuadCubeBeta; ring

end AlphaSqCross

end WeierstrassCurve
