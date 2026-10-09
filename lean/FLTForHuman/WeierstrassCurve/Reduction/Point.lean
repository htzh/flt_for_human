/-
The reduction map of an integral Weierstrass model (WORKORDER-W4-definition-wave.md, stage 1).

The bottom of the good-reduction definition layer: the coordinate-wise reduction of the
affine points of `W.map A.subtype` onto the points of the residue curve `W.map (residue A)`,
whenever that curve is smooth (`Δ ≠ 0`), a point with non-integral `x` reducing to the point
at infinity.  This is `Definitions/Def_WeierstrassCurve_ReductionMap.lean`'s Weierstrass half
(pinned `aa2d8b3`, lines 97–197); the two `ValuationSubring` tool blocks of the same pin file
(`mul_mem_nonunits`, `one_notMem_nonunits`, and the decomposition/inertia action) are homed
beside the file's first such block in
`FLTForHuman/NumberTheory/ValuationAtPlace.lean`, not here.

Statements are transcribed verbatim from the pin; the proof bodies are adapted to mathlib
`v4.34.0` (the pin's `dif_pos`/`dif_neg` are `dite_eq_left`/`dite_eq_right`, which are no
longer deprecated).  The pin's `attribute [-instance]`/`[-simp]` scaffolding is not
transcribed: none of its names is in the port's import cone.

Assumes from `NumberTheory/ValuationAtPlace.lean`: `ValuationSubring.{mul_mem_nonunits,
one_notMem_nonunits}`.  `reducePoint` uses `open Classical in` and is `noncomputable`, as in
the pin.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_ReductionMap.lean>
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.LocalSubring
import FLTForHuman.NumberTheory.ValuationAtPlace

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L}

private lemma some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

variable (W : WeierstrassCurve A)

theorem Affine.Y_mem_of_X_mem {x y : L}
    (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  by_contra hy

  have hy0 : y ≠ 0 := fun h0 => hy (h0 ▸ A.zero_mem)
  have hyinv : y⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hy)
  rw [equation_iff] at h

  have key : (1 : L) =
      (x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2 + (W.map A.subtype).toAffine.a₄ * x
          + (W.map A.subtype).toAffine.a₆) * (y⁻¹ * y⁻¹)
        - (W.map A.subtype).toAffine.a₁ * x * y⁻¹
        - (W.map A.subtype).toAffine.a₃ * y⁻¹ := by
    field_simp
    linear_combination h

  refine A.one_notMem_nonunits ?_
  rw [key]
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have ha₆ : (W.map A.subtype).toAffine.a₆ ∈ A := SetLike.coe_mem W.a₆
  have hcubic : x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2
      + (W.map A.subtype).toAffine.a₄ * x + (W.map A.subtype).toAffine.a₆ ∈ A :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2))) (mul_mem ha₄ hx)) ha₆
  exact sub_mem (sub_mem (A.mul_mem_nonunits hcubic (mul_mem hyinv hyinv))
      (A.mul_mem_nonunits (mul_mem ha₁ hx) hyinv))
    (A.mul_mem_nonunits ha₃ hyinv)

theorem map_residue_Δ_ne_zero_iff : (W.map (residue A)).Δ ≠ 0 ↔ IsUnit W.Δ := by
  rw [map_Δ]
  exact residue_ne_zero_iff_isUnit W.Δ

theorem Affine.equation_residue {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Equation (residue A x) (residue A y) := by
  have hA : W.toAffine.Equation x y := (W.toAffine.map_equation A.subtype_injective x y).mp h
  exact hA.map (residue A)

theorem Affine.nonsingular_residue (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (Affine.equation_residue W h)

variable {W}

open Classical in

noncomputable def reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1)
    else
      .zero

variable (hΔ : (W.map (residue A)).Δ ≠ 0)

@[simp]
lemma reducePoint_zero : reducePoint hΔ (0 : (W.map A.subtype).toAffine.Point) = 0 :=
  rfl

lemma reducePoint_some_of_mem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    reducePoint hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) := by
  simp only [reducePoint]
  exact dite_eq_left hx

lemma reducePoint_some_of_notMem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∉ A) : reducePoint hΔ (.some x y h) = 0 := by
  simp only [reducePoint]
  exact dite_eq_right hx

theorem reducePoint_neg (P : (W.map A.subtype).toAffine.Point) :
    reducePoint hΔ (-P) = -reducePoint hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      rw [reducePoint_some_of_mem _ _ hx, reducePoint_some_of_mem _ _ hx,
        Affine.Point.neg_some]
      refine some_congr rfl ?_ _ _
      show residue A (W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩) = _
      exact (Affine.map_negY (residue A) (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    · rw [reducePoint_some_of_notMem _ _ hx, reducePoint_some_of_notMem _ _ hx]
      rfl

section Inertia

open scoped Pointwise

variable (K : Type*) [Field K] [Algebra K L]

theorem reducePoint_some_apply_of_mem_inertia {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) :
    reducePoint hΔ (.some (σ x) (σ y) h') = reducePoint hΔ (.some x y h) := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup hσ hx
    have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup hσ hy
    rw [reducePoint_some_of_mem _ _ hσx, reducePoint_some_of_mem _ _ hx]

    refine some_congr ?_ ?_ _ _
    · calc residue A (⟨σ x, hσx⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨x, hx⟩ : A)) := rfl
        _ = residue A (⟨x, hx⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
    · calc residue A (⟨σ y, hσy⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨y, hy⟩ : A)) := rfl
        _ = residue A (⟨y, hy⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
  · have hσx : σ x ∉ A := fun hmem => hx (by
      simpa using A.smul_mem_of_mem_decompositionSubgroup (inv_mem hσ) hmem)
    rw [reducePoint_some_of_notMem _ _ hσx, reducePoint_some_of_notMem _ _ hx]

end Inertia

end WeierstrassCurve
