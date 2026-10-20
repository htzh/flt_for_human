/-
  The integral subgroup of `GL₂` over a commutative ring.

  `LocalGL2.integralSubgroup R K` is the image of `GL₂(R)` in `GL₂(K)` under the
  coefficient map: the elements of `GL₂(K)` both of whose `R`-entries and whose
  inverse's entries are integral. `transposeGL` is the transpose as a group element
  (an anti-automorphism, an involution, and preserving the integral subgroup), and
  `det_map_algebraMap` is the determinant of the coefficient map.

  Transcribed verbatim from `Definitions/Def_LocalLanglands_LocalHeckeInstance.lean`
  (pinned `aa2d8b3`, 78 lines / 10 declarations). The pin's `import Mathlib` is
  replaced by specific mathlib modules; `LocalGL2` is the pin's namespace and is kept.
  The pin also imports `Def_LocalLanglands_HeckePair` and
  `Def_LocalLanglands_CartanDecomposition`, whose declarations are not used here, so
  neither is imported.

  spec-pin: Definitions/Def_LocalLanglands_LocalHeckeInstance.lean
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

open Matrix

noncomputable section

namespace LocalGL2

def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range

theorem mem_integralSubgroup_iff {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {x : GL (Fin 2) K} :
    x ∈ integralSubgroup R K ↔
      ∃ y : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (algebraMap R K) y = x :=
  Iff.rfl

section Transpose

variable {A : Type*} [CommRing A]

def transposeGL (x : GL (Fin 2) A) : GL (Fin 2) A where
  val := x.valᵀ
  inv := x.invᵀ
  val_inv := by rw [← Matrix.transpose_mul, x.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, x.val_inv, Matrix.transpose_one]

@[simp] theorem transposeGL_val (x : GL (Fin 2) A) :
    (transposeGL x : Matrix (Fin 2) (Fin 2) A) = (x : Matrix (Fin 2) (Fin 2) A)ᵀ := rfl

theorem transposeGL_mul (x y : GL (Fin 2) A) :
    transposeGL (x * y) = transposeGL y * transposeGL x := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeGL_val, transposeGL_val, transposeGL_val, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeGL_involutive (x : GL (Fin 2) A) : transposeGL (transposeGL x) = x := by
  refine Units.ext ?_
  rw [transposeGL_val, transposeGL_val, Matrix.transpose_transpose]

@[simp] theorem transposeGL_one : transposeGL (1 : GL (Fin 2) A) = 1 := by
  refine Units.ext ?_
  rw [transposeGL_val, Units.val_one, Matrix.transpose_one]

end Transpose

section IntegralPreservation

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem transposeGL_map_algebraMap (y : GL (Fin 2) R) :
    transposeGL (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y)
      = Matrix.GeneralLinearGroup.map (algebraMap R K) (transposeGL y) := by
  refine Units.ext ?_
  show ((Matrix.GeneralLinearGroup.map (algebraMap R K) y :
      Matrix (Fin 2) (Fin 2) K))ᵀ = _
  ext i j
  simp [Matrix.transpose_apply]

theorem transposeGL_mem_integralSubgroup {x : GL (Fin 2) K} (hx : x ∈ integralSubgroup R K) :
    transposeGL x ∈ integralSubgroup R K := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨transposeGL y, (transposeGL_map_algebraMap y).symm⟩

theorem det_map_algebraMap (M : Matrix (Fin 2) (Fin 2) R) :
    (M.map (algebraMap R K)).det = algebraMap R K M.det := by
  simp [Matrix.det_fin_two]

end IntegralPreservation

end LocalGL2

end
