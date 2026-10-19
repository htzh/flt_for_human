/-
  The elementary matrices of the GL₂ strong-approximation engine.

  The two unitriangular subgroups `unipotentGL2`/`lowerUnipGL2`, the diagonal torus
  `diagTorusGL2` (the `1 × u` torus, whose determinant is the unit `u`), their
  multiplicativity and their functoriality under a ring homomorphism
  (`GeneralLinearGroup.map`), the two conjugation-entry formulas
  `conj_unipotent_entry`/`conj_lowerUnip_entry` (a conjugated unipotent is the
  identity plus one rank-one term), and the four-factor Gauss (LU) identity
  `gauss_factorization`: with `c` the lower-left entry, `δ` the determinant and
  `ci`, `δi` their inverses, a `2 × 2` matrix is
  `unipotent * lowerUnip * unipotent * diagonal`.

  Transcribed verbatim from
  `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:21–128`
  (the pin's `ElementaryMatrices` section, pinned `aa2d8b3`). The pin's
  `p2m_open`/`p2m_export` scaffolding is not transcribed; this module is the
  first of the five tier-3 engine modules of the GL₂ strong-approximation port and
  assumes nothing beyond `AutomorphicForm.unipotentGL2`.
-/
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option autoImplicit false

open Matrix AutomorphicForm

noncomputable section

namespace NumberField

namespace AdelicLevel

namespace GL2StrongApproxW8M

section ElementaryMatrices

variable {S : Type*} [CommRing S]

-- pin: lowerUnipGL2 (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:25)
def lowerUnipGL2 (x : S) : GL (Fin 2) S where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

-- pin: lowerUnipGL2_coe (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:37)
@[scoped simp] theorem lowerUnipGL2_coe (x : S) :
    (lowerUnipGL2 x : Matrix (Fin 2) (Fin 2) S) = !![1, 0; x, 1] := rfl

-- pin: lowerUnipGL2_inv (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:40)
theorem lowerUnipGL2_inv (x : S) : (lowerUnipGL2 x)⁻¹ = lowerUnipGL2 (-x) :=
  Units.ext rfl

-- pin: unipotentGL2_inv (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:43)
theorem unipotentGL2_inv (x : S) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  Units.ext rfl

-- pin: lowerUnipGL2_add (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:46)
theorem lowerUnipGL2_add (x y : S) :
    lowerUnipGL2 (x + y) = lowerUnipGL2 x * lowerUnipGL2 y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]

-- pin: map_lowerUnipGL2 (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:52)
theorem map_lowerUnipGL2 {T : Type*} [CommRing T] (f : S →+* T) (x : S) :
    GeneralLinearGroup.map f (lowerUnipGL2 x) = lowerUnipGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipGL2, GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

-- pin: map_unipotentGL2 (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:58)
theorem map_unipotentGL2 {T : Type*} [CommRing T] (f : S →+* T) (x : S) :
    GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentGL2, GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

-- pin: diagTorusGL2 (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:64)
def diagTorusGL2 (u : Sˣ) : GL (Fin 2) S where
  val := !![1, 0; 0, (u : S)]
  inv := !![1, 0; 0, ((u⁻¹ : Sˣ) : S)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

-- pin: diagTorusGL2_coe (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:76)
@[scoped simp] theorem diagTorusGL2_coe (u : Sˣ) :
    (diagTorusGL2 u : Matrix (Fin 2) (Fin 2) S) = !![1, 0; 0, (u : S)] := rfl

-- pin: diagTorusGL2_mul (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:79)
theorem diagTorusGL2_mul (u w : Sˣ) :
    diagTorusGL2 (u * w) = diagTorusGL2 u * diagTorusGL2 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]

-- pin: map_diagTorusGL2 (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:85)
theorem map_diagTorusGL2 {T : Type*} [CommRing T] (f : S →+* T) (u : Sˣ) :
    GeneralLinearGroup.map f (diagTorusGL2 u) = diagTorusGL2 (Units.map (f : S →* T) u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTorusGL2, GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

-- pin: conj_unipotent_entry (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:91)
theorem conj_unipotent_entry {u w : Matrix (Fin 2) (Fin 2) S} (h : u * w = 1) (b : S)
    (i j : Fin 2) :
    (u * !![1, b; 0, 1] * w) i j
      = (1 : Matrix (Fin 2) (Fin 2) S) i j + b * (u i 0 * w 1 j) := by
  have hcalc : (u * !![1, b; 0, 1] * w) i j = (u * w) i j + b * (u i 0 * w 1 j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hcalc, h]

-- pin: conj_lowerUnip_entry (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:100)
theorem conj_lowerUnip_entry {u w : Matrix (Fin 2) (Fin 2) S} (h : u * w = 1) (b : S)
    (i j : Fin 2) :
    (u * !![1, 0; b, 1] * w) i j
      = (1 : Matrix (Fin 2) (Fin 2) S) i j + b * (u i 1 * w 0 j) := by
  have hcalc : (u * !![1, 0; b, 1] * w) i j = (u * w) i j + b * (u i 1 * w 0 j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hcalc, h]

-- pin: gauss_factorization (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:109)
theorem gauss_factorization (M : Matrix (Fin 2) (Fin 2) S) (c ci δ δi : S)
    (hc : M 1 0 = c) (hci : c * ci = 1) (hδ : M.det = δ) (hδi : δ * δi = 1) :
    !![1, (M 0 0 - 1) * ci; 0, 1] * !![1, 0; c, 1]
        * !![1, (M 1 1 * δi - 1) * ci; 0, 1]
        * !![1, 0; 0, δ] = M := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = δ := by
    rw [← Matrix.det_fin_two]; exact hδ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (M 0 0 - 1) * hci
  · linear_combination
      (M 0 1 + (M 0 0 - 1) * (M 1 1 * δi - 1) * ci * δ) * hci
        + (ci * M 0 1) * hc + ci * hdet + (ci * M 0 0 * M 1 1) * hδi
  · linear_combination - hc
  · linear_combination ((M 1 1 * δi - 1) * δ) * hci + M 1 1 * hδi

end ElementaryMatrices

end GL2StrongApproxW8M

end AdelicLevel

end NumberField
