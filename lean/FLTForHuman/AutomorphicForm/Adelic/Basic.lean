/-
  The adèlic group `GL₂(𝔸_K)` and its structural maps.

  `AdelicGL2 R K` is `GL₂(𝔸_K)`; `globalPoints` embeds the rational points
  `GL₂(K)`, `centralScalar` the idèles as central scalars, and `chiDet` turns an
  idèle-class character into the central character `g ↦ χ(det g)` on the group.
  This is the base vocabulary of every adèlic automorphic module.

  `Definitions/Def_AutomorphicForm_AdelicLsXi.lean` mixes this base vocabulary
  with the `LsXi` L²-space; the port splits it (playbook §3.1) and this module is
  the first half, transcribed verbatim from the pin (pinned `aa2d8b3`).
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open NumberField Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

def globalPoints : Matrix.GeneralLinearGroup (Fin 2) K →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

def centralScalar : (AdeleRing R K)ˣ →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

def chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K → ℂ :=
  fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

/-- A central scalar commutes with every element of `GL₂(𝔸_K)`.  This is the one home of the fact
(`centralScalar` is a scalar matrix, hence central); the Siegel and cusp modules that use it import
it from here rather than re-proving it. -/
theorem centralScalar_mul_comm {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (z : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    centralScalar R K z * g = g * centralScalar R K z := by
  have hz : centralScalar R K z ∈ Subgroup.center (AdelicGL2 R K) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨z, rfl⟩
  exact ((Subgroup.mem_center_iff.mp hz) g).symm

end AutomorphicForm

end
