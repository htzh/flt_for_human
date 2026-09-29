/-
  A group representation attached to a matrix representation: the monoid
  homomorphism `G →* GL n k` gives the `k`-representation of `G` on the
  column vectors `n → k` by matrix-vector multiplication.

  Transcribed verbatim from `Definitions/Def_Deformations_MatrixRepresentation.lean`
  (pinned `aa2d8b3`, 23 lines).
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

set_option autoImplicit false

universe u

namespace Deformation

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

noncomputable def matrixRepresentation (ρ : G →* GL n k) : Representation k G (n → k) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp]
lemma matrixRepresentation_apply (ρ : G →* GL n k) (g : G) :
    matrixRepresentation ρ g = Matrix.mulVecLin (ρ g).val :=
  Matrix.GeneralLinearGroup.coe_toLin _

end Deformation
