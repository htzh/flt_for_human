/-
  The principal level subgroup.

  `weyl` is the Weyl element `!![0, 1; 1, 0]` of `GL₂(𝔸_K)`, and `principalLevel N` is
  the intersection of `levelOne N` with its `weyl`-conjugate — the subgroup fixed by
  the Atkin–Lehner involution, the level structure the principal-level smoothing
  theorem is invariant under. It is contained in `levelOne N`.

  Transcribed verbatim from `Definitions/Def_NumberField_PrincipalLevel.lean`
  (pinned `aa2d8b3`); the pin's `Def_NumberField_AdelicLevel` import is the port's
  `AdelicLevel/Level`.
-/
import FLTForHuman.NumberTheory.AdelicLevel.Level
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def weyl : GL (Fin 2) (AdeleRing R K) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

variable (N : Ideal R)

def principalLevel : Subgroup (GL (Fin 2) (AdeleRing R K)) :=
  levelOne R K N ⊓ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom

theorem principalLevel_le_levelOne : principalLevel R K N ≤ levelOne R K N := inf_le_left

theorem mem_principalLevel_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ principalLevel R K N ↔
      g ∈ levelOne R K N ∧ g ∈ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom :=
  Iff.rfl

end NumberField.AdelicLevel

end
