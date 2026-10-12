/-
  The `LsXi` L²-space of adèlic functions with a central character.

  `IsLsXiFunction` collects the two invariance laws — left invariance under
  `GL₂(K)` and transformation by a central character `ξ` on a subgroup `Z` of the
  idèles — and `LsXiMember` adds square-integrability on a domain `D` of
  `GL₂(𝔸_K)`. `IsIdeleClassChar`/`IsUnitaryChar`/`SquaresToXi` are the character
  conditions on the central character that the automorphic theory imposes.

  `Definitions/Def_AutomorphicForm_AdelicLsXi.lean` mixes this with the base group
  vocabulary; the port splits it (playbook §3.1) and this module is the second
  half, transcribed verbatim from the pin (pinned `aa2d8b3`).
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsIdeleClassChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ u : Kˣ, χ (Units.map (algebraMap K (AdeleRing R K)) u) = 1

def IsUnitaryChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AdeleRing R K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def SquaresToXi (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ z : Z, χ (z : (AdeleRing R K)ˣ) ^ 2 = ξ z

variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)

structure IsLsXiFunction (φ : AdelicGL2 R K → ℂ) : Prop where
  left_invariant : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 R K),
    φ (globalPoints R K γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 R K),
    φ (centralScalar R K (z : (AdeleRing R K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g

theorem isLsXiFunction_zero : IsLsXiFunction R K Z ξ (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ => rfl, fun _ _ => by simp⟩

variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))

structure LsXiMember (φ : AdelicGL2 R K → ℂ) : Prop extends IsLsXiFunction R K Z ξ φ where
  memLp_two : MemLp φ 2 ((volume : Measure (AdelicGL2 R K)).restrict D)

theorem lsXiMember_zero : LsXiMember R K Z ξ D (fun _ => (0 : ℂ)) :=
  ⟨isLsXiFunction_zero R K Z ξ, MemLp.zero'⟩

end AutomorphicForm

end
