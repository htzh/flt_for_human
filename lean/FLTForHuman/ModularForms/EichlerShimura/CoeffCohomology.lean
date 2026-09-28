/-
Copyright (c) 2026 FLT-for-human contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT-for-human contributors
-/

import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel

/-!
# Coefficient cohomology of a representation, parabolic classes

For a group `G`, a commutative ring `K` and a `K`-representation `ρ` on `V`,
this module packages the coefficient cohomology that the Eichler–Shimura period
map lands in:

* `coeffCocycles ρ` — the `K`-submodule of `G → V` of `1`-cocycles
  `z (g * h) = z g + ρ g (z h)`;
* `coeffCoboundaryMap ρ` / `coeffCoboundaries ρ` — the coboundaries
  `v ↦ (g ↦ ρ g v - v)` and their range;
* `IsParabolicCocycle ρ z` — for `Γ ≤ SL(2, ℤ)`, the condition that a cocycle
  evaluated at every parabolic `γ` (trace squared `4`) lies in the range of
  `ρ γ - 1`;
* `coeffParabolicCocycles ρ` — the parabolic cocycles, containing the
  coboundaries;
* `coeffH1par ρ` — the parabolic first cohomology
  `Z¹_par / B¹`, with its additive group and `K`-module structure, the
  quotient map `coeffH1parMk`, its surjectivity and its kernel description.

The target of the period map is `coeffH1par ((binaryFormRepSL ℂ n).comp (Γ_0 N).subtype)`.

## FLT source and pin

Pin `aa2d8b3`: `Definitions/Def_Gamma0CoeffCohomology.lean`, the `Cocycles` and
`Parabolic` blocks (lines 9–122),
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Gamma0CoeffCohomology.lean#L9-L122>.
Every declaration is the pin's verbatim, names and signatures included.

**Omitted:** the pin's `Hecke` block (`coeffHeckeFun`, `coeffHeckeFun_apply`,
`coeffHeckeFun_trivial`, lines 124–151) and its
`Def_Gamma0HeckeOperatorHom` import — Hecke equivariance is outside this cone
(topic §1: "Nothing here uses `coeffHeckeFun`"). The pin's bare `import Mathlib`
is replaced by specific imports.

## What this module assumes

Mathlib only: `Representation` for the coefficient system,
`Submodule`/`LinearMap.range`/`Submodule.Quotient`/`Submodule.mkQ` for the
cohomology, and `Matrix.SpecialLinearGroup` for `SL(2, ℤ)` and its trace.
Nothing from other `FLTForHuman` modules.

## Adaptation notes (mathlib `v4.34.0`)

None in the statements; the proofs are the pin's. The pin's `open
CongruenceSubgroup` is dropped (unused here).
-/

open scoped MatrixGroups

namespace HeckeEis

section Cocycles

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The `K`-submodule of `1`-cocycles of the representation `ρ`. -/
def coeffCocycles (ρ : Representation K G V) : Submodule K (G → V) where
  carrier := {z | ∀ g h : G, z (g * h) = z g + ρ g (z h)}
  zero_mem' := by
    intro g h
    simp
  add_mem' := by
    intro z w hz hw g h
    simp only [Pi.add_apply, hz g h, hw g h, map_add]
    abel
  smul_mem' := by
    intro c z hz g h
    simp only [Pi.smul_apply, hz g h, smul_add, map_smul]

theorem mem_coeffCocycles_iff (ρ : Representation K G V) (z : G → V) :
    z ∈ coeffCocycles ρ ↔ ∀ g h : G, z (g * h) = z g + ρ g (z h) :=
  Iff.rfl

/-- The coboundary map `v ↦ (g ↦ ρ g v - v)`. -/
def coeffCoboundaryMap (ρ : Representation K G V) : V →ₗ[K] (G → V) where
  toFun v := fun g => ρ g v - v
  map_add' v w := by
    ext g
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' c v := by
    ext g
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

@[simp]
theorem coeffCoboundaryMap_apply (ρ : Representation K G V) (v : V) (g : G) :
    coeffCoboundaryMap ρ v g = ρ g v - v :=
  rfl

/-- The `K`-submodule of coboundaries, the range of `coeffCoboundaryMap`. -/
def coeffCoboundaries (ρ : Representation K G V) : Submodule K (G → V) :=
  LinearMap.range (coeffCoboundaryMap ρ)

theorem mem_coeffCoboundaries_iff (ρ : Representation K G V) (z : G → V) :
    z ∈ coeffCoboundaries ρ ↔ ∃ v : V, (fun g => ρ g v - v) = z := by
  simp [coeffCoboundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

theorem coeffCoboundaries_le_coeffCocycles (ρ : Representation K G V) :
    coeffCoboundaries ρ ≤ coeffCocycles ρ := by
  rintro z ⟨v, rfl⟩ g h
  show ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
  rw [map_mul, map_sub]
  simp only [Module.End.mul_apply]
  abel

end Cocycles

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

/-- A cocycle is parabolic if its value at every parabolic `γ`
(trace squared `4`) lies in the range of `ρ γ - 1`. -/
def IsParabolicCocycle (ρ : Representation K Γ V) (z : Γ → V) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
    z γ ∈ LinearMap.range (ρ γ - 1)

/-- The `K`-submodule of parabolic cocycles. -/
def coeffParabolicCocycles (ρ : Representation K Γ V) : Submodule K (Γ → V) where
  carrier := {z | z ∈ coeffCocycles ρ ∧ IsParabolicCocycle ρ z}
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => by simp⟩
  add_mem' := by
    rintro z w ⟨hz, hz'⟩ ⟨hw, hw'⟩
    exact ⟨Submodule.add_mem _ hz hw, fun γ hγ => Submodule.add_mem _ (hz' γ hγ) (hw' γ hγ)⟩
  smul_mem' := by
    rintro c z ⟨hz, hz'⟩
    exact ⟨Submodule.smul_mem _ c hz, fun γ hγ => Submodule.smul_mem _ c (hz' γ hγ)⟩

theorem mem_coeffParabolicCocycles_iff (ρ : Representation K Γ V) (z : Γ → V) :
    z ∈ coeffParabolicCocycles ρ ↔ z ∈ coeffCocycles ρ ∧ IsParabolicCocycle ρ z :=
  Iff.rfl

theorem coeffParabolicCocycles_le_coeffCocycles (ρ : Representation K Γ V) :
    coeffParabolicCocycles ρ ≤ coeffCocycles ρ :=
  fun _ hz => hz.1

theorem coeffCoboundaries_le_coeffParabolicCocycles (ρ : Representation K Γ V) :
    coeffCoboundaries ρ ≤ coeffParabolicCocycles ρ := by
  intro z hz
  refine ⟨coeffCoboundaries_le_coeffCocycles ρ hz, fun γ _ => ?_⟩
  obtain ⟨v, rfl⟩ := hz
  exact ⟨v, by simp [coeffCoboundaryMap]⟩

/-- The parabolic first cohomology `Z¹_par / B¹`. -/
def coeffH1par (ρ : Representation K Γ V) : Type _ :=
  ↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype

instance instAddCommGroupCoeffH1par (ρ : Representation K Γ V) : AddCommGroup (coeffH1par ρ) :=
  inferInstanceAs (AddCommGroup
    (↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype))

instance instModuleCoeffH1par (ρ : Representation K Γ V) : Module K (coeffH1par ρ) :=
  inferInstanceAs (Module K
    (↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype))

/-- The quotient map from parabolic cocycles onto `coeffH1par ρ`. -/
def coeffH1parMk (ρ : Representation K Γ V) : ↥(coeffParabolicCocycles ρ) →ₗ[K] coeffH1par ρ :=
  ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype).mkQ

theorem coeffH1parMk_surjective (ρ : Representation K Γ V) :
    Function.Surjective (coeffH1parMk ρ) :=
  Submodule.mkQ_surjective _

theorem coeffH1parMk_eq_zero_iff (ρ : Representation K Γ V) (z : ↥(coeffParabolicCocycles ρ)) :
    coeffH1parMk ρ z = 0 ↔ (z : Γ → V) ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

end Parabolic

end HeckeEis
