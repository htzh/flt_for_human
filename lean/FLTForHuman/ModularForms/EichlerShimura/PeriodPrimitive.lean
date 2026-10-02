/-
  The `ModularCurve.Period` vocabulary: equivariant primitives and their periods.

  A function `F : ℍ → ℂ` is an **equivariant primitive** for a subgroup `Γ` when
  the obstruction to `Γ`-invariance is a constant per group element,
  `F (γ • z) - F z = c γ`; the constant `period` is a group homomorphism
  `Γ → ℂ` (`periodHom`). A homomorphism `Γ →+ A` is **parabolic** when it kills
  the trace-`±2` (parabolic) elements — the condition the cuspidal part of the
  period map satisfies.

  Transcribed verbatim from `Definitions/Def_ModularCurve_PeriodMap.lean`
  (pinned `aa2d8b3`, 81 lines) and `Definitions/Def_ModularCurve_PeriodMapBundled.lean`
  (30 lines): the `IsEquivariantPrimitive`/`IsParabolicHom`/`parabolicHoms`
  vocabulary and the `Γ₀(N)` bundled `HasEquivariantPrimitive`. Mathlib-only.

  This is the vocabulary the pin's `ModularCurve.Period` API is built on; the
  `periodOf`/`periodLatticeOf`/`periodMapOf` layer is `PeriodOf.lean`, and the
  path-integral `period`/`periodLattice` on `Γ₀(N)` is `PeriodIntegral.lean`.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Algebra.Module.Hom
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

namespace ModularCurve.Period

open UpperHalfPlane

open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)

/-- `F` is an equivariant primitive for `Γ`: its failure to be `Γ`-invariant is
a constant depending only on the group element. -/
def IsEquivariantPrimitive : Prop :=
  ∀ γ : Γ, ∃ c : ℂ, ∀ z : ℍ, F ((γ : SL(2, ℤ)) • z) - F z = c

/-- A homomorphism `Γ →+ A` is parabolic when it kills every element whose
matrix trace squares to `4` (the parabolic elements). -/
def IsParabolicHom {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0

variable {Γ F}

namespace IsEquivariantPrimitive

noncomputable def period (_hF : IsEquivariantPrimitive Γ F) (γ : Γ) : ℂ :=
  F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I

theorem sub_eq_period (hF : IsEquivariantPrimitive Γ F) (γ : Γ) (z : ℍ) :
    F ((γ : SL(2, ℤ)) • z) - F z = hF.period γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [hc z, period, hc UpperHalfPlane.I]

@[simp]
theorem period_one (hF : IsEquivariantPrimitive Γ F) : hF.period 1 = 0 := by
  have h := hF.sub_eq_period 1 UpperHalfPlane.I
  simpa using h.symm

theorem period_mul (hF : IsEquivariantPrimitive Γ F) (γ δ : Γ) :
    hF.period (γ * δ) = hF.period γ + hF.period δ := by
  have h1 := hF.sub_eq_period (γ * δ) UpperHalfPlane.I
  have h2 := hF.sub_eq_period γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h3 := hF.sub_eq_period δ UpperHalfPlane.I
  have hsmul : ((γ * δ : Γ) : SL(2, ℤ)) • UpperHalfPlane.I
      = (γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [← mul_smul]; rfl
  rw [hsmul] at h1
  linear_combination h2 + h3 - h1

noncomputable def periodHom (hF : IsEquivariantPrimitive Γ F) : Additive Γ →+ ℂ where
  toFun γ := hF.period (Additive.toMul γ)
  map_zero' := hF.period_one
  map_add' γ δ := hF.period_mul (Additive.toMul γ) (Additive.toMul δ)

@[simp]
theorem periodHom_apply (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    hF.periodHom (Additive.ofMul γ) = hF.period γ :=
  rfl

end IsEquivariantPrimitive

section ParabolicHoms

variable (R : Type*) [Semiring R] (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A] [Module R A]

def parabolicHoms : Submodule R (Additive Γ →+ A) where
  carrier := {φ | IsParabolicHom Γ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ (Additive.ofMul γ) + ψ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, smul_zero]

variable {R Γ A}

theorem mem_parabolicHoms_iff {φ : Additive Γ →+ A} : φ ∈ parabolicHoms R Γ A ↔ IsParabolicHom Γ φ :=
  Iff.rfl

end ParabolicHoms

end ModularCurve.Period

namespace ModularCurve

open UpperHalfPlane CongruenceSubgroup Filter Topology Period

open scoped MatrixGroups

/-- The `Γ₀(N)` bundled form of `Period.IsEquivariantPrimitive`, together with
the primitive and cusp-vanishing conditions. -/
def HasEquivariantPrimitive (N : ℕ) (f : CuspForm (Gamma0 N) 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    IsEquivariantPrimitive (Gamma0 N) F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

noncomputable def periodMap (N : ℕ) (f : CuspForm (Gamma0 N) 2) : Additive (Gamma0 N) →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F then h.choose_spec.2.2.1.periodHom else 0

theorem periodMap_def (N : ℕ) (f : CuspForm (Gamma0 N) 2) {F : ℍ → ℂ}
    (hF : HasEquivariantPrimitive N f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitive N f F₀), periodMap N f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dite_eq_left h⟩

end ModularCurve

end
