/-
  Cross-module wire test for the `ModularCurve.Period` API and the
  equivariant-primitive headline.

  A `spec/` probe, not a library module. Four executed zones: the
  `IsEquivariantPrimitive` vocabulary, the `Γ₀(N)` period lattice, the general
  `periodOf`/`periodMapOf` layer, and the headline. The headline is applied in
  hypothesis form (no concrete cusp form is available to instantiate it), while
  the vocabulary and lattice zones are discharged concretely.
-/
import FLTForHuman.ModularForms.EichlerShimura.ExistsEquivariantPrimitive

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open UpperHalfPlane

namespace ModularCurvePeriodConsumer

-- Zone 1: the `ModularCurve.Period` vocabulary. A constant function is an
-- equivariant primitive with zero periods.
example (Γ : Subgroup SL(2, ℤ)) (c : ℂ) :
    ModularCurve.Period.IsEquivariantPrimitive Γ (fun _ : ℍ => c) :=
  fun _ => ⟨0, fun _ => by simp⟩

example (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)
    (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F) (γ : Γ) (z : ℍ) :
    F ((γ : SL(2, ℤ)) • z) - F z = hF.period γ :=
  hF.sub_eq_period γ z

-- Zone 2: the `Γ₀(N)` period lattice is spanned by the periods.
example (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    ModularCurve.period N γ ∈ ModularCurve.periodLattice N :=
  ModularCurve.period_mem_periodLattice N γ

-- Zone 3: the general-level period lattice and the period map chosen from an
-- equivariant primitive.
example (Γ : Subgroup SL(2, ℤ)) (γ : Γ) :
    ModularCurve.periodOf Γ γ ∈ ModularCurve.periodLatticeOf Γ :=
  ModularCurve.periodOf_mem_periodLatticeOf Γ γ

example (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) {F : ℍ → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : ModularCurve.HasEquivariantPrimitiveOf Γ f F₀),
      ModularCurve.periodMapOf Γ f = h₀.2.2.1.periodHom :=
  ModularCurve.periodMapOf_def Γ f hF

-- Zone 4: the headline, applied in hypothesis form.
#check @ModularCurve.exists_hasEquivariantPrimitiveOf
example (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : CuspForm Γ 2) :
    ∃ F : ℍ → ℂ, ModularCurve.HasEquivariantPrimitiveOf Γ f F :=
  ModularCurve.exists_hasEquivariantPrimitiveOf Γ f

end ModularCurvePeriodConsumer

end
