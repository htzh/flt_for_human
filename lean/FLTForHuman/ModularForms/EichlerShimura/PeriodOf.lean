/-
  Periods of an equivariant primitive: the general-level API.

  For a subgroup `Γ ≤ SL(2, ℤ)`, `periodOf` is the period of an equivariant
  primitive along `I → γ • I`, `periodLatticeOf` its `ℤ`-span,
  `HasEquivariantPrimitiveOf` the bundled predicate (primitive, vanishing at
  `∞`, equivariant, bounded at every cusp), and `periodMapOf` the resulting
  period homomorphism, chosen from the predicate by `Classical.choose` and `0`
  when no primitive exists. These generalise the `Γ₀(N)` definitions of
  `PeriodIntegral.lean` by the `_gamma0` `rfl` lemmas.

  Transcribed verbatim from `Definitions/Def_ModularCurve_PeriodOf.lean` (pinned
  `aa2d8b3`, 132 lines), the pin's `Period` section. The pin's `CuspForm`
  section of the same file (the Petersson inner product,
  `peterssonIntegrandOf`/`peterssonOf`) is **not** ported: none of the 28
  consumers of `ModularCurve.exists_hasEquivariantPrimitiveOf` reaches it.
-/
import FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive
import FLTForHuman.ModularForms.EichlerShimura.PeriodIntegral
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter Topology

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Period

variable (Γ : Subgroup SL(2, ℤ))

def periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (t : ℝ) : ℂ :=
  f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)

theorem continuous_periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    Continuous (periodIntegrandOf Γ τ₀ τ₁ f) :=
  ((f.holo'.continuous).comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const

theorem intervalIntegrable_periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (a b : ℝ) :
    IntervalIntegrable (periodIntegrandOf Γ τ₀ τ₁ f) MeasureTheory.volume a b :=
  (continuous_periodIntegrandOf Γ τ₀ τ₁ f).intervalIntegrable a b

theorem periodIntegrandOf_add (τ₀ τ₁ : ℍ) (f g : CuspForm Γ 2) :
    periodIntegrandOf Γ τ₀ τ₁ (f + g) = periodIntegrandOf Γ τ₀ τ₁ f + periodIntegrandOf Γ τ₀ τ₁ g := by
  funext t
  simp [periodIntegrandOf, add_mul]

theorem periodIntegrandOf_smul (τ₀ τ₁ : ℍ) (c : ℂ) (f : CuspForm Γ 2) :
    periodIntegrandOf Γ τ₀ τ₁ (c • f) = fun t => c * periodIntegrandOf Γ τ₀ τ₁ f t := by
  funext t
  simp [periodIntegrandOf, mul_assoc]

def periodAlongOf (τ₀ τ₁ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) where
  toFun f := ∫ t in (0 : ℝ)..1, periodIntegrandOf Γ τ₀ τ₁ f t
  map_add' f g := by
    rw [periodIntegrandOf_add]
    exact intervalIntegral.integral_add (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1)
      (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ g 0 1)
  map_smul' c f := by
    rw [periodIntegrandOf_smul, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _

theorem periodAlongOf_apply (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    periodAlongOf Γ τ₀ τ₁ f = ∫ t in (0 : ℝ)..1, f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) :=
  rfl

def periodOf (γ : Γ) : Module.Dual ℂ (CuspForm Γ 2) :=
  periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)

theorem periodOf_apply (γ : Γ) (f : CuspForm Γ 2) :
    periodOf Γ γ f =
      ∫ t in (0 : ℝ)..1, f (segmentPath UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) t) *
        ((((γ : SL(2, ℤ)) • UpperHalfPlane.I : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)) :=
  rfl

def periodLatticeOf : Submodule ℤ (Module.Dual ℂ (CuspForm Γ 2)) :=
  Submodule.span ℤ (Set.range (periodOf Γ))

theorem periodOf_mem_periodLatticeOf (γ : Γ) : periodOf Γ γ ∈ periodLatticeOf Γ :=
  Submodule.subset_span (Set.mem_range_self γ)

def HasEquivariantPrimitiveOf (f : CuspForm Γ 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    Period.IsEquivariantPrimitive Γ F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

def periodMapOf (f : CuspForm Γ 2) : Additive Γ →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F then h.choose_spec.2.2.1.periodHom else 0

theorem periodMapOf_def (f : CuspForm Γ 2) {F : ℍ → ℂ} (hF : HasEquivariantPrimitiveOf Γ f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitiveOf Γ f F₀), periodMapOf Γ f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dite_eq_left h⟩

theorem periodAlongOf_gamma0 (N : ℕ) (τ₀ τ₁ : ℍ) :
    periodAlongOf (CongruenceSubgroup.Gamma0 N) τ₀ τ₁ = periodAlong N τ₀ τ₁ := rfl

theorem periodOf_gamma0 (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    periodOf (CongruenceSubgroup.Gamma0 N) γ = period N γ := rfl

theorem periodLatticeOf_gamma0 (N : ℕ) :
    periodLatticeOf (CongruenceSubgroup.Gamma0 N) = periodLattice N := rfl

theorem hasEquivariantPrimitiveOf_gamma0_iff (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (F : ℍ → ℂ) : HasEquivariantPrimitiveOf (CongruenceSubgroup.Gamma0 N) f F ↔
      HasEquivariantPrimitive N f F := Iff.rfl

theorem periodMapOf_gamma0 (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodMapOf (CongruenceSubgroup.Gamma0 N) f = periodMap N f := rfl

end Period

end ModularCurve

end
