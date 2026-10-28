/-
  The Petersson inner product on cusp forms, at level `Γ₀(N)` and for an arbitrary
  `Γ ≤ SL(2, ℤ)`.

  For cusp forms `f g` of weight `k`, `peterssonIntegrandOf Γ f g` is the pointwise
  density `UpperHalfPlane.petersson k (f ∣[k] q⁻¹) (g ∣[k] q⁻¹)` summed over the
  cosets `q : SL(2, ℤ) ⧸ Γ`, and `peterssonOf Γ f g` is its integral over the
  standard fundamental domain `𝒟 = ModularGroup.fd`. The `Γ₀(N)` pair
  `peterssonIntegrand`/`petersson` is the same construction at `Γ = Γ₀(N)`, and the
  `_gamma0` `rfl` lemmas identify the two. These are the definition layer the
  period/leaf rows consume.

  Transcribed verbatim from `Definitions/Def_CuspForm_Petersson.lean` (pinned
  `aa2d8b3`, 30 lines, its 3 declarations) and the `CuspForm` section of
  `Definitions/Def_ModularCurve_PeriodOf.lean` (132 lines; the `CuspForm` section
  `:108-130`, its 5 declarations). The pin's `Period` section of the latter file is
  the port's `ModularForms/EichlerShimura/PeriodOf.lean`; this module is the home
  of that file's `CuspForm` section, which its header records as deferred.
  Mathlib-only: `UpperHalfPlane.petersson` is mathlib's pointwise density
  (`Mathlib/NumberTheory/ModularForms/Petersson.lean`) and `ModularGroup.fd` the
  fundamental domain (`Mathlib/NumberTheory/Modular.lean`); nothing is restated.

  The port's `ModularForms/Analytic/Petersson.lean` is a *different* pin module
  (`Def_CuspForm_PeterssonOn.lean`): its `peterssonOn` takes plain functions and
  explicit `Γ k`, whereas the `…Of` pair here is the `CuspForm`-typed general-level
  form of the pin's own `Def_ModularCurve_PeriodOf.lean`.

  spec-pin: Definitions/Def_CuspForm_Petersson.lean
  spec-pin: Definitions/Def_ModularCurve_PeriodOf.lean
-/
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

section Gamma0

variable {N : ℕ} {k : ℤ}

/-- The pointwise Petersson density of `f` and `g` summed over the cosets of `Γ₀(N)`
in `SL(2, ℤ)`. -/
def peterssonIntegrand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (⇑g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

/-- The Petersson inner product of two `Γ₀(N)`-cusp forms: integrate the coset-summed
density over the standard fundamental domain. -/
def petersson (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd) (peterssonIntegrand f g)

theorem petersson_def (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    petersson f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonIntegrand f g) := rfl

end Gamma0

section General

variable (Γ : Subgroup SL(2, ℤ)) {k : ℤ}

/-- The pointwise Petersson density of `f` and `g` summed over the cosets of an
arbitrary `Γ ≤ SL(2, ℤ)`. -/
def peterssonIntegrandOf (f g : CuspForm Γ k) (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (⇑g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

/-- The Petersson inner product of two `Γ`-cusp forms. -/
def peterssonOf (f g : CuspForm Γ k) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd) (peterssonIntegrandOf Γ f g)

theorem peterssonOf_def (f g : CuspForm Γ k) :
    peterssonOf Γ f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonIntegrandOf Γ f g) := rfl

theorem peterssonIntegrandOf_gamma0 {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    peterssonIntegrandOf (CongruenceSubgroup.Gamma0 N) f g = peterssonIntegrand f g := rfl

theorem peterssonOf_gamma0 {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    peterssonOf (CongruenceSubgroup.Gamma0 N) f g = petersson f g := rfl

end General

end CuspForm

end
