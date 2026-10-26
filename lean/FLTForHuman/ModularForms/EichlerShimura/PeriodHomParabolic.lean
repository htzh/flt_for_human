/-
  The period homomorphism of an equivariant primitive is parabolic.

  An equivariant primitive `F` for `Γ` has periods `periodHom γ = F (γ • z) - F z`; if in
  addition `F` has a finite limit along every `SL(2, ℤ)`-translate of the cusp
  (`hlim` below), then `periodHom` kills every parabolic element — i.e. it is a
  `ModularCurve.Period.IsParabolicHom`. The proof is the classification of parabolic
  elements: `γ` of trace `±2` is `ε * (δ * T ^ n * δ⁻¹)` with `ε = ±1`, and along that
  conjugate both ends of the translate tend to the same limit while `F` differs by the
  constant period, so the period vanishes.

  Transcribed from `Theorems/Thm_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom.lean`
  (pinned `aa2d8b3`, 21 lines of proof over the ported vocabulary of
  `ModularForms/EichlerShimura/PeriodPrimitive.lean`). The one non-mathlib input is
  `ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four`.

  This node was missing from the port: `ModularCurve/Period/ParabolicHoms.lean` keeps only
  the `Γ₀(N)`-bundled special case, `private`, so it is not on the public API. It is also
  why `frontier` reported the node's consumers as satisfied — a `private` declaration
  satisfies the last-name tier.

  spec-pin: Theorems/Thm_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom.lean
  spec-pin: P2M/Sol/S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom.lean
-/
import FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive
import FLTForHuman.ModularForms.ModularGroup
import FLTForHuman.ModularCurve.Period.ParabolicHoms
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

set_option autoImplicit false

noncomputable section

namespace ModularCurve.Period

open UpperHalfPlane Filter Topology

open scoped MatrixGroups Real Topology

/-- **The period map of an equivariant primitive with cusp limits is parabolic.**
Every parabolic element is conjugate to a power of `T` (the ported classification
`ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four`); along a conjugate of `T ^ n`
the primitive differs by that constant while both ends of the translate tend to the same
cusp limit, so the period is `0`. -/
theorem IsEquivariantPrimitive.isParabolicHom_periodHom {Γ : Subgroup SL(2, ℤ)}
    {F : UpperHalfPlane → ℂ} (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Filter.Tendsto (fun w : UpperHalfPlane => F (δ • w)) UpperHalfPlane.atImInfty (nhds L)) :
    ModularCurve.Period.IsParabolicHom Γ hF.periodHom := by
  intro γ hγ
  rw [IsEquivariantPrimitive.periodHom_apply]
  obtain ⟨ε, δ, n, hε, hγeq⟩ :=
    ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
  obtain ⟨L, hL⟩ := hlim δ
  have hmem : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ := hγeq ▸ γ.2
  have hsub : γ = ⟨ε * (δ * ModularGroup.T ^ n * δ⁻¹), hmem⟩ := Subtype.ext hγeq
  rw [hsub]
  exact PeriodMapParabolicOf.period_eq_zero hF δ hL n ε hε hmem


end ModularCurve.Period
