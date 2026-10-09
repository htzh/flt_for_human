/-
  The period map of a cusp form lands in the parabolic cocycles.

  `periodMapOf Γ f` is the homomorphism `Γ →+ ℂ` sending `γ` to the period of an
  equivariant primitive of `f` along `I → γ • I`; `Period.parabolicHoms ℂ Γ ℂ`
  is the submodule of those homomorphisms that vanish on the trace-`±2`
  (parabolic) elements. Every parabolic `γ ∈ SL(2, ℤ)` is conjugate to a power of
  `T` (`ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four`), and along such a
  conjugate the period is a constant difference of a translate of the primitive
  whose two ends both tend to the same limit at `i∞`; hence it is `0`.

  Transcribed from
  `P2M/Sol/S_ModularCurve_periodMapOf_mem_parabolicHoms.lean` (pinned `aa2d8b3`,
  91 lines); the statement is the `Theorems/` wrapper's. Every helper is
  `private`, so the checker diffs only the headline.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_periodMapOf_mem_parabolicHoms.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_periodMapOf_mem_parabolicHoms.lean>
-/
import FLTForHuman.ModularForms.EichlerShimura.PeriodOf
import FLTForHuman.ModularForms.ModularGroup

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

open UpperHalfPlane Filter Topology

namespace ModularCurve

namespace PeriodMapParabolicOf

open ModularCurve.Period

private theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

private theorem const_eq_zero_of_tendsto_sub {α : Type*} {l : Filter α} [l.NeBot]
    {g h : α → ℂ} {L c : ℂ} (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hc : ∀ a, g a - h a = c) : c = 0 := by
  have hsub : Tendsto (fun a => g a - h a) l (𝓝 (L - L)) := hg.sub hh
  rw [sub_self] at hsub
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun a => (hc a).symm) hsub

private theorem period_eq_zero {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F) (δ : SL(2, ℤ)) {L : ℂ}
    (hlim : Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) (n : ℤ) (ε : SL(2, ℤ))
    (hε : ε = 1 ∨ ε = -1) (hγ : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ) :
    hF.period ⟨_, hγ⟩ = 0 := by

  have hεact : ∀ z : ℍ, (ε : SL(2, ℤ)) • z = z := by
    intro z
    rcases hε with rfl | rfl
    · exact one_smul _ z
    · ext1
      rw [UpperHalfPlane.specialLinearGroup_apply]
      simp
  have hkey : ∀ w : ℍ, (ε * (δ * ModularGroup.T ^ n * δ⁻¹) : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)
      = δ • (ModularGroup.T ^ n • w) := by
    intro w
    rw [mul_smul, hεact, ← mul_smul, ← mul_smul]
    congr 1
    group
  have hc' : ∀ w : ℍ, F (δ • (ModularGroup.T ^ n • w)) - F (δ • w) = hF.period ⟨_, hγ⟩ := by
    intro w
    rw [← hkey]
    exact hF.sub_eq_period ⟨_, hγ⟩ (δ • w)
  refine const_eq_zero_of_tendsto_sub
    (g := fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
    (h := fun w : ℍ => F (δ • w)) (L := L) ?_ hlim hc'
  have hfun : (fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
      = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => ((n : ℤ) : ℝ) +ᵥ w := by
    funext w
    simp only [Function.comp_apply, UpperHalfPlane.modular_T_zpow_smul]
  rw [hfun]
  exact hlim.comp (tendsto_vadd_atImInfty ((n : ℤ) : ℝ))

private theorem isParabolicHom_periodHom {Γ : Subgroup SL(2, ℤ)} {f : CuspForm Γ 2} {F : ℍ → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) :
    IsParabolicHom Γ hF.2.2.1.periodHom := by
  intro γ hγ
  obtain ⟨ε, δ, n, hε, hγeq⟩ :=
    ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
  obtain ⟨L, hL⟩ := hF.2.2.2 δ
  have hmem : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ := by rw [← hγeq]; exact γ.2
  have hγ' : γ = ⟨_, hmem⟩ := Subtype.ext hγeq
  rw [IsEquivariantPrimitive.periodHom_apply, hγ']
  exact period_eq_zero hF.2.2.1 δ hL n ε hε hmem

private theorem main (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ parabolicHoms ℂ Γ ℂ := by
  classical
  by_cases h : ∃ F : ℍ → ℂ, ModularCurve.HasEquivariantPrimitiveOf Γ f F
  · obtain ⟨F, hF⟩ := h
    obtain ⟨F₀, h₀, hp⟩ := ModularCurve.periodMapOf_def Γ f hF
    rw [hp]
    exact isParabolicHom_periodHom h₀
  · have : ModularCurve.periodMapOf Γ f = 0 := dite_eq_right h
    rw [this]
    exact Submodule.zero_mem _

end PeriodMapParabolicOf

/-- **The period map lands in the parabolic cocycles.** The pin's
`ModularCurve.periodMapOf_mem_parabolicHoms`, with the statement of the
`Theorems/` wrapper. -/
theorem periodMapOf_mem_parabolicHoms (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ ModularCurve.Period.parabolicHoms ℂ Γ ℂ :=
  PeriodMapParabolicOf.main Γ f

end ModularCurve

end
