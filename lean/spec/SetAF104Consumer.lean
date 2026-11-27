import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeProjector
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumDensity
import FLTForHuman.AutomorphicForm.Adelic.IwasawaQuotientIntegral
import FLTForHuman.ModularCurve.X1.GenusBound

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal NNReal InnerProductSpace

namespace SetAF104Consumer

/-! ## Zone 1 — the arch-type projector fixes a separating vector (orders A + B)

The two projector/density modules meet here: order B's separation row produces a level-invariant
`archCut tys` vector `ψ` that pairs nontrivially with a nonzero carrier vector `v`, and order A's
projector for the *same* `tys` then fixes it — so the pairing survives the projection. Deleting
either module breaks this theorem: `exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero`
is B's, `exists_idempotent_archTypeProjector` is A's. -/

theorem exists_archTypeProjector_fixes_a_separating_vector
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
      (E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      ψ ∈ archCutSubmodule F tys ∧ E.comp E = E ∧
        ⟪v, E (toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩)⟫_ℂ ≠ 0 := by
  obtain ⟨tys, _U, _hU, _hUo, _hUc, _hUint, ψ, hψ, hψarch, _hψinv, hinner⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
      (F := F) hΦ₀ σ ξ hσ v hv
  obtain ⟨E, hEidem, _hMmap, hEfix, _hEproduce, _hTccomm, _hgComm⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector
      (F := F) hΦ₀ σ ξ hσ tys
  exact ⟨tys, ψ, hψ, E, hψarch, hEidem, by rw [hEfix ψ hψ hψarch]; exact hinner⟩

/-! ## Zone 2 — the quotient measure's normalising constant at `K = ℚ` (order D)

Order D's Iwasawa row at the smallest number field: the Haar-quotient measure of
`rationalCentreUnipotent ℚ` is a *nonzero, finite* constant times the iterated Iwasawa integral, so in
particular that constant exists and is neither `0` nor `∞`. -/

theorem exists_quotientMeasure_constant_rat :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ := by
  obtain ⟨c, hc0, hctop, _⟩ :=
    AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
      (K := ℚ)
  exact ⟨c, hc0, hctop⟩

/-! ## Zone 3 — the `jq`-ramification bounds imply the genus inequality (order E)

Order E's two `X₁` rows compose: the three order bounds at a place `P` (`ord y ≤ 3`,
`ord (y - 1728) ≤ 2`, `ord (y - a) ≤ 1` for `a ∉ {0, 1728}`) are exactly the fibre-count input of the
Riemann–Hurwitz inequality, so both are consequences of the same `hy` and can be stated together. -/

theorem ord_bounds_and_genus_inequality
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a : AlgebraicClosure ℚ) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    P.ord y ≤ 3 ∧ P.ord (y - 1728) ≤ 2 ∧
      P.ord (y - algebraMap (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ :=
    ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
      M Γ hΓ y hy P
  exact ⟨h1, h2, h3 a ha0 ha1728⟩

end SetAF104Consumer
