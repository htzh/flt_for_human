/-
  SET-AF55B consumer: the cuspidal carrier's window, modulus and orthogonality.

  **The zone.** Five rows, hence five compositions, read off the three modules of the set:

  * `FLTForHuman/AutomorphicForm/Adelic/Cusp/CarrierWindowMonotonicity.lean`:
    `AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot` (B1) and
    `AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero`
    (B2);
  * `FLTForHuman/AutomorphicForm/Adelic/Cusp/ConstituentModulus.lean`:
    `AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` (B3) and
    `AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` (B4);
  * `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumOrthogonality.lean`:
    `AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant`
    (B5).

  **The readings.**

  * Zone B1. The window-monotonicity row is an inclusion of carriers. The consumer *executes* it
    at a concrete member — the composition that every consumer of the isotypic carrier performs:
    an isotypic cusp form square-integrable on the wider window is one on the narrower window, so
    membership transfers along `d₁ ≤ d₁'`.
  * Zone B2. The same reading for the `K`-finite carrier, whose hypothesis is a witness
    `φ ≠ 0` rather than the non-triviality of the carrier: membership in the wider carrier
    transfers to the narrower one.
  * Zone B3. The modulus row produces the exponent `σ`. The consumer spends it at a central
    element `z`: the archimedean size of the central character is the idèle norm to the power
    `σ` — the shape in which the modulus enters the (non-)vanishing estimates.
  * Zone B4. The test-factor row produces local constancy and compact support. The consumer
    reads the support half as `tsupport`-membership: outside the compact `tsupport` of `ff`
    the twisted factor vanishes, so it is a test factor for the finite places.
  * Zone B5. The orthogonality row kills a functional on one element. The consumer spends it
    as a kernel statement: the intersection of the cuspidal subcarrier with the orthogonal
    complement of the level subcarrier lies in the kernel of the lifted operator — the form in
    which the row feeds the spectral decomposition.

  Statement-level data (`hcov`, `hΦ₀`, `hT`, `V`, `hV`) cannot be instantiated concretely —
  they are properties of an arbitrary covering, slab fundamental domain, lifted operator and
  cuspidal constituent — so they enter in hypothesis form, which is the legitimate reading for
  these rows.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CarrierWindowMonotonicity
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentModulus
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumOrthogonality

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm.SetAF55BConsumer

/-! ### Zones B1 and B2: the window is monotone in `d₁` -/

section window

variable (F : Type) [Field F] [NumberField F]
variable (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
variable (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)

/-- **Zone B1.** The isotypic carrier at the wider window is contained in the one at the
narrower window, spent on a member: whatever is isotypic-cuspidal on `[d₁', d₂)` is
isotypic-cuspidal on `[d₁, d₂)`. -/
theorem consumer_B1_membership
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hne : isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ ≠ ⊥)
    {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : ψ ∈ isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) :
    ψ ∈ isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ :=
  isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot F c u d₁ d₂ d₁' T hc hle hd₁' hlt
    hcov ξ N S Ψ hne hψ

/-- **Zone B2.** The same reading for the `K`-finite carrier, whose hypothesis is a witness
`φ ≠ 0` of the wider carrier's non-triviality. -/
theorem consumer_B2_membership
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hne : ∃ φ : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ ∧ Continuous φ ∧ φ ≠ 0)
    {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : ψ ∈ cuspKFiniteSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ) :
    ψ ∈ cuspKFiniteSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ :=
  CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero F c u d₁ d₂
    d₁' T hc hle hd₁' hlt hcov ξ hne hψ

end window

/-! ### Zone B3: the modulus of a cusp constituent -/

section modulus

variable (F : Type) [Field F] [NumberField F]
variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))

/-- **Zone B3.** The modulus exponent of a cusp constituent, spent at a central element: the
archimedean size of the central character at `z` is the idèle norm of `z` to the power `σ`. -/
theorem consumer_B3_modulus_at
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) :
    ∃ σ : ℝ,
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ σ := by
  obtain ⟨σ, hσ⟩ :=
    CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent F c u d₁ d₂ T ξ V hV
  exact ⟨σ, hσ z⟩

end modulus

/-! ### Zone B4: the conjugate-inverse test factor, read at its support -/

section testfactor

variable (F : Type) [Field F] [NumberField F]

/-- **Zone B4.** The twisted finite test factor, read as compact support: outside the compact
`tsupport` of `ff` the factor `b ↦ conj (ff b⁻¹) * ‖det b‖ ^ (-σ)` vanishes identically. -/
theorem consumer_B4_tsupport (σ : ℝ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hff : IsFinTestFactor F ff) :
    ∃ K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)), IsCompact K ∧
      ∀ b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), b ∉ K →
        conj (ff b⁻¹) *
          ((NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ) = 0 := by
  let G : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ := fun b => conj (ff b⁻¹) *
    ((NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ)
  have h : IsFinTestFactor F G :=
    CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ ff hff
  exact ⟨tsupport G, h.2, fun b hb => image_eq_zero_of_notMem_tsupport (f := G) hb⟩

end testfactor

/-! ### Zone B5: orthogonality, read as a kernel statement -/

section orthogonality

variable (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
variable (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
variable (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)

/-- **Zone B5.** The orthogonality row as a kernel statement: the cuspidal subcarrier meets the
orthogonal complement of the level subcarrier inside the kernel of the lift. -/
theorem consumer_B5_le_ker
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, f (x * u) = f x)
    (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T) :
    cuspSubcarrier F hΦ₀ σ ξ ⊓ (cuspLevelSubcarrier F hΦ₀ σ ξ N)ᗮ ≤
      LinearMap.ker (T : Carrier F Φ₀ σ →ₗ[ℂ] Carrier F Φ₀ σ) := by
  intro v hv
  exact
    CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
      F hΦ₀ σ ξ N f hf hfU T hT v hv.1 hv.2

end orthogonality

end AutomorphicForm.SetAF55BConsumer
