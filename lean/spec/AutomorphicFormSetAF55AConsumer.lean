/-
  SET-AF55A consumer: the archimedean cut's closure calculus.

  **The zone.** Eight rows, hence eight compositions, read off the five modules of the set:

  * `FLTForHuman/AutomorphicForm/Adelic/LeftCasimirTestFn.lean`:
    `AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite`
    (A1), `AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite`
    (A2) and
    `AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite`
    (A7);
  * `FLTForHuman/AutomorphicForm/Adelic/TestFnInvariance.lean`:
    `AutomorphicForm.isFactorizableTestFn_comp_inv_mul` (A3);
  * `FLTForHuman/AutomorphicForm/Adelic/TestFactorIntegral.lean`:
    `AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` (A4) and
    `AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` (A5);
  * `FLTForHuman/AutomorphicForm/Adelic/ArchApproximation.lean`:
    `AutomorphicForm.exists_linearMap_archCutProjector` (A6);
  * `FLTForHuman/AutomorphicForm/Adelic/Cusp/ConstituentCharCut.lean`:
    `AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` (A8).

  **The readings.**

  * Zone A1. The Casimir dictionary at a real place: the consumer *executes* it by extracting the
    test factor `β` and its two properties together with the membership of the Casimir in
    `levelInvariantSubmodule ⊓ archCutSubmodule` — the shape in which the cusp constituent's rows
    consume the row.
  * Zone A2. The same at a complex place, where the row produces both `β` (from `archCasimirAtComplex`)
    and its conjugate `βb` (from `archCasimirBarAtComplex`); the consumer carries both, with both
    memberships, since a constituent needs `del` and `delbar` together.
  * Zone A3. The stability row is a closure statement. The consumer spends it twice: conjugating a
    factorizable bi-finite test function by one finite-times-row-isometry element and then by a
    second one, so that the double conjugation is factorizable and bi-finite for the same type
    family — the composition the level-invariance of a right convolution performs.
  * Zone A4. The integrated finite factor, read at its support: outside the compact support of the
    integral the function vanishes, which is the half of `IsFinTestFactor` that the level
    arguments consume.
  * Zone A5. The same reading for the archimedean factor.
  * Zone A6. The projector, read at a vector: the consumer fixes a `φ` in the cut, and obtains the
    linear map `Q` together with `Q φ = φ` and the `rightConv` property — the two properties the
    cusp constituent's rows use.
  * Zone A7. The level-and-cut membership, spent at a level element: the level half is unfolded
    into the pointwise identity `rightConv φ f (g * u) = rightConv φ f g`, and the cut half is
    carried alongside.
  * Zone A8. The character-typed cut, spent on its witness: the consumer takes the non-zero
    element of the intersection and reads the archimedean character type off it
    (`mem_archCutSubmodule_ofChar_iff`), which is how a consumer replaces an arbitrary `tys` by a
    character family.

  Statement-level data (`D`, `hcov`, `ξ`, `V`, `hV`, the factorizations) cannot be instantiated
  concretely — they are properties of an arbitrary production datum, covering, constituent and
  test function — so they enter in hypothesis form, which is the legitimate reading for these
  rows.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.LeftCasimirTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnInvariance
import FLTForHuman.AutomorphicForm.Adelic.TestFactorIntegral
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentCharCut

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm.SetAF55AConsumer

/-! ### Zone A1: the Casimir dictionary at a real place -/

section real

variable (K : Type) [Field K] [NumberField K]
variable (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
variable (tys : ArchTypeFamily K)

/-- **Zone A1.** The real-place Casimir dictionary, spent as the pair `(β, membership)`: the
Casimir of the right convolution is again a right convolution by a factorizable bi-finite test
factor, and it stays in the level-invariant archimedean cut. -/
theorem consumer_A1_casimir_dictionary
    (w : InfinitePlace K) (hw : w.IsReal)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g) :
    ∃ β : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
      archCasimirAt hw (rightConv K x' α) = rightConv K x' β ∧
      archCasimirAt hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys := by
  obtain ⟨-, -, -, ⟨β, hβf, hβb, hΩ⟩, hmem⟩ :=
    isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite K D w hw N tys x' hxc hxl
      hxt α hαf hαb hαU
  exact ⟨β, hβf, hβb, hΩ, hmem⟩

/-- **Zone A2.** The complex-place Casimir dictionary, spent the same way for both `del` and
`delbar`: the two test factors and the two memberships, which is what a constituent consumes. -/
theorem consumer_A2_casimir_dictionary
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g) :
    ∃ β βb : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
      archCasimirAtComplex hw (rightConv K x' α) = rightConv K x' β ∧
      IsFactorizableTestFn K βb ∧ IsArchBiFinite K tys βb ∧
      archCasimirBarAtComplex hw (rightConv K x' α) = rightConv K x' βb ∧
      archCasimirAtComplex hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys ∧
      archCasimirBarAtComplex hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys := by
  obtain ⟨-, -, -, ⟨β, hβf, hβb, hΩ⟩, ⟨βb, hβbf, hβbb, hΩb⟩, hmem, hmemB⟩ :=
    isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite K D w hw N tys
      x' hxc hxl hxt α hαf hαb hαU
  exact ⟨β, βb, hβf, hβb, hΩ, hβbf, hβbb, hΩb, hmem, hmemB⟩

end real

/-! ### Zone A3: conjugation of a factorizable bi-finite test function -/

section invariance

variable (F : Type) [Field F] [NumberField F]
variable (tys : ArchTypeFamily F)

/-- **Zone A3.** The conjugation row, spent twice: `z ↦ f ((g * k)⁻¹ * z)` stays factorizable and
bi-finite, so its own conjugate by a second finite-times-row-isometry element does too — the double
conjugation a level-invariant right convolution performs. -/
theorem consumer_A3_double_conjugation
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range))
    {g' : AdelicGL2 (𝓞 F) F} (hg' : g' ∈ finiteAdelicGL2Subgroup F)
    {k' : AdelicGL2 (𝓞 F) F} (hk' : k' ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)) :
    IsFactorizableTestFn F (fun z => f ((g * k)⁻¹ * ((g' * k')⁻¹ * z))) ∧
      IsArchBiFinite F tys (fun z => f ((g * k)⁻¹ * ((g' * k')⁻¹ * z))) :=
  isFactorizableTestFn_comp_inv_mul F tys
    (isFactorizableTestFn_comp_inv_mul F tys hf hbf hg hk).1
    (isFactorizableTestFn_comp_inv_mul F tys hf hbf hg hk).2 hg' hk'

end invariance

/-! ### Zones A4 and A5: the two integrated test factors, read at their support -/

section testfactor

variable (F : Type) [Field F] [NumberField F]

/-- **Zone A4.** The integrated finite factor, read as compact support: outside the compact
`tsupport` of `x ↦ ∫ b, ff (x * b) * g b` the integral vanishes. -/
theorem consumer_A4_tsupport
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))]
    (μ : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    (ff g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hff : IsFinTestFactor F ff) (hgs : HasCompactSupport g) :
    ∃ K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)), IsCompact K ∧
      ∀ x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), x ∉ K → (∫ b, ff (x * b) * g b ∂μ) = 0 :=
  ⟨tsupport fun x => ∫ b, ff (x * b) * g b ∂μ,
    (isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport F μ ff g hff hgs).2,
    fun _ hx => image_eq_zero_of_notMem_tsupport (f := fun x => ∫ b, ff (x * b) * g b ∂μ) hx⟩

/-- **Zone A5.** The integrated archimedean factor, read the same way at its support. -/
theorem consumer_A5_tsupport
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing F))) [μ.IsHaarMeasure]
    (fa g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (hg : Continuous g) (hgs : HasCompactSupport g) :
    ∃ K : Set (GL (Fin 2) (InfiniteAdeleRing F)), IsCompact K ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), x ∉ K → (∫ a, fa (x * a) * g a ∂μ) = 0 :=
  ⟨tsupport fun x => ∫ a, fa (x * a) * g a ∂μ,
    (isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport F μ fa g hfa hg hgs).2,
    fun _ hx => image_eq_zero_of_notMem_tsupport (f := fun x => ∫ a, fa (x * a) * g a ∂μ) hx⟩

end testfactor

/-! ### Zone A6: the projector, read at a fixed vector of the cut -/

section projector

variable (F : Type) [Field F] [NumberField F]
variable (tys : ArchTypeFamily F)

/-- **Zone A6.** The projector, spent at a vector `φ` of the cut: the consumer obtains the linear
map `Q`, the fixed-point property `Q φ = φ` at that vector, and the `rightConv` property that the
cusp constituent's rows consume. -/
theorem consumer_A6_projector_at
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ : φ ∈ archCutSubmodule F tys) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      Q φ = φ ∧
      (∀ φ' : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ' →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ'}) →
        Q φ' ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ'}) := by
  obtain ⟨Q, h1, h2, -⟩ := exists_linearMap_archCutProjector F tys
  exact ⟨Q, h1 φ hφc hφ, h2⟩

end projector

/-! ### Zone A7: the level-invariant cut, read at a level element -/

section level

variable (F : Type) [Field F] [NumberField F]
variable (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F))
variable (tys : ArchTypeFamily F)

/-- **Zone A7.** The level-and-cut membership, spent pointwise: the level half unfolds into the
identity `rightConv φ f (g * u) = rightConv φ f g` at every level element, and the archimedean
half is carried alongside. -/
theorem consumer_A7_level_and_cut
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    (∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N,
      rightConv F φ f (g * u) = rightConv F φ f g) ∧
      rightConv F φ f ∈ archCutSubmodule F tys := by
  have h := CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
    F D N tys f hf hbf hfs φ hφc hφU
  exact ⟨fun g u hu => (Submodule.mem_inf.mp h).1 g u hu, (Submodule.mem_inf.mp h).2⟩

end level

/-! ### Zone A8: the character-typed cut, spent on its witness -/

section charcut

variable (K : Type) [Field K] [NumberField K]
variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))

/-- **Zone A8.** A constituent meeting the cut meets the cut of a *character* type family: the
consumer takes the non-zero element of the intersection and reads its archimedean character type
off `mem_archCutSubmodule_ofChar_iff`. -/
theorem consumer_A8_char_member
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥) :
    ∃ χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ,
      ∃ y : AdelicGL2 (𝓞 K) K → ℂ,
        y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ) ∧
        y ≠ 0 ∧ HasArchType₀ K χ y := by
  obtain ⟨χ, hχ⟩ := CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot K c u d₁ d₂ T hc hd₁ hd
    hcov ξ V hV hreal N hN tys hX
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨χ, y, hy, hy0,
    (mem_archCutSubmodule_ofChar_iff K χ y).mp (Submodule.mem_inf.mp hy).2⟩

end charcut

end AutomorphicForm.SetAF55AConsumer
