/-
  The cuspidal-spectrum carrier's API: five rows on top of the gate.

  `exists_isSlabFundamentalDomain` produces a slab fundamental domain from the
  determinant-norm fundamental domain at `(1, 2)`. `isotypicCuspSubmodule_le_cuspMemberSubmodule`
  and `cuspKFiniteSubmodule_le_cuspMemberSubmodule` transfer the centre-cut covering hypothesis
  of the Hecke-isotypic (resp. `K`-finite) cuspidal submodule to the carrier's cusp member
  submodule: automorphy at a centre-cut cover that covers the centre is automorphy at the
  slab fundamental domain (`DetNormSlab`'s headline), and the `K`-finite row uses
  saturation at `1` (`rightTranslate F 1 φ = φ`) to recover the smooth-cusp condition.

  `eq_zero_of_toCarrier_eq_zero` is injectivity of `toCarrier` on continuous members: a
  continuous member whose carrier image vanishes is almost everywhere zero on the weighted
  space (`ae_withDensity_iff`), hence almost everywhere zero on every translate of the
  fundamental domain (`measure_preimage_mul` against the countable global-points subgroup),
  so it is zero everywhere — a non-zero value at `y` is pushed into the *interior* of the
  slab by a central scalar of the right determinant norm, where
  `not_ae_zero_restrict_of_continuous_of_mem_interior` contradicts the vanishing.

  `exists_hasModulus_of_isAutomorphicFnAt_of_continuous` is the row that needs
  `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow`
  (`NumberField/TateGlobal/NormExponent.lean`): the central character evaluated at a fixed
  non-vanishing point is a quotient of two values of a continuous `φ`, hence a continuous
  idèle-class character, and the norm-exponent theorem gives it a real exponent.

  Transcribed from the five pin proof files
  `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_{exists_isSlabFundamentalDomain,
  isotypicCuspSubmodule_le_cuspMemberSubmodule, cuspKFiniteSubmodule_le_cuspMemberSubmodule,
  eq_zero_of_toCarrier_eq_zero, exists_hasModulus_of_isAutomorphicFnAt_of_continuous}.lean`
  (pinned `aa2d8b3`). Each statement is the matching
  `Theorems/Thm_AutomorphicForm_CuspidalSpectrum_*.lean` wrapper verbatim, at the wrapper's
  binders and the wrapper's name inside `AutomorphicForm.CuspidalSpectrum`.

  Body-level drift, per row:
  * `eq_zero_of_toCarrier_eq_zero`, `exists_hasModulus_of_isAutomorphicFnAt_of_continuous` —
    the pin's `push_neg` is the deprecated spelling at `v4.34.0` and is written `push Not`
    (friction FR-0036). Nothing else changed.
  * `cuspKFiniteSubmodule_le_cuspMemberSubmodule` — unchanged; the pin's `hc`/`hd₁` are kept
    because they are the wrapper's statement, and its `rightTranslate` saturation step is
    `funext x; simp [rightTranslate]` as at the pin.

  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isotypicCuspSubmodule_le_cuspMemberSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isotypicCuspSubmodule_le_cuspMemberSubmodule.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlab
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormExponent
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.NumberField.TateGlobalNormSection

set_option autoImplicit false

-- The pin's `haveI` walls in `eq_zero_of_toCarrier_eq_zero` (the four `Countable` instances
-- and the Haar instance) feed instance search in the proof below.
set_option linter.style.haveILetI false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

theorem exists_isSlabFundamentalDomain (F : Type) [Field F] [NumberField F] :
    ∃ (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)), IsSlabFundamentalDomain F α β Φ₀ := by
  obtain ⟨S, hS, hFD⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F 1 2
  exact ⟨1, 2, S, ⟨one_pos, one_lt_two, hS, hFD⟩⟩

theorem isotypicCuspSubmodule_le_cuspMemberSubmodule
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤ cuspMemberSubmodule F Φ₀ ξ :=
  Submodule.span_le.mpr fun φ hφ =>
    ⟨⟨⟨AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
          F c u d₁ d₂ T hd hcov α β hΦ₀.pos Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ φ
          hφ.smoothCusp.1.1, hφ.smoothCusp.1.2⟩, hφ.smoothCusp.2⟩, hφ.continuous⟩

-- The pin's statement keeps `hc` and `hd₁` although its proof does not use them; they are the
-- wrapper's hypotheses, so the binding stays and only the unused-variable linter is silenced.
set_option linter.unusedVariables false in
theorem cuspKFiniteSubmodule_le_cuspMemberSubmodule
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ≤ cuspMemberSubmodule F Φ₀ ξ := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨hsat, hcont, -⟩
  have h1 : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ := by
    have h := hsat 1
    have e : rightTranslate F 1 φ = φ := by
      funext x; simp [rightTranslate]
    rw [e] at h
    exact h
  exact ⟨⟨⟨AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
        F c u d₁ d₂ T hd hcov α β hΦ₀.pos Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ φ h1.1.1,
        h1.1.2⟩, h1.2⟩, hcont⟩

theorem eq_zero_of_toCarrier_eq_zero
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ)
    (h0 : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = 0) : φ = 0 := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hcont : Continuous φ := hφ.2
  obtain ⟨⟨hleft, hcentral⟩, -⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
  have hdetcont := NumberField.TateGlobal.continuous_ideleNorm_det F

  have h1 : ∀ᵐ x ∂(μ.restrict Φ₀), φ x = 0 := by
    have hw : φ =ᵐ[weightedMeasure F Φ₀ σ] 0 := by
      have h0' : (memLp_weightedMeasure_of_mem F hΦ₀ σ hφ.1).toLp φ = 0 := h0
      have h := (memLp_weightedMeasure_of_mem F hΦ₀ σ hφ.1).coeFn_toLp
      rw [h0'] at h
      exact h.symm.trans (Lp.coeFn_zero _ _ _)
    have hmeas : Measurable fun x : AdelicGL2 (𝓞 F) F => ENNReal.ofReal (weight F σ x) := by
      refine Measurable.ennreal_ofReal ?_
      show Measurable fun x : AdelicGL2 (𝓞 F) F =>
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ)
      exact hdetcont.measurable.pow_const _
    rw [weightedMeasure_def, Filter.EventuallyEq, ae_withDensity_iff hmeas] at hw
    filter_upwards [hw] with x hx
    refine hx ?_
    have hpos : 0 < weight F σ x :=
      Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _
    exact (ENNReal.ofReal_pos.mpr hpos).ne'

  set S : Set (AdelicGL2 (𝓞 F) F) := detNormSlab F α β with hS
  set B : Set (AdelicGL2 (𝓞 F) F) := {x | φ x ≠ 0} ∩ Φ₀ with hB
  have hBnull : μ B = 0 := by
    have h := ae_iff.mp h1
    rw [Measure.restrict_apply (isOpen_ne_fun hcont continuous_const).measurableSet] at h
    exact h
  set Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range with hΓ
  haveI : Countable F := by
    exact (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable
      (f := (Units.val : Matrix.GeneralLinearGroup (Fin 2) F → Matrix (Fin 2) (Fin 2) F))
      (fun a b h => Units.ext h)
  haveI : Countable Γ := (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable
  have hpre : ∀ γ : Γ, μ ((fun x => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹' B) = 0 := fun γ => by
    rw [measure_preimage_mul]; exact hBnull
  have hU : μ (⋃ γ : Γ, (fun x => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹' B) = 0 :=
    measure_iUnion_null hpre
  have h2 : ∀ᵐ x ∂(μ.restrict S), φ x = 0 := by
    have hcov : ∀ᵐ x ∂(μ.restrict S), ∃ γ : Γ, γ • x ∈ Φ₀ := hΦ₀.isFundamentalDomain.ae_covers
    have hnot : ∀ᵐ x ∂(μ.restrict S), x ∈ (⋃ γ : Γ, (fun x => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹' B)ᶜ :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr hU)
    filter_upwards [hcov, hnot] with x hx hxn
    obtain ⟨γ, hγ⟩ := hx
    by_contra hne
    apply hxn
    refine Set.mem_iUnion.mpr ⟨γ, ?_⟩
    show (γ : AdelicGL2 (𝓞 F) F) * x ∈ B
    refine ⟨?_, ?_⟩
    · obtain ⟨γ₀, hγ₀⟩ := γ.2
      show φ ((γ : AdelicGL2 (𝓞 F) F) * x) ≠ 0
      rw [← hγ₀, hleft]
      exact hne
    · simpa [Subgroup.smul_def, smul_eq_mul] using hγ

  by_contra hφne
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hφne (funext h)
  obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
  set ny : ℝ := NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) with hny
  have hny_pos : 0 < ny := NumberField.TateGlobal.ideleNorm_pos _
  set t : ℝ := (α + β) / 2 with ht
  have hαβ : α < β := hΦ₀.lt
  have hαt : α < t := by rw [ht]; linarith
  have htβ : t < β := by rw [ht]; linarith
  have ht_pos : 0 < t := hΦ₀.pos.trans hαt
  set rr : ℝ := Real.sqrt (t / ny) with hrr
  have hrr_pos : 0 < rr := Real.sqrt_pos.mpr (div_pos ht_pos hny_pos)
  set r : ℝ≥0ˣ := Units.mk0 ⟨rr, hrr_pos.le⟩ (by
    intro h
    have := congrArg (fun q : ℝ≥0 => (q : ℝ)) h
    simp only [NNReal.coe_zero] at this
    exact hrr_pos.ne' this) with hr
  have hz : NumberField.TateGlobal.ideleNorm F (s r) = rr := by
    rw [hs r]
    rfl
  have key : φ (centralScalar (𝓞 F) F (s r) * y) = ((ξ ⟨s r, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * φ y :=
    hcentral ⟨s r, Subgroup.mem_top _⟩ y
  have hφx : φ (centralScalar (𝓞 F) F (s r) * y) ≠ 0 := by
    rw [key]
    exact mul_ne_zero (Units.ne_zero _) hy
  have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (s r)) = s r * s r := by
    show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (s r)) = s r * s r
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]
  have hdetx : NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (s r) * y)) = t := by
    rw [map_mul, hdet, NumberField.TateGlobal.ideleNorm_mul,
      NumberField.TateGlobal.ideleNorm_mul, hz, ← hny]
    have hsq : rr * rr = t / ny := Real.mul_self_sqrt (div_pos ht_pos hny_pos).le
    rw [hsq, div_mul_cancel₀ _ hny_pos.ne']
  have hopen : IsOpen {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} :=
    isOpen_Ioo.preimage hdetcont
  have hsub : {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} ⊆ S :=
    fun g hg => (mem_detNormSlab F α β g).mpr ⟨hg.1.le, hg.2.le⟩
  have hxint : centralScalar (𝓞 F) F (s r) * y ∈ interior S :=
    interior_maximal hsub hopen (show _ ∈ Set.Ioo α β by rw [hdetx]; exact ⟨hαt, htβ⟩)
  exact not_ae_zero_restrict_of_continuous_of_mem_interior (μ := μ) hcont hφx hxint h2

theorem exists_hasModulus_of_isAutomorphicFnAt_of_continuous
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F (productionPinsOf F D
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      (adelicBox F)) ξ φ)
    (hφc : Continuous φ) (hφ0 : φ ≠ 0) :
    ∃ σ : ℝ, HasModulus F ξ σ := by
  obtain ⟨⟨hleft, hcentral⟩, -⟩ := (isAutomorphicFnAt_fdPins_iff F D ξ φ).mp hφ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, φ g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (funext h)

  let μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) ≃* _).symm.toMonoidHom
  have hμ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, μ z = ξ ⟨z, Subgroup.mem_top z⟩ := fun z => rfl

  have hquot : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ((μ z : ℂˣ) : ℂ) = φ (centralScalar (𝓞 F) F z * g₀) / φ g₀ := by
    intro z
    rw [hμ, eq_div_iff hg₀]
    exact (hcentral ⟨z, Subgroup.mem_top z⟩ g₀).symm

  have hcS : Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
    have hval : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
        ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
          = Matrix.diagonal fun _ => (z : AdeleRing (𝓞 F) F) :=
      fun z => NumberField.AdelicVolume.centralScalar_val z
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have : (fun z : (AdeleRing (𝓞 F) F)ˣ =>
          ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          = fun z : (AdeleRing (𝓞 F) F)ˣ =>
            Matrix.diagonal fun _ : Fin 2 => ((↑z : AdeleRing (𝓞 F) F)) := funext hval
      show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      rw [this]
      exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
    · have : (fun z : (AdeleRing (𝓞 F) F)ˣ =>
          ((↑((centralScalar (𝓞 F) F z)⁻¹ : AdelicGL2 (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          = fun z : (AdeleRing (𝓞 F) F)ˣ =>
            Matrix.diagonal fun _ : Fin 2 => ((↑(z⁻¹) : AdeleRing (𝓞 F) F)) := by
        funext z
        rw [← map_inv, hval]
      rw [this]
      exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

  have hc1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ) := by
    have : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
        = fun z => φ (centralScalar (𝓞 F) F z * g₀) / φ g₀ := funext hquot
    rw [this]
    exact (hφc.comp (hcS.mul continuous_const)).div_const _
  have hcont : Continuous μ := by
    refine Units.continuous_iff.2 ⟨hc1, ?_⟩
    have : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((↑((μ z)⁻¹) : ℂ)))
        = (fun z => ((μ z : ℂˣ) : ℂ)) ∘ fun z => z⁻¹ := by
      funext z
      simp only [Function.comp_apply, map_inv]
    rw [this]
    exact hc1.comp continuous_inv

  have hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ := by
    intro u
    have hglob : centralScalar (𝓞 F) F (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u)
        = globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
      refine Units.ext ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar,
          Matrix.GeneralLinearGroup.map, Matrix.diagonal]
    have h := hcentral ⟨Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u, Subgroup.mem_top _⟩ g₀
    have h' : φ (centralScalar (𝓞 F) F
        (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u) * g₀) = φ g₀ := by
      rw [hglob, hleft]
    rw [h'] at h

    have hξ : ((ξ ⟨Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u, Subgroup.mem_top _⟩ :
        ℂˣ) : ℂ) = 1 :=
      (mul_eq_right₀ hg₀).mp h.symm
    exact Units.ext (by rw [hμ]; exact hξ)
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F μ hclass hcont
  exact ⟨σ, fun z => by simpa [hμ] using hσ z⟩

end CuspidalSpectrum

end AutomorphicForm
