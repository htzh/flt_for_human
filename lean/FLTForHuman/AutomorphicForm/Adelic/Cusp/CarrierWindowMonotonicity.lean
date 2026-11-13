/-
  The cuspidal carrier is monotone in the slab window.

  `isotypicCuspSubmodule` (the Hecke-isotypic cuspidal subspace) and `cuspKFiniteSubmodule`
  (the `K`-finite one) are stated against a centre-cut covering
  `⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂`.  Widening the window (`d₁ ≤ d₁'`, with
  `d₁' < d₂`) can only shrink the carrier: an element of the wider carrier is `L²` on the wider
  covering, hence on the narrower one, and the central-character bound
  `norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre` carries the `L²` membership
  across (`memLp_iUnion_centreCutSiegelSet_of_detWindow_le`).  The first row is the isotypic
  carrier — non-triviality `≠ ⊥` is what its hypothesis carries, and its proof reads a non-zero
  member's automorphy off the carrier's definition; the second is the `K`-finite carrier, whose
  hypothesis is a witness `φ ≠ 0` and whose proof transfers the right translate of that witness.

  The two rows are the pin's `d₁`-monotonicity step for the cuspidal carrier: everything that
  states a carrier at one window and consumes it at another goes through them.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot.lean`
  (68 lines) and
  `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero.lean`
  (66 lines), with the statements from the wrappers of the same names.

  Assumes from earlier modules: the carriers and their `ne_bot` dictionary
  (`IsotypicCuspSpace.lean`, `Cusp/SpectrumCarrier.lean`), and the two `L²`-transfer rows of
  `Siegel/DetWindowCover.lean` and `Siegel/CentreCutCover.lean` — neither of which anything else
  in the port imports, so this module is their first consumer.

  spec-pin: Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.Siegel.DetWindowCover
import FLTForHuman.AutomorphicForm.Adelic.Siegel.CentreCutCover
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open NumberField.SiegelVolume
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (hne : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≠ ⊥) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤
      isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ := by
  -- `hc` is a frozen binder of the wrapper's statement; it is consumed here rather than omitted.
  have hcpos : 0 < c := hc
  refine Submodule.span_le.mpr ?_
  intro ψ hψ
  apply Submodule.subset_span

  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := (isotypicCuspSubmodule_ne_bot_iff F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ).mp hne
  have hA0 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ₀).mp hφ₀.smoothCusp.1.1
  have hA := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) ψ).mp
    (show IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ψ from hψ.smoothCusp.1.1)

  let ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) ≃* (AdeleRing (𝓞 F) F)ˣ).symm.toMonoidHom
  have hω0 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ₀ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ₀ g :=
    fun z g => hA0.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hωψ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      ψ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * ψ g :=
    fun z g => hA.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hd₂ : 0 < d₂ := hd₁'.trans hlt
  have hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 :=
    fun hd₁ w a ha =>
      AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre F c u d₁ d₂ T hd₁ hd₂ hcov
        φ₀ hφ₀.continuous (Function.ne_iff.mp hφ₀ne) hA0.1.left_invariant ω hω0 hA0.2 w a ha
  have hMem : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
    AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le F c u d₁ d₂ d₁' T hd₁' hlt hle ψ
      hψ.continuous.aestronglyMeasurable ω hωψ hcontr hA.2
  exact ⟨⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ψ).mpr ⟨hA.1, hMem⟩,
      hψ.smoothCusp.1.2⟩, hψ.smoothCusp.2⟩, hψ.continuous, hψ.level_invariant, hψ.hecke_eigen,
      hψ.central_eigen⟩

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (hne : ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ ∧ Continuous φ ∧ φ ≠ 0) :
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  -- `hc` is a frozen binder of the wrapper's statement; it is consumed here rather than omitted.
  have hcpos : 0 < c := hc
  refine Submodule.span_le.mpr ?_
  rintro ψ ⟨hsat, hcont, htys⟩
  apply Submodule.subset_span

  obtain ⟨φ₀, hφ₀A, hφ₀c, hφ₀ne⟩ := hne
  have hA0 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ₀).mp hφ₀A
  let ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) ≃* (AdeleRing (𝓞 F) F)ˣ).symm.toMonoidHom
  have hω0 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ₀ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ₀ g :=
    fun z g => hA0.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hd₂ : 0 < d₂ := hd₁'.trans hlt
  have hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 :=
    fun hd₁ w a ha =>
      AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre F c u d₁ d₂ T hd₁ hd₂ hcov
        φ₀ hφ₀c (Function.ne_iff.mp hφ₀ne) hA0.1.left_invariant ω hω0 hA0.2 w a ha
  refine ⟨fun g => ?_, hcont, htys⟩

  have hg := hsat g
  have hA := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) (rightTranslate F g ψ)).mp
    (show IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ (rightTranslate F g ψ) from hg.1.1)
  have hωψ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (x : AdelicGL2 (𝓞 F) F),
      rightTranslate F g ψ (centralScalar (𝓞 F) F z * x) =
        ((ω z : ℂˣ) : ℂ) * rightTranslate F g ψ x :=
    fun z x => hA.1.central_transform ⟨z, Subgroup.mem_top z⟩ x
  have hMem : MemLp (rightTranslate F g ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
    AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le F c u d₁ d₂ d₁' T hd₁' hlt hle
      (rightTranslate F g ψ) (continuous_rightTranslate F hcont g).aestronglyMeasurable ω hωψ hcontr hA.2
  exact ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (rightTranslate F g ψ)).mpr
      ⟨hA.1, hMem⟩, hg.1.2⟩, hg.2⟩
