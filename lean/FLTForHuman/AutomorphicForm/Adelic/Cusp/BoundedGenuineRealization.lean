/-
  The bounded genuine cusp realization.

  The *bounded* twin of the genuine cusp realization: a realization whose underlying function is
  continuous, bounded on every windowed-Siegel translate, and has integrable/summable Whittaker
  coefficients. The seven notions here (`IsBoundedOnSiegelWindows`, `IsBoundedGenuineFn`,
  `IsBoundedGenuineCuspRealizationAt`, `IsBoundedGenuineCuspRealizable`,
  `IsArithBoundedGenuineCuspRealizable`, `IsArithBoundedGenuineCuspRealizableVia` and the
  `CuspidalityNotion` `boundedGenuineCuspNotionOf`) are the input the weight-one lift's
  boundedness row and the smooth-cusp-realization comparison consume; the API lemmas below are
  the pin's own.

  Transcribed whole from `Definitions/Def_AutomorphicForm_BoundedGenuineCuspRealization.lean`
  (pinned `aa2d8b3`, 316 lines / 34 declarations). The pin's stub imports are replaced by the
  port modules; the pin namespace `AutomorphicForm` is kept.

  `memLp_two_restrict_of_bound` is the one public helper of the `S_` pin below; the pin's
  search-stage label `Ws1.L3` is renamed to the subject namespace `BoundedRealization` (FR-0224;
  the pin's statement is kept verbatim, including its `letI` binders).

  spec-pin: Definitions/Def_AutomorphicForm_BoundedGenuineCuspRealization.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre.lean

  ## Port deltas

  - `open NumberField.AdelicHaar`: `memLp_two_restrict_of_bound` states `glBorel`, `adelicGLHaar`
    and `borelSpace_glBorel` unqualified, as the pin does (`NumberTheory/AdelicHaar/GeneralLinear`).
  - `MeasureTheory` added to the opens: the pin's `S_` file opens it, and the new lemma's frozen
    statement says `MemLp`/`IsFiniteMeasure` unqualified.
  - FR-0223's `haveI`/`letI` → `have`/`let` substitution does **not** compile at three sites
    here (`memLp_two_restrict_of_bound`, and the `hLs` and `SmoothCuspRealizationAt` blocks of the
    69 row). The frozen goals carry a `letI`-bound `MeasurableSpace` in their *types*, and that
    statement-level instance is opaque to instance synthesis; only `letI`'s *inlining* of
    `glBorel`/`pins.mS` into the goal makes the measure arguments unify. At those three sites the
    pin's line is therefore written in **term position** (`letI …; body`, no `by`), which keeps
    the inlining and is not a tactic-mode construct — no `set_option` is used, and the statement
    text is untouched. `hd`/`hcov` of the 69 row are spent once each (FR-0164).
  - heartbeat probe (`-DmaxHeartbeats`): silent at **2000**, first failure at **1500** (the 69 row's
    `whnf`); `whittakerCoefficient_detTwist`'s `simp only` first fails at 1000. Never installed.
-/
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsBoundedOnSiegelWindows (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C

def IsBoundedGenuineFn (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  Continuous φ ∧
    IsBoundedOnSiegelWindows F φ ∧
    (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun α : F => whittakerCoefficient F pins ψ φ α g)

def IsBoundedGenuineCuspRealizationAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ) : Prop :=
  IsBoundedGenuineFn F pins ψ R.toFun

def IsBoundedGenuineCuspRealizable (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ R : SmoothCuspRealizationAt F pins Φ, IsBoundedGenuineCuspRealizationAt F pins ψ Φ R

def IsArithBoundedGenuineCuspRealizable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsBoundedGenuineCuspRealizable F pins ψ Φ.toRawCentral

def IsArithBoundedGenuineCuspRealizableVia (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {R : Type*} [CommRing R] (ι : R →+* ℂ)
    (Φ : HeckeEigensystem F R) : Prop :=
  IsArithBoundedGenuineCuspRealizable F pins ψ (Φ.map ι)

def boundedGenuineCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ =>
    @IsArithBoundedGenuineCuspRealizable F _i1 _i2 (pins F)
      (@NumberField.StandardAddChar.stdAddChar F _i1 _i2) Φ

variable {F}

theorem boundedGenuineCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (boundedGenuineCuspNotionOf pins).IsCusp F Φ ↔
      IsArithBoundedGenuineCuspRealizable F (pins F) (NumberField.StandardAddChar.stdAddChar F) Φ :=
  Iff.rfl

theorem isBoundedGenuineFn_iff (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsBoundedGenuineFn F pins ψ φ ↔
      Continuous φ ∧
        (∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
          ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C) ∧
        (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun α : F => whittakerCoefficient F pins ψ φ α g) :=
  Iff.rfl

theorem isBoundedGenuineCuspRealizable_iff (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ) :
    IsBoundedGenuineCuspRealizable F pins ψ Φ ↔
      ∃ R : SmoothCuspRealizationAt F pins Φ,
        Continuous R.toFun ∧
          (∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
            ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
              ‖R.toFun g‖ ≤ C) ∧
          (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ R.toFun α g) ∧
          ∀ g : AdelicGL2 (𝓞 F) F,
            Summable (fun α : F => whittakerCoefficient F pins ψ R.toFun α g) :=
  Iff.rfl

theorem isBoundedGenuineFn_productionPinsOf_iff
    (D D' : Set (AdelicGL2 (𝓞 F) F))
    (U U' : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen gen' : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsBoundedGenuineFn F (productionPinsOf F D U gen B) ψ φ ↔
      IsBoundedGenuineFn F (productionPinsOf F D' U' gen' B) ψ φ :=
  Iff.rfl

namespace IsBoundedGenuineFn

variable {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}

theorem continuous (h : IsBoundedGenuineFn F pins ψ φ) : Continuous φ :=
  h.1

theorem isBoundedOnSiegelWindows (h : IsBoundedGenuineFn F pins ψ φ) :
    IsBoundedOnSiegelWindows F φ :=
  h.2.1

theorem exists_bound_on_window (h : IsBoundedGenuineFn F pins ψ φ) (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C :=
  h.2.1 c u d₁ d₂ T hc hd₁

theorem whittakerCoefficientIntegrable (h : IsBoundedGenuineFn F pins ψ φ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : WhittakerCoefficientIntegrable F pins ψ φ α g :=
  h.2.2.1 α g

theorem summable_whittakerCoefficient (h : IsBoundedGenuineFn F pins ψ φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun α : F => whittakerCoefficient F pins ψ φ α g) :=
  h.2.2.2 g

end IsBoundedGenuineFn

private theorem det_unipotentGL2 {A : Type*} [CommRing A] (x : A) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

theorem whittakerCoefficient_detTwist (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) α g
      = c (Matrix.GeneralLinearGroup.det g) * whittakerCoefficient F pins ψ φ α g := by
  have := pins.nS
  simp only [whittakerCoefficient, map_mul, det_unipotentGL2, one_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem IsBoundedGenuineFn.detTwist {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsBoundedGenuineFn F pins ψ φ)
    (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hc : Continuous fun g : AdelicGL2 (𝓞 F) F => c (Matrix.GeneralLinearGroup.det g))
    (hc₁ : ∀ u : (AdeleRing (𝓞 F) F)ˣ, ‖c u‖ ≤ 1) :
    IsBoundedGenuineFn F pins ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) := by
  obtain ⟨hφ, hb, hint, hsum⟩ := h
  refine ⟨hc.mul hφ, fun c' u d₁ d₂ T hc' hd₁ => ?_, fun α g => ?_, fun g => ?_⟩
  · obtain ⟨C, hC⟩ := hb c' u d₁ d₂ T hc' hd₁
    refine ⟨C, fun g hg => ?_⟩
    calc ‖c (Matrix.GeneralLinearGroup.det g) * φ g‖
          = ‖c (Matrix.GeneralLinearGroup.det g)‖ * ‖φ g‖ := norm_mul _ _
      _ ≤ ‖φ g‖ := mul_le_of_le_one_left (norm_nonneg _) (hc₁ _)
      _ ≤ C := hC g hg
  · have hi := hint α g
    have := pins.nS
    change MeasureTheory.Integrable _ _ at hi ⊢
    simp only [map_mul, det_unipotentGL2, one_mul, mul_assoc]
    exact hi.const_mul _
  · have key : (fun α : F => whittakerCoefficient F pins ψ
        (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) α g)
        = fun α : F => c (Matrix.GeneralLinearGroup.det g) * whittakerCoefficient F pins ψ φ α g :=
      funext fun α => whittakerCoefficient_detTwist pins ψ c φ α g
    rw [key]
    exact (hsum g).mul_left _

namespace IsBoundedGenuineCuspRealizationAt

variable {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
  {R : SmoothCuspRealizationAt F pins Φ}

theorem isBoundedGenuineFn (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsBoundedGenuineFn F pins ψ R.toFun :=
  h

theorem isGenuineCuspRealizationAt (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsGenuineCuspRealizationAt F pins Φ R :=
  h.1

theorem isBoundedOnSiegelWindows (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsBoundedOnSiegelWindows F R.toFun :=
  h.2.1

theorem exists_bound_on_window (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖R.toFun g‖ ≤ C :=
  h.2.1 c u d₁ d₂ T hc hd₁

theorem whittakerCoefficientIntegrable (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : WhittakerCoefficientIntegrable F pins ψ R.toFun α g :=
  h.2.2.1 α g

theorem summable_whittakerCoefficient (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun α : F => whittakerCoefficient F pins ψ R.toFun α g) :=
  h.2.2.2 g

theorem of_toFun_eq {Φ' : HeckeEigensystem F ℂ} {R' : SmoothCuspRealizationAt F pins Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (he : R'.toFun = R.toFun) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact h

theorem detTwist {Φ' : HeckeEigensystem F ℂ} {R' : SmoothCuspRealizationAt F pins Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hc : Continuous fun g : AdelicGL2 (𝓞 F) F => c (Matrix.GeneralLinearGroup.det g))
    (hc₁ : ∀ u : (AdeleRing (𝓞 F) F)ˣ, ‖c u‖ ≤ 1)
    (he : R'.toFun = fun g => c (Matrix.GeneralLinearGroup.det g) * R.toFun g) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact IsBoundedGenuineFn.detTwist h c hc hc₁

end IsBoundedGenuineCuspRealizationAt

theorem isBoundedGenuineCuspRealizationAt_of_isBoundedGenuineFn {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Φ) (h : IsBoundedGenuineFn F pins ψ R.toFun) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ R :=
  h

theorem IsBoundedGenuineCuspRealizationAt.of_toFun_eq_productionPinsOf
    {D D' : Set (AdelicGL2 (𝓞 F) F)} {U U' : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen gen' : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
    {B : Set (AdeleRing (𝓞 F) F)} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {Φ Φ' : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ}
    {R' : SmoothCuspRealizationAt F (productionPinsOf F D' U' gen' B) Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F (productionPinsOf F D U gen B) ψ Φ R)
    (he : R'.toFun = R.toFun) :
    IsBoundedGenuineCuspRealizationAt F (productionPinsOf F D' U' gen' B) ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact (isBoundedGenuineFn_productionPinsOf_iff D D' U U' gen gen' B ψ R.toFun).mp h

theorem IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (h : IsBoundedGenuineCuspRealizable F pins ψ Φ) : IsGenuineCuspRealizable F pins Φ :=
  h.imp fun _ hR => hR.isGenuineCuspRealizationAt

theorem IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (h : IsArithBoundedGenuineCuspRealizable F pins ψ Φ) :
    IsArithGenuineCuspRealizable F pins Φ :=
  IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable h

theorem IsArithBoundedGenuineCuspRealizableVia.isArithGenuineCuspRealizableVia
    {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {R : Type*} [CommRing R]
    {ι : R →+* ℂ} {Φ : HeckeEigensystem F R}
    (h : IsArithBoundedGenuineCuspRealizableVia F pins ψ ι Φ) :
    IsArithGenuineCuspRealizableVia F pins ι Φ :=
  IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable h

theorem boundedGenuineCuspNotionOf_isCusp_imp
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (h : (boundedGenuineCuspNotionOf pins).IsCusp F Φ) :
    (genuineCuspNotionOf pins).IsCusp F Φ :=
  IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable h

namespace BoundedRealization

theorem memLp_two_restrict_of_bound (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : letI := glBorel (Fin 2) (𝓞 ℚ) ℚ; adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤)
    (v : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hv : Continuous v) (C : ℝ) (hC : ∀ g ∈ D, ‖v g‖ ≤ C) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict D) :=
  letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD⟩
  MemLp.of_bound hv.aestronglyMeasurable C (by
    rw [ae_restrict_iff (isClosed_le hv.norm continuous_const).measurableSet]
    exact ae_of_all _ hC)

end BoundedRealization

/- The first consumer: a genuine cusp realization whose function is bounded on the covered
   windows is the production-pins realization at the same function. -/
theorem exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ R)
    (hb : IsBoundedOnSiegelWindows ℚ R.toFun) :
    ∃ R' : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Φ,
      R'.toFun = R.toFun :=
  letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  by
  classical
  -- FR-0164: the pin's two dead hypotheses are spent once, without touching the statement.
  have hd' : d₁ < d₂ := hd
  have hcov' : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) := hcov
  change Continuous R.toFun at hR
  set D : Set (AdelicGL2 (𝓞 ℚ) ℚ) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂ with hDdef

  have hLs : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ R.centralChar R.toFun :=
    letI := (productionPinsGeneral ℚ).mS
    ((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z R.centralChar
      (productionPinsGeneral ℚ).D R.toFun).mp R.smoothCusp.1.1).1

  have hDfin : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤ :=
    measure_biUnion_lt_top T.finite_toSet
      (fun x _ => AutomorphicForm.adelicGLHaar_mul_right_centreCutSiegelSet_lt_top ℚ hc u hd₁ d₂ x)
  obtain ⟨C, hC⟩ := hb c u d₁ d₂ T hc hd₁
  have hMem : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict D) :=
    BoundedRealization.memLp_two_restrict_of_bound D hDfin R.toFun hR C hC
  refine ⟨{ toFun := R.toFun
            exists_ne_zero := R.exists_ne_zero
            centralChar := R.centralChar
            smoothCusp := ?_
            level_invariant := R.level_invariant
            exceptionalSet := R.exceptionalSet
            hecke_eigen := R.hecke_eigen
            central_eigen := R.central_eigen }, rfl⟩
  refine ⟨⟨?_, R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
  exact letI := (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).mS
    (lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ R.centralChar _ R.toFun).mpr ⟨hLs, hMem⟩

end AutomorphicForm

end
