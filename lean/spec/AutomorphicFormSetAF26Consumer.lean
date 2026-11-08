/-
  Cross-module wire test for SET-AF26 (the local `L²` bound of an `LsXi` function).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* a headline of
  `AutomorphicForm/Adelic/LsXiBound.lean` rather than re-deriving it:

  * **Siegel row.** `exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_…_of_coversModCentre`
    bounds the `L²` mass over a compact `R` by `N` times the mass over the centre-cut window. The zone
    consumes it at a *smaller* compact set `R' ⊆ R` — the constant is inherited unchanged, which is
    the only way to move the bound between compacta without redoing the covering argument
    (`lintegral_mono_set` on top of the headline).

  * **Fundamental-domain row.** `…_of_isFundamentalDomain` is instantiated at the concrete compact set
    `C = {g}` (a singleton is compact), so the headline's `∃ N` is read as the sharp pointwise-mass
    bound `∫⁻_{y ∈ {g}} ‖φ y‖² ≤ N · ∫⁻_{Φ₀} ‖φ y‖²`.

  * **Degenerate data.** The work order asks for the Siegel row at `T = ∅`. That instantiation does
    *not* exist: `T = ∅` makes the window empty, and the ported
    `SiegelCovering.not_coversModCentre_empty` refutes `CoversModCentre K ∅`. The zone proves the
    refutation at the exact shape the headline's `hcov` has, so the vacuity is recorded rather than
    assumed away.

  It imports only the module it consumes.
-/
import FLTForHuman.AutomorphicForm.Adelic.LsXiBound

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace SetAF26Consumer

variable {K : Type} [Field K] [NumberField K]

/-- **Zone 1 (Siegel row).** The cover bound transfers to any compact subset `R' ⊆ R` with the same
constant: the headline's `N` is a property of the window, not of the compactum. -/
theorem exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isCompact_subset
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hR : IsCompact R)
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    {R' : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hR' : IsCompact R') (hR'R : R' ⊆ R) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∫⁻ y in R', (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal N *
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨N, hN⟩ :=
    exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
      K c u d₁ d₂ T hd hcov χ hR
  refine ⟨N, fun φ hφ hcont => ?_⟩
  have hR'm : MeasurableSet R' := hR'.isClosed.measurableSet
  have hind : ∀ y : GL (Fin 2) (AdeleRing (𝓞 K) K),
      R'.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) y
        ≤ R.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) y := by
    intro y
    by_cases hy : y ∈ R'
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hR'R hy)]
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  calc ∫⁻ y in R', (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫⁻ y, R'.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) y
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := (lintegral_indicator hR'm _).symm
    _ ≤ ∫⁻ y, R.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) y
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := lintegral_mono hind
    _ = ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        lintegral_indicator hR.isClosed.measurableSet _
    _ ≤ ENNReal.ofReal N *
          ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := hN φ hφ hcont

/-- **Zone 2 (fundamental-domain row).** The fundamental-domain bound at the singleton `C = {g}`: the
headline's constant `N` controls the mass at a single point against the mass over the fundamental
domain. -/
theorem exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_at_singleton
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (g : AdelicGL2 (𝓞 K) K) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∫⁻ y in ({g} : Set (AdelicGL2 (𝓞 K) K)), (‖φ y‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal N * ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
    K χ (isCompact_singleton : IsCompact ({g} : Set (AdelicGL2 (𝓞 K) K))) α β hβ hαβ Φ₀ hΦ₀

/-- **Zone 3 (degenerate data).** The Siegel row at `T = ∅` is vacuous: its window is empty, and no
empty set covers `GL₂(𝔸_K)` modulo the centre. This is the refutation of the `hcov` hypothesis at
`T = ∅`, in the headline's own shape. -/
theorem not_coversModCentre_window_empty (c u d₁ d₂ : ℝ) :
    ¬ CoversModCentre K (⋃ x ∈ (∅ : Finset (AdelicGL2 (𝓞 K) K)),
      (· * x) '' centreCutSiegelSet K c u d₁ d₂) := by
  have hempty : (⋃ x ∈ (∅ : Finset (AdelicGL2 (𝓞 K) K)),
      (· * x) '' centreCutSiegelSet K c u d₁ d₂) = ∅ := by simp
  rw [hempty]
  exact not_coversModCentre_empty

end SetAF26Consumer

end
