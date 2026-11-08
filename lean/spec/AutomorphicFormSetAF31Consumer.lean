/-
  Cross-module wire test for SET-AF31 (the determinant-window cover and the archimedean unit's norm
  bound).

  A `spec/` probe, not a library module. The two headlines of
  `AutomorphicForm/Adelic/Siegel/DetWindowCover.lean` are a gate-and-door pair, and the zones below
  *compose* them rather than re-deriving either:

  * **Zone 1 (the gate, at a degenerate window).**
    `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` turns a cover at the window `[d₁,d₂]`
    into one at the degenerate window `[1,1]` (`e₁ = e₂ = 1`): the window conditions transfer because
    `0 < 1` and `1 ≤ 1`.

  * **Zone 2 (the gate, enlarged).** The degenerate cover is then fed through
    `SiegelCovering.CoversModCentre.mono`: a right translate of `centreCutSiegelSet c u 1 1` is one of
    `centreCutSiegelSet c u 0 2`, since the only window-sensitive clause is `archDetNorm ∈ Icc · ·`.
    The composition is what makes the door's hypothesis available — the door needs `d₁ ≤ 0`, which the
    degenerate window `[1,1]` does *not* satisfy, so the direct instantiation
    (`e₁ = e₂ = 1` straight into the door) does not exist and is not claimed here.

  * **Zone 3 (the door, fed by the gate).**
    `norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre` is applied at the enlarged window
    `[0,2]` with the Zone-2 cover as `hcov`: a square-integrable automorphic function with a central
    character `ω` contracts the archimedean central unit's character by `‖·‖ < 1`. The `L²` mass
    estimate over the cover is the door's only unported premise and stays a parameter.

  * **Zone 4 (the `‖·‖ < 1` consequence, trivial central character).** At `ω = 1` the door's
    conclusion reads `‖(1 : ℂ)‖ < 1`: the composed hypotheses force the archimedean unit's central
    character to be nontrivial. This is the shape the `L²` estimates consume.

  * **Zone 5 (the zero function).** The work order asks for the `‖·‖ < 1` consequence *for the zero
    function*. That instantiation does not exist: the door's `hφ0 : ∃ g, φ g ≠ 0` is exactly what
    excludes `φ = 0`, and the zone records the refutation at the hypothesis's own shape rather than
    assuming the vacuous case away.

  It imports only the module it consumes.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.DetWindowCover

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel MeasureTheory
open IsDedekindDomain Filter
open scoped ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace SetAF31Consumer

variable {F : Type} [Field F] [NumberField F]

/-- `centreCutSiegelSet` is monotone in the determinant window: every other clause is unchanged. -/
theorem centreCutSiegelSet_subset_of_Icc_subset {c u d₁ d₂ e₁ e₂ : ℝ}
    (hwin : Set.Icc d₁ d₂ ⊆ Set.Icc e₁ e₂) :
    centreCutSiegelSet F c u d₁ d₂ ⊆ centreCutSiegelSet F c u e₁ e₂ := by
  rintro g ⟨hK, hfloor, hxwin, hdet⟩
  exact ⟨hK, hfloor, hxwin, fun v => hwin (hdet v)⟩

/-- The same monotonicity for the finite union of right translates `⋃ x ∈ T, (· * x) '' ·`. -/
theorem iUnion_centreCutSiegelSet_subset {c u d₁ d₂ e₁ e₂ : ℝ}
    {T : Finset (AdelicGL2 (𝓞 F) F)} (hwin : Set.Icc d₁ d₂ ⊆ Set.Icc e₁ e₂) :
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      ⊆ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u e₁ e₂) := by
  intro g hg
  rw [Set.mem_iUnion₂] at hg ⊢
  obtain ⟨x, hx, s, hs, rfl⟩ := hg
  exact ⟨x, hx, s, centreCutSiegelSet_subset_of_Icc_subset hwin hs, rfl⟩

/-- **Zone 1.** The gate at the degenerate window `[1,1]`. -/
theorem coversModCentre_detWindow_one (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u 1 1) :=
  coversModCentre_iUnion_centreCutSiegelSet_of_detWindow F c u d₁ d₂ 1 1 T one_pos le_rfl hcov

/-- **Zone 2.** The gate composed with `CoversModCentre.mono`: the degenerate cover yields one at the
window `[0,2]`, which is the window the door's `d₁ ≤ 0` hypothesis admits. -/
theorem coversModCentre_detWindow_zero_two (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u 0 2) :=
  CoversModCentre.mono
    (iUnion_centreCutSiegelSet_subset fun r hr => ⟨hr.1.trans' zero_le_one, hr.2.trans (by norm_num)⟩)
    (coversModCentre_detWindow_one c u d₁ d₂ T hcov)

/-- **Zone 3.** The door at the gate's window: the `L²` hypothesis is stated over the enlarged
cover `⋃ x ∈ T, (· * x) '' centreCutSiegelSet c u 0 2` that Zone 2 produces. -/
theorem norm_apply_archCentralUnit_lt_one_of_detWindow (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F))
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ0 : ∃ g, φ g ≠ 0)
    (hγ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u 0 2)))
    (w : InfinitePlace F) (a : (w.Completion)ˣ) (ha : ‖(a : w.Completion)‖ < 1) :
    ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 :=
  norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre F c u 0 2 T le_rfl (by norm_num)
    (coversModCentre_detWindow_zero_two c u d₁ d₂ T hcov) φ hφc hφ0 hγ ω hω hL2 w a ha

/-- **Zone 4.** The `‖·‖ < 1` consequence at the trivial central character: for a function with
trivial central character the composed hypotheses give `‖(1 : ℂ)‖ < 1`, i.e. the bound is a *strict*
contraction of the character and never an identity. (Zone 4b reads the same fact in the honest
negative form: no such cover can hold at a trivial central character once the `L²` mass is finite.) -/
theorem norm_one_lt_one_of_detWindow (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ0 : ∃ g, φ g ≠ 0)
    (hγ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hφ1 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = φ g)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u 0 2)))
    (w : InfinitePlace F) (a : (w.Completion)ˣ) (ha : ‖(a : w.Completion)‖ < 1) :
    ‖(1 : ℂ)‖ < 1 := by
  have hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = (((1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) z : ℂˣ) : ℂ) * φ g := by
    intro z g
    rw [hφ1 z g]
    simp
  have h := norm_apply_archCentralUnit_lt_one_of_detWindow c u d₁ d₂ T hcov φ hφc hφ0 hγ
    (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) hω hL2 w a ha
  simp at h

/-- **Zone 4b.** The same consequence in negative form: at a trivial central character, a function
with finite `L²` mass over the enlarged window rules out the cover itself. -/
theorem not_coversModCentre_of_trivial_central (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ0 : ∃ g, φ g ≠ 0)
    (hγ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hφ1 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = φ g)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u 0 2)))
    (w : InfinitePlace F) (a : (w.Completion)ˣ) (ha : ‖(a : w.Completion)‖ < 1) :
    ¬ CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  intro hcov
  have h := norm_one_lt_one_of_detWindow c u d₁ d₂ T hcov φ hφc hφ0 hγ hφ1 hL2 w a ha
  simp at h

/-- **Zone 5.** The zero function is excluded by the door's `hφ0`, so the `‖·‖ < 1` consequence has no
zero-function instance: this is the refutation of `hφ0` at `φ = 0`, in the hypothesis's own shape. -/
theorem zero_fn_not_mem_hφ0 :
    ¬ ∃ g : AdelicGL2 (𝓞 F) F, (fun _ => (0 : ℂ)) g ≠ 0 := by
  rintro ⟨g, hg⟩
  exact hg rfl

end SetAF31Consumer
