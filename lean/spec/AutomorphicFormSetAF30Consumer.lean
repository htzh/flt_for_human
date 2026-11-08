/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/Siegel/CentreCutCover.lean`.

  The four rows under test are exercised in composition, not by `#check`:

  * `exists_coversModCentre_centreCutSiegelSetAmple` (520) with `CoversModCentre.mono` and
    `centreCutSiegelSetAmple_subset`: the ample cover lands back in the plain centre-cut set at the
    enlarged window (`max u R`), i.e. in the row's own hypothesis shape — so the row *iterates*;
  * `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` (346) unpacked to the point it
    produces (a point outside every translate modulo the centre), and instantiated at the concrete
    translate set `{1}`;
  * (346) composed with (520)'s object: the `u = 0` threshold also rules out the *ample* cover,
    because `centreCutSiegelSetAmple ⊆ centreCutSiegelSet`;
  * `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` (432) instantiated at the zero archimedean
    factor and the trivial central character, where every hypothesis is discharged explicitly.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF30Consumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.CentreCutCover

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace AutomorphicFormSetAF30Consumer

variable (F : Type) [Field F] [NumberField F]

/-- Row 520 composed with `CoversModCentre.mono`: from a cover by the plain centre-cut set one gets
a cover by the same plain set at the enlarged window `max u R` — the row's hypothesis shape again,
because the ample set is contained in the plain one. -/
theorem coversModCentre_centreCutSiegelSet_of_ample {c u d₁ d₂ : ℝ}
    {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧
      CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) := by
  obtain ⟨κ, R, hκ, hR, hcov'⟩ := exists_coversModCentre_centreCutSiegelSetAmple F
  refine ⟨κ, R, hκ, hR, CoversModCentre.mono ?_ (hcov' c u d₁ d₂ T hcov)⟩
  exact Set.iUnion₂_mono fun x _ => Set.image_mono (centreCutSiegelSetAmple_subset c (max u R) d₁ d₂ κ)

/-- The same row applied twice: the cover survives a second ampleness pass. -/
theorem coversModCentre_centreCutSiegelSet_iterate {c u d₁ d₂ : ℝ}
    {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    ∃ κ R R' : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧ 0 ≤ R' ∧
      CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max (max u R) R') d₁ d₂) := by
  obtain ⟨κ, R, hκ, hR, hcov₁⟩ := coversModCentre_centreCutSiegelSet_of_ample F hcov
  obtain ⟨κ', R', hκ', hR', hcov₂⟩ :=
    coversModCentre_centreCutSiegelSet_of_ample F (u := max u R) hcov₁
  exact ⟨κ', R, R', hκ', hR, hR', hcov₂⟩

/-- Row 346 unpacked: there is a point of `GL₂(𝔸)` that no rational translate (modulo the centre)
puts into any translate of the `u = 0` centre-cut Siegel set. -/
theorem exists_point_outside_of_u_eq_zero (c d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ∃ g : AdelicGL2 (𝓞 F) F, ∀ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ),
      ∀ x ∈ T, globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z ∉
        (· * x) '' centreCutSiegelSet F c 0 d₁ d₂ := by
  classical
  by_contra hcon
  refine not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero F c d₁ d₂ T fun g => ?_
  by_contra hno
  refine hcon ⟨g, fun γ z x hx hximg => hno ⟨γ, z, Set.mem_iUnion₂.mpr ⟨x, hx, hximg⟩⟩⟩

/-- Row 346 at the concrete translate set `{1}`: a point whose every rational translate, modulo the
centre, lies outside the `u = 0` centre-cut Siegel set itself. -/
theorem large_height_point_outside_translate (c d₁ d₂ : ℝ) :
    ∃ g : AdelicGL2 (𝓞 F) F, ∀ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ),
      globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z ∉
        (· * (1 : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c 0 d₁ d₂ := by
  obtain ⟨g, hg⟩ := exists_point_outside_of_u_eq_zero F c d₁ d₂ {1}
  exact ⟨g, fun γ z => hg γ z 1 (Finset.mem_singleton_self 1)⟩

/-- Rows 346 and 520 together: the `u = 0` threshold rules out the *ample* cover as well, since
`centreCutSiegelSetAmple ⊆ centreCutSiegelSet`. -/
theorem not_coversModCentre_centreCutSiegelSetAmple_of_u_eq_zero (c d₁ d₂ κ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ¬ CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c 0 d₁ d₂ κ) := by
  refine fun h => not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero F c d₁ d₂ T
    (CoversModCentre.mono ?_ h)
  exact Set.iUnion₂_mono fun x _ => Set.image_mono (centreCutSiegelSetAmple_subset c 0 d₁ d₂ κ)

/-- Row 432 instantiated at the zero archimedean factor and the trivial central character: the
`MemLp` bound at the narrow determinant window `d₁` follows from the one at `dp`, every hypothesis
being discharged explicitly. -/
theorem memLp_zero_of_detWindow_le (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp) (hd : 0 < d₁) :
    letI := glBorel (Fin 2) (𝓞 F) F
    MemLp (fun _ : AdelicGL2 (𝓞 F) F => (0 : ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  refine memLp_iUnion_centreCutSiegelSet_of_detWindow_le F c u d₁ d₂ dp T hdp hdp₂ hd₁
    (fun _ => 0) aestronglyMeasurable_const (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) ?_ ?_ ?_
  · intro z g
    simp
  · intro hle
    exact absurd hle (not_le.mpr hd)
  · simp

end AutomorphicFormSetAF30Consumer
