/-
  Cross-module wire test for SET-AF27 (the `L²`-continuity of right convolution).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* a headline of
  `AutomorphicForm/Adelic/RightConvLpContinuity.lean` instead of restating it:

  * **Zone 1 (pin 139).** `exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le`
    is an abstract compactness argument, so it can be *discharged* at concrete data: `X = ℝ`, `E = ℝ`,
    `ι = Unit` and `ν` a probability measure. Tightness becomes vacuous (`ν univᶜ = 0`), the family is
    the single Gaussian bump `x ↦ exp (-(x ^ 2))` whose pointwise bound and a.e. bound are both `1`,
    and equicontinuity of a one-element family follows from continuity of that one function. All four
    substantive hypotheses are proved here, so the zone is the lemma's statement with nothing assumed.

  * **Zone 2 (pin 209 at `Kc = {1}`).** The uniform-continuity row is instantiated at the *degenerate*
    compactum `Kc = {1}` and read at the identity coset `g = 1`: the neighbourhood `V` of `1` then
    controls `rightConv φ f (1 * h) - rightConv φ f 1` uniformly over the `L²`-bounded `φ`.

  * **Zone 3 (the constant is not canonical).** The row is monotone in `ε`: the same neighbourhood `V`
    serves every larger `ε'`. This is the composition that makes the row usable as a `ε`-`δ` input —
    the consumer picks the radius it needs, not the one the headline happened to produce.

  It imports the module it consumes plus `Mathlib.MeasureTheory.Measure.Tight`, whose
  `isTightMeasureSet_singleton` is what discharges zone 1's tightness hypothesis at a probability
  measure on `ℝ` (the headline itself does not need it).
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvLpContinuity
import Mathlib.MeasureTheory.Measure.Tight

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open IsDedekindDomain Filter
open scoped ENNReal Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace SetAF27Consumer

/-! ## Zone 1: pin 139 with every hypothesis discharged -/

/-- The Gaussian bump is bounded by `1`. -/
theorem norm_exp_neg_sq_le_one (x : ℝ) : ‖Real.exp (-(x ^ 2))‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have h : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  linarith

/-- A family indexed by a subsingleton is equicontinuous as soon as its one member is continuous. -/
theorem equicontinuous_of_subsingleton_index {ι : Type*} [Subsingleton ι]
    {f : ℝ → ℝ} (hf : Continuous f) : Equicontinuous (fun (_ : ι) => f) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro δ hδ
  filter_upwards [Metric.continuousAt_iff'.mp hf.continuousAt δ hδ] with y hy i
  simpa [dist_comm] using hy

/-- **Zone 1.** The generic equicontinuity lemma (pin 139) at `X = ℝ`, `E = ℝ`, `ι = Unit` and a
probability measure: tightness is vacuous, the family is one Gaussian bump, and both the pointwise and
the almost-everywhere bound are `1`. -/
theorem exists_finset_exp_neg_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : Finset Unit,
      ∀ i : Unit, ∃ j ∈ s, eLpNorm ((fun (_ : Unit) (x : ℝ) => Real.exp (-(x ^ 2))) i
        - (fun (_ : Unit) (x : ℝ) => Real.exp (-(x ^ 2))) j) 2 ν < ε :=
  exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
    (u := fun (_ : Unit) (x : ℝ) => Real.exp (-(x ^ 2))) ν 2 (by norm_num) ENNReal.ofNat_ne_top
    (fun η hη => by
      rcases eq_or_ne η ⊤ with rfl | hηtop
      · exact ⟨∅, isCompact_empty, by simp⟩
      · obtain ⟨K, hK, hle⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
          (isTightMeasureSet_singleton (μ := ν)) (η / 2) (ENNReal.half_pos hη.ne')
        exact ⟨K, hK, lt_of_le_of_lt (hle ν rfl) (ENNReal.half_lt_self hη.ne' hηtop)⟩)
    (equicontinuous_of_subsingleton_index (f := fun x : ℝ => Real.exp (-(x ^ 2))) (by continuity))
    (fun x => ⟨1, fun _ => norm_exp_neg_sq_le_one x⟩)
    1 (fun _ => Filter.Eventually.of_forall norm_exp_neg_sq_le_one) ε hε

/-! ## Zone 2: the 209 row at the degenerate compactum `Kc = {1}` -/

/-- **Zone 2.** Pin 209 at `Kc = {1}`, read at the identity coset `g = 1`. -/
theorem exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_at_one
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
          ∀ h ∈ V,
            ‖rightConv K φ f (1 * h) - rightConv K φ f 1‖ ≤
              ε * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by
  obtain ⟨V, hV, hcl⟩ :=
    exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
      K χ f hf (isCompact_singleton : IsCompact ({1} : Set (AdelicGL2 (𝓞 K) K)))
      α β hβ hαβ Φ₀ hΦ₀ ε hε
  exact ⟨V, hV, fun φ hls hcont hmem h hh => hcl φ hls hcont hmem 1 (by simp) h hh⟩

/-! ## Zone 3: the radius `ε` is a choice, not a constant of the row -/

/-- **Zone 3.** The 209 row is monotone in `ε`: the neighbourhood produced for `ε` serves every
`ε' ≥ ε`, so a consumer may weaken the radius after the fact. -/
theorem exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_of_le
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    {Kc : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hKc : IsCompact Kc)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ε ε' : ℝ) (hε : 0 < ε) (hεε' : ε ≤ ε') :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
          ∀ g ∈ Kc, ∀ h ∈ V,
            ‖rightConv K φ f (g * h) - rightConv K φ f g‖ ≤
              ε' * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by
  obtain ⟨V, hV, hcl⟩ :=
    exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
      K χ f hf hKc α β hβ hαβ Φ₀ hΦ₀ ε hε
  refine ⟨V, hV, fun φ hls hcont hmem g hg h hh => (hcl φ hls hcont hmem g hg h hh).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hεε' ENNReal.toReal_nonneg

end SetAF27Consumer

end
