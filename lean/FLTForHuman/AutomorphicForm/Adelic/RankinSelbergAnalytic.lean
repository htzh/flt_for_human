/-
  The analyticity of the `S`-part integral: the Petersson integral in the complex variable.

  The integral that the Rankin–Selberg unfolding produces,

    `s ↦ ∫ g in 𝓕, x g · G s g · conj (y g) · ‖det g‖ ^ (-w)`,

  is holomorphic on the half-plane `a < Re s` whenever the family `G` is holomorphic in `s`,
  continuous in `(s, g)`, locally bounded by `(1 + archHeight g) ^ N`, and the product
  `‖x g‖ ‖y g‖ (1 + archHeight (g * tᵢ⁻¹)) ^ N ‖det g‖ ^ (-w)` is integrable on the piece of the
  Siegel cover that `𝓕` meets.  Moreover, when `G` vanishes to the order of `(s - s₀)` with
  quotient `E`, the same integral is `(s - s₀)` times the Petersson integral of `x · E s` against
  `y` — so the vanishing order of the local factor is read off the Petersson integral.

  These are the two rows that turn the unfolded identity of `PeterssonUnfolding.lean` into an
  analytic statement about the local factor: they are the pin's `exists_analyticOnNhd_…` rows, and
  they are the consumers of the analytic floor `MeasureTheory/ParametricIntegral.lean`
  (`differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le`), of the Petersson
  integral's home and of the two Siegel covers below.

  Transcribed from the two pins below (pinned `aa2d8b3`, 186 + 185 lines), all public (4 + 4
  declarations each).  The two differ only in the Siegel cover `𝓕` is allowed to meet — the
  centre-cut Siegel set versus the integral windowed Siegel set — and both are transcribed whole.

  Assumes `PeterssonIntegral.lean` (`peterssonIntegral`), `WindowedSiegel/Set.lean`
  (`archHeight`, `integralWindowedSiegelSet`) and `WindowedSiegel/CentreCutSet.lean`
  (`centreCutSiegelSet`), the analytic floor `MeasureTheory/ParametricIntegral.lean`
  (`differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le`) and the idèle-norm
  façade `NumberField/TateGlobalContinuousIdeleNorm.lean`
  (`NumberField.TateGlobal.continuous_ideleNorm_det`).

  Heartbeat probe pair (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file, one
  run per value, measured and never installed): silent at `N = 25000`, first failure at `N = 12000`
  (an `isDefEq` timeout in the first headline's nonnegativity step, `:240`, and the tactic step
  enclosing it, `:189`, with a second `whnf` timeout at the first headline's `:404`).  The edit
  loop runs at Lean's default `200000`, so no bound is installed.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonIntegral
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Set
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.MeasureTheory.ParametricIntegral
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open Filter Topology Metric
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace PeterssonAnalytic

variable {F : Type} [Field F] [NumberField F]

/-- The weight `‖det g‖ ^ (-w)` is continuous on the adèlic `GL₂`. -/
theorem continuous_weight (w : ℝ) :
    Continuous fun g : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) :=
  (NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun _ =>
    Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'

/-- The weight `‖det g‖ ^ (-w)` is positive. -/
theorem weight_pos (w : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) :=
  Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _

namespace CentreCut

/-- A right translate of the centre-cut Siegel set is measurable. -/
theorem measurableSet_translate (c u d₁ d₂ : ℝ) (t : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * t) '' centreCutSiegelSet F c u d₁ d₂) := by
  rw [Set.image_mul_right]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const _)

end CentreCut

namespace Windowed

/-- A right translate of the integral windowed Siegel set is measurable. -/
theorem measurableSet_translate (c u : ℝ) (t : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * t) '' integralWindowedSiegelSet F c u) := by
  rw [Set.image_mul_right]
  exact (measurableSet_integralWindowedSiegelSet F c u).preimage (measurable_mul_const _)

end Windowed

end PeterssonAnalytic

theorem exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (w a c u d₁ d₂ : ℝ) (_hc : 0 < c) (ι : Type) [Fintype ι] (t : ι → AdelicGL2 (𝓞 F) F)
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕cov : 𝓕 ⊆ ⋃ i, (· * t i) '' centreCutSiegelSet F c u d₁ d₂)
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hGan : ∀ g, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re})
    (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (_hGbd : ∀ (C : Set ℂ), IsCompact C → C ⊆ {s : ℂ | a < s.re} → ∀ i : ι,
      ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ centreCutSiegelSet F c u d₁ d₂,
        ‖G s (g * t i)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) (_hxc : Continuous x) (_hyc : Continuous y)
    (_hdecay : ∀ (i : ι) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t i) '' centreCutSiegelSet F c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) {s : ℂ | a < s.re} ∧
    ∀ (s₀ : ℂ) (σ₁ : ℝ) (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), σ₁ < s.re → G s g = (s - s₀) * E s g) →
      ∀ s : ℂ, σ₁ < s.re → a < s.re →
        (∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y := by
  classical
  set Φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => x g * G s g * (starRingEnd ℂ) (y g) *
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) with hΦ
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set U : Set ℂ := {s : ℂ | a < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨?_, ?_⟩
  ·
    have hGs : ∀ s ∈ U, Continuous fun g : AdelicGL2 (𝓞 F) F => G s g := by
      intro s hs
      have h1 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s} ×ˢ Set.univ) :=
        _hGc.mono (Set.prod_mono (Set.singleton_subset_iff.mpr hs) le_rfl)
      have h2 : Continuous fun g : AdelicGL2 (𝓞 F) F => ((s, g) : ℂ × AdelicGL2 (𝓞 F) F) := by
        fun_prop
      exact h1.comp_continuous h2 fun g => ⟨rfl, Set.mem_univ _⟩
    have hΦc : ∀ s ∈ U, Continuous (Φ s) := by
      intro s hs
      rw [hΦ]
      exact ((_hxc.mul (hGs s hs)).mul (Complex.continuous_conj.comp _hyc)).mul
        (Complex.continuous_ofReal.comp (PeterssonAnalytic.continuous_weight w))

    have hsub : ∀ s, (∫ g in 𝓕, Φ s g ∂μ) =
        ∫ g : 𝓕, Φ s (g : AdelicGL2 (𝓞 F) F) ∂(μ.comap Subtype.val) :=
      fun s => (integral_subtype_comap _h𝓕m (Φ s)).symm
    have hgoal : AnalyticOnNhd ℂ
        (fun s : ℂ => ∫ g : 𝓕, Φ s (g : AdelicGL2 (𝓞 F) F) ∂(μ.comap Subtype.val)) U := by
      apply DifferentiableOn.analyticOnNhd _ hUo
      refine MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
        (μ.comap Subtype.val) hUo (fun s (g : 𝓕) => Φ s g) (fun s hs => ?_) (fun g => ?_)
        (fun z₀ hz₀ => ?_)
      ·
        exact ((hΦc s hs).comp continuous_subtype_val).aestronglyMeasurable
      ·
        have hG := (_hGan (g : AdelicGL2 (𝓞 F) F)).differentiableOn
        rw [hΦ]
        exact ((hG.const_mul _).mul_const _).mul_const _
      ·
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUo z₀ hz₀
        have hC : IsCompact (closedBall z₀ (δ / 2)) := isCompact_closedBall _ _
        have hCU : closedBall z₀ (δ / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
        choose M N hMN using fun i : ι => _hGbd _ hC hCU i

        set maj : ι → AdelicGL2 (𝓞 F) F → ℝ := fun i g =>
          |M i| * (‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ (N i) *
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) with hmaj
        set Mg : AdelicGL2 (𝓞 F) F → ℝ := fun g =>
          ∑ i, ((· * t i) '' centreCutSiegelSet F c u d₁ d₂).indicator (maj i) g with hMg
        refine ⟨δ / 2, by linarith, fun g : 𝓕 => Mg g, ?_, ?_⟩
        ·
          have hint : IntegrableOn Mg 𝓕 μ := by
            rw [hMg]
            refine integrable_finsetSum _ fun i _ => ?_
            rw [integrable_indicator_iff
              (PeterssonAnalytic.CentreCut.measurableSet_translate c u d₁ d₂ (t i))]
            change IntegrableOn (maj i) _ (μ.restrict 𝓕)
            rw [IntegrableOn,
              Measure.restrict_restrict
                (PeterssonAnalytic.CentreCut.measurableSet_translate c u d₁ d₂ (t i)),
              Set.inter_comm]
            exact ((_hdecay i (N i)).const_mul (|M i|))
          exact (integrableOn_iff_comap_subtypeVal _h𝓕m).mp hint
        ·
          intro z hz g
          have hzC : z ∈ closedBall z₀ (δ / 2) := ball_subset_closedBall hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (_h𝓕cov g.2)
          obtain ⟨g₀, hg₀, hg₀eq⟩ := hi
          have hgi : (g : AdelicGL2 (𝓞 F) F) ∈ (· * t i) '' centreCutSiegelSet F c u d₁ d₂ :=
            ⟨g₀, hg₀, hg₀eq⟩
          have hg₀' : g₀ = (g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹ := by rw [← hg₀eq]; simp

          have hGb : ‖G z g‖ ≤ |M i| * (1 + archHeight F (glArch (𝓞 F) F
              ((g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹))) ^ (N i) := by
            have h := hMN i z hzC g₀ hg₀
            have hgt : g₀ * t i = (g : AdelicGL2 (𝓞 F) F) := hg₀eq
            rw [hgt, hg₀'] at h
            refine h.trans ?_
            apply mul_le_mul_of_nonneg_right (le_abs_self _)
            exact pow_nonneg (by linarith [archHeight_pos F (glArch (𝓞 F) F
              ((g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹))]) _

          have hnorm : ‖Φ z g‖ = ‖x g‖ * ‖G z g‖ * ‖y g‖ *
              NumberField.TateGlobal.ideleNorm F
                (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w) := by
            rw [hΦ]
            simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (PeterssonAnalytic.weight_pos w _)]

          have hterm : ‖Φ z g‖ ≤ maj i g := by
            rw [hnorm]
            have hw0 := (PeterssonAnalytic.weight_pos w (g : AdelicGL2 (𝓞 F) F)).le
            calc ‖x (g : AdelicGL2 (𝓞 F) F)‖ * ‖G z g‖ * ‖y (g : AdelicGL2 (𝓞 F) F)‖ *
                  NumberField.TateGlobal.ideleNorm F
                    (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w)
                = (‖x (g : AdelicGL2 (𝓞 F) F)‖ * ‖y (g : AdelicGL2 (𝓞 F) F)‖ *
                    NumberField.TateGlobal.ideleNorm F
                      (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w)) *
                    ‖G z g‖ := by ring
              _ ≤ (‖x (g : AdelicGL2 (𝓞 F) F)‖ * ‖y (g : AdelicGL2 (𝓞 F) F)‖ *
                    NumberField.TateGlobal.ideleNorm F
                      (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w)) *
                    (|M i| * (1 + archHeight F (glArch (𝓞 F) F
                      ((g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹))) ^ (N i)) :=
                  mul_le_mul_of_nonneg_left hGb (by positivity)
              _ = maj i g := by simp only [hmaj]; ring
          have hnonneg : ∀ j, 0 ≤ ((· * t j) '' centreCutSiegelSet F c u d₁ d₂).indicator (maj j)
              (g : AdelicGL2 (𝓞 F) F) := by
            intro j
            apply Set.indicator_nonneg
            intro g' _
            rw [hmaj]
            have := PeterssonAnalytic.weight_pos w g'
            have := archHeight_pos F (glArch (𝓞 F) F (g' * (t j)⁻¹))
            positivity
          calc ‖Φ z g‖ ≤ maj i g := hterm
            _ = ((· * t i) '' centreCutSiegelSet F c u d₁ d₂).indicator (maj i)
                (g : AdelicGL2 (𝓞 F) F) :=
                (Set.indicator_of_mem hgi _).symm
            _ ≤ Mg g := by
                rw [hMg]
                exact Finset.single_le_sum (f := fun j =>
                  ((· * t j) '' centreCutSiegelSet F c u d₁ d₂).indicator (maj j)
                  (g : AdelicGL2 (𝓞 F) F)) (fun j _ => hnonneg j) (Finset.mem_univ i)

    have heq : (fun s : ℂ => ∫ g in 𝓕, Φ s g ∂μ) =
        fun s => ∫ g : 𝓕, Φ s (g : AdelicGL2 (𝓞 F) F) ∂(μ.comap Subtype.val) :=
      funext hsub
    show AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, Φ s g ∂μ) U
    rw [heq]
    exact hgoal
  ·
    intro s₀ σ₁ E hE s hs _
    show (∫ g in 𝓕, Φ s g ∂μ) = (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y
    unfold peterssonIntegral
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hΦ, hE s g hs]
    ring

theorem exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow
    (F : Type) [Field F] [NumberField F]
    (w a c u : ℝ) (_hc : 0 < c) (ι : Type) [Fintype ι] (t : ι → AdelicGL2 (𝓞 F) F)
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕cov : 𝓕 ⊆ ⋃ i, (· * t i) '' integralWindowedSiegelSet F c u)
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hGan : ∀ g, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re})
    (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (_hGbd : ∀ (C : Set ℂ), IsCompact C → C ⊆ {s : ℂ | a < s.re} → ∀ i : ι,
      ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ integralWindowedSiegelSet F c u,
        ‖G s (g * t i)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) (_hxc : Continuous x) (_hyc : Continuous y)
    (_hdecay : ∀ (i : ι) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t i) '' integralWindowedSiegelSet F c u) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) {s : ℂ | a < s.re} ∧
    ∀ (s₀ : ℂ) (σ₁ : ℝ) (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), σ₁ < s.re → G s g = (s - s₀) * E s g) →
      ∀ s : ℂ, σ₁ < s.re → a < s.re →
        (∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y := by
  classical
  set Φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => x g * G s g * (starRingEnd ℂ) (y g) *
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) with hΦ
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set U : Set ℂ := {s : ℂ | a < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨?_, ?_⟩
  ·
    have hGs : ∀ s ∈ U, Continuous fun g : AdelicGL2 (𝓞 F) F => G s g := by
      intro s hs
      have h1 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s} ×ˢ Set.univ) :=
        _hGc.mono (Set.prod_mono (Set.singleton_subset_iff.mpr hs) le_rfl)
      have h2 : Continuous fun g : AdelicGL2 (𝓞 F) F => ((s, g) : ℂ × AdelicGL2 (𝓞 F) F) := by
        fun_prop
      exact h1.comp_continuous h2 fun g => ⟨rfl, Set.mem_univ _⟩
    have hΦc : ∀ s ∈ U, Continuous (Φ s) := by
      intro s hs
      rw [hΦ]
      exact ((_hxc.mul (hGs s hs)).mul (Complex.continuous_conj.comp _hyc)).mul
        (Complex.continuous_ofReal.comp (PeterssonAnalytic.continuous_weight w))

    have hsub : ∀ s, (∫ g in 𝓕, Φ s g ∂μ) =
        ∫ g : 𝓕, Φ s (g : AdelicGL2 (𝓞 F) F) ∂(μ.comap Subtype.val) :=
      fun s => (integral_subtype_comap _h𝓕m (Φ s)).symm
    have hgoal : AnalyticOnNhd ℂ
        (fun s : ℂ => ∫ g : 𝓕, Φ s (g : AdelicGL2 (𝓞 F) F) ∂(μ.comap Subtype.val)) U := by
      apply DifferentiableOn.analyticOnNhd _ hUo
      refine MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
        (μ.comap Subtype.val) hUo (fun s (g : 𝓕) => Φ s g) (fun s hs => ?_) (fun g => ?_)
        (fun z₀ hz₀ => ?_)
      ·
        exact ((hΦc s hs).comp continuous_subtype_val).aestronglyMeasurable
      ·
        have hG := (_hGan (g : AdelicGL2 (𝓞 F) F)).differentiableOn
        rw [hΦ]
        exact ((hG.const_mul _).mul_const _).mul_const _
      ·
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUo z₀ hz₀
        have hC : IsCompact (closedBall z₀ (δ / 2)) := isCompact_closedBall _ _
        have hCU : closedBall z₀ (δ / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
        choose M N hMN using fun i : ι => _hGbd _ hC hCU i

        set maj : ι → AdelicGL2 (𝓞 F) F → ℝ := fun i g =>
          |M i| * (‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ (N i) *
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) with hmaj
        set Mg : AdelicGL2 (𝓞 F) F → ℝ := fun g =>
          ∑ i, ((· * t i) '' integralWindowedSiegelSet F c u).indicator (maj i) g with hMg
        refine ⟨δ / 2, by linarith, fun g : 𝓕 => Mg g, ?_, ?_⟩
        ·
          have hint : IntegrableOn Mg 𝓕 μ := by
            rw [hMg]
            refine integrable_finsetSum _ fun i _ => ?_
            rw [integrable_indicator_iff
              (PeterssonAnalytic.Windowed.measurableSet_translate c u (t i))]
            change IntegrableOn (maj i) _ (μ.restrict 𝓕)
            rw [IntegrableOn,
              Measure.restrict_restrict
                (PeterssonAnalytic.Windowed.measurableSet_translate c u (t i)),
              Set.inter_comm]
            exact ((_hdecay i (N i)).const_mul (|M i|))
          exact (integrableOn_iff_comap_subtypeVal _h𝓕m).mp hint
        ·
          intro z hz g
          have hzC : z ∈ closedBall z₀ (δ / 2) := ball_subset_closedBall hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (_h𝓕cov g.2)
          obtain ⟨g₀, hg₀, hg₀eq⟩ := hi
          have hgi : (g : AdelicGL2 (𝓞 F) F) ∈ (· * t i) '' integralWindowedSiegelSet F c u :=
            ⟨g₀, hg₀, hg₀eq⟩
          have hg₀' : g₀ = (g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹ := by rw [← hg₀eq]; simp

          have hGb : ‖G z g‖ ≤ |M i| * (1 + archHeight F (glArch (𝓞 F) F
              ((g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹))) ^ (N i) := by
            have h := hMN i z hzC g₀ hg₀
            have hgt : g₀ * t i = (g : AdelicGL2 (𝓞 F) F) := hg₀eq
            rw [hgt, hg₀'] at h
            refine h.trans ?_
            apply mul_le_mul_of_nonneg_right (le_abs_self _)
            exact pow_nonneg (by linarith [archHeight_pos F (glArch (𝓞 F) F
              ((g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹))]) _

          have hnorm : ‖Φ z g‖ = ‖x g‖ * ‖G z g‖ * ‖y g‖ *
              NumberField.TateGlobal.ideleNorm F
                (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w) := by
            rw [hΦ]
            simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (PeterssonAnalytic.weight_pos w _)]

          have hterm : ‖Φ z g‖ ≤ maj i g := by
            rw [hnorm]
            have hw0 := (PeterssonAnalytic.weight_pos w (g : AdelicGL2 (𝓞 F) F)).le
            calc ‖x (g : AdelicGL2 (𝓞 F) F)‖ * ‖G z g‖ * ‖y (g : AdelicGL2 (𝓞 F) F)‖ *
                  NumberField.TateGlobal.ideleNorm F
                    (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w)
                = (‖x (g : AdelicGL2 (𝓞 F) F)‖ * ‖y (g : AdelicGL2 (𝓞 F) F)‖ *
                    NumberField.TateGlobal.ideleNorm F
                      (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w)) *
                    ‖G z g‖ := by ring
              _ ≤ (‖x (g : AdelicGL2 (𝓞 F) F)‖ * ‖y (g : AdelicGL2 (𝓞 F) F)‖ *
                    NumberField.TateGlobal.ideleNorm F
                      (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 F) F)) ^ (-w)) *
                    (|M i| * (1 + archHeight F (glArch (𝓞 F) F
                      ((g : AdelicGL2 (𝓞 F) F) * (t i)⁻¹))) ^ (N i)) :=
                  mul_le_mul_of_nonneg_left hGb (by positivity)
              _ = maj i g := by simp only [hmaj]; ring
          have hnonneg : ∀ j, 0 ≤ ((· * t j) '' integralWindowedSiegelSet F c u).indicator (maj j)
              (g : AdelicGL2 (𝓞 F) F) := by
            intro j
            apply Set.indicator_nonneg
            intro g' _
            rw [hmaj]
            have := PeterssonAnalytic.weight_pos w g'
            have := archHeight_pos F (glArch (𝓞 F) F (g' * (t j)⁻¹))
            positivity
          calc ‖Φ z g‖ ≤ maj i g := hterm
            _ = ((· * t i) '' integralWindowedSiegelSet F c u).indicator (maj i)
                (g : AdelicGL2 (𝓞 F) F) :=
                (Set.indicator_of_mem hgi _).symm
            _ ≤ Mg g := by
                rw [hMg]
                exact Finset.single_le_sum (f := fun j =>
                  ((· * t j) '' integralWindowedSiegelSet F c u).indicator (maj j)
                  (g : AdelicGL2 (𝓞 F) F)) (fun j _ => hnonneg j) (Finset.mem_univ i)

    have heq : (fun s : ℂ => ∫ g in 𝓕, Φ s g ∂μ) =
        fun s => ∫ g : 𝓕, Φ s (g : AdelicGL2 (𝓞 F) F) ∂(μ.comap Subtype.val) :=
      funext hsub
    show AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, Φ s g ∂μ) U
    rw [heq]
    exact hgoal
  ·
    intro s₀ σ₁ E hE s hs _
    show (∫ g in 𝓕, Φ s g ∂μ) = (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y
    unfold peterssonIntegral
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hΦ, hE s g hs]
    ring

end AutomorphicForm
