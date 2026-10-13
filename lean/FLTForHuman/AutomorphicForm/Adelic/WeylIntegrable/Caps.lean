/-
  The per-file caps of the Bruhat-transversal / Weyl-integrand trio.

  Each of the three pin silos ends with a `..._impl` and a `solution`, both stating
  the wrapper's headline; B additionally carries the 22-line
  `AutomorphicForm.RhSContinuity.rhs_hole` (`continuousOn_tsum` under the shared
  uniform bound, then `continuousAt`). The shared
  `weylIntertwiningIntegrand_integrable_of_re_gt_half_impl` is public in the pair and
  `private` with a `_root_` escape in the cousin; it is written once, in
  `Assembly.lean`, and the cousin's `solution` invokes it. The three `solution`s are
  given a dev-only file suffix so that the flattened pin tail `solution` does not
  collide; their `-- pin:` comments carry the pin name.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  (2692–2763), `S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean`
  (2696–2792) and `S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean`
  (2403–2420) (pinned `aa2d8b3`).
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.UniformBound
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

noncomputable section

namespace AutomorphicForm

namespace RhSContinuity

open AutomorphicForm.WeylIntegrable in

-- pin: rhs_hole (S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean:2696)
theorem rhs_hole
    (F : Type) [Field F] [NumberField F]
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ)) :
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    Continuous (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) := by
  intro hα μ ν hμ hν s hs φ hφ hφc
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds g₀
  obtain ⟨M, hM, hle⟩ :=
    bruhatTransversal_norm_le_summable_uniform F α hα hαΔ μ ν hμ hν s hs φ hφ hφc hK
  exact (continuousOn_tsum
      (fun ξ => (hφc.comp (continuous_const_mul _)).continuousOn)
      hM (fun ξ g hg => hle g hg ξ)).continuousAt hKn

end RhSContinuity

-- pin: continuous_bruhatTransversal_tsum_of_re_gt_half_impl (S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean:2733)
theorem continuous_bruhatTransversal_tsum_of_re_gt_half_impl
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    Continuous (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) := by
  intro α
  exact RhSContinuity.rhs_hole F α (fun x => rfl)

-- pin: bruhatTransversal_summand_norm_summable_of_re_gt_half_impl (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2692)
theorem bruhatTransversal_summand_norm_summable_of_re_gt_half_impl
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Summable (fun ξ : F => ‖φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) := by
  intro α hα μ ν hμ hν s hs φ hφ hφc g
  exact WeylIntegrable.bruhatTransversal_summand_norm_summable F α hα (fun x => rfl) μ ν hμ hν s hs φ hφ hφc g

-- The pin's A `solution` (A 2747) is the same statement as A's `_impl`; the port
-- renames it with a file suffix so the three flattened `solution` tails do not
-- collide, and records the pin name in the provenance comment.
-- pin: solution (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2747)
theorem bruhatTransversal_summand_norm_summable_of_re_gt_half_solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Summable (fun ξ : F => ‖φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) :=
  bruhatTransversal_summand_norm_summable_of_re_gt_half_impl F

-- pin: solution (S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean:2777)
theorem continuous_bruhatTransversal_tsum_of_re_gt_half_solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    Continuous (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) :=
  continuous_bruhatTransversal_tsum_of_re_gt_half_impl F

-- The cousin's `_impl` (C 2339) is the same declaration as the shared public one,
-- written once in `Assembly.lean`; only C's `solution` is transcribed here.
-- pin: solution (S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean:2403)
theorem weylIntertwiningIntegrand_integrable_of_re_gt_half_solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    Integrable (fun x : AdeleRing (𝓞 F) F =>
      φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) :=
  WeylIntegrable.weylIntertwiningIntegrand_integrable_of_re_gt_half_impl F

end AutomorphicForm

end
