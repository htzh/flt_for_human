/-
  The façade of the Bruhat-transversal / Weyl-integrand trio.

  Three declarations: the consumed headlines
  `AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half`,
  `AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half` and
  `AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half`. Each
  statement is the pin wrapper `Theorems/Thm_AutomorphicForm_*.lean` verbatim
  (playbook §4: the wrapper is the statement authority), and each proof is the
  corresponding cap of `AutomorphicForm/Adelic/WeylIntegrable/Caps.lean`:

  * `bruhatTransversal_summand_norm_summable_of_re_gt_half` —
    `AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half_impl`
    (pin A 2692, proved from `…/WeylIntegrable/UniformBound.lean`'s
    `bruhatTransversal_summand_norm_summable`);
  * `continuous_bruhatTransversal_tsum_of_re_gt_half` —
    `AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half_impl`
    (pin B 2733), itself `AutomorphicForm.RhSContinuity.rhs_hole` (pin B 2696);
  * `weylIntertwiningIntegrand_integrable_of_re_gt_half` —
    `AutomorphicForm.WeylIntegrable.weylIntertwiningIntegrand_integrable_of_re_gt_half_impl`
    (pin A 2341), written once for the pair and the cousin in
    `…/WeylIntegrable/Assembly.lean`.

  The rest of the theory stays public in the unlisted tier-3 modules
  (`LatticeEstimates`, `Assembly`, `UniformBound`, `Caps`) and the landed gate;
  `spec/UNWIRED-PUBLIC.md` lists what they hold. Only these three headlines are
  checked, so this module declares nothing else.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrappers are
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean
  and the proof silos are the three `P2M/Sol/S_AutomorphicForm_*` files of the same pin.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Caps

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

namespace AutomorphicForm

-- pin: AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2747)
theorem bruhatTransversal_summand_norm_summable_of_re_gt_half
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

-- pin: AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half (S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean:2777)
theorem continuous_bruhatTransversal_tsum_of_re_gt_half
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

-- pin: AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half (S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean:2403)
theorem weylIntertwiningIntegrand_integrable_of_re_gt_half
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
