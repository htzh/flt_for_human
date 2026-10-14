/-
  The real-place Iwasawa analytic estimates.

  The four public `AutomorphicForm.RealIwasawa.*` statements of
  `topics/automorphicForm/TOPIC-iwasawa-analytic-core.md`, each transcribed verbatim from its pin
  `Theorems/Thm_AutomorphicForm_RealIwasawa_<name>.lean` wrapper (the statement authority) and
  proved by a one-line application of the corresponding
  `AutomorphicForm.RealIwasawa.Engine.<name>` kernel of the tier-3 engine
  (`Real/{Core,Decay,Continuation}.lean`). The engines stay tier 3 and are recorded in
  `spec/UNWIRED-PUBLIC.md`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`.
-/
import FLTForHuman.AutomorphicForm.Iwasawa.Real.Core
import FLTForHuman.AutomorphicForm.Iwasawa.Real.Decay
import FLTForHuman.AutomorphicForm.Iwasawa.Real.Continuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff FourierTransform

namespace AutomorphicForm.RealIwasawa

-- pin: contDiff_and_exists_bound_iteratedFDeriv_kR_apply (Theorems/Thm_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean:8)
theorem contDiff_and_exists_bound_iteratedFDeriv_kR_apply
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C :=
  Engine.contDiff_and_exists_bound_iteratedFDeriv_kR_apply hg

-- pin: norm_fourierIntegral_cpow_rad_mul_le_polyDecay (Theorems/Thm_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean:9)
theorem norm_fourierIntegral_cpow_rad_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  Engine.norm_fourierIntegral_cpow_rad_mul_le_polyDecay hg hu hPC hPB L hc hL N

-- pin: exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact (Theorems/Thm_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean:12)
theorem exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℝ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU1 : ∀ u ∈ U, 1 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℝ → ℝ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ x : ℝ, ‖iteratedFDeriv ℝ n (P g) x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P g x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  Engine.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
    𝒢 h𝒢 hdet U hU hU1 P hPC hPB L hc hL N

-- pin: continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (Theorems/Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:11)
theorem continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (k : ℤ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ContinuousOn (fun p : ℂ × ℝ => j p.1 p.2) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) ∧
    (∀ t : ℝ, DifferentiableOn ℂ (fun w : ℂ => j w t) {w : ℂ | 1 / 2 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | 1 / 2 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, ‖j w t‖ ≤ C * (1 + |t|) ^ (-(N : ℝ))) :=
  Engine.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral k

end AutomorphicForm.RealIwasawa
