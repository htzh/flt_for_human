/-
  The complex-place Iwasawa analytic estimates.

  The nine public `AutomorphicForm.ComplexIwasawa.*` statements of
  `topics/automorphicForm/TOPIC-iwasawa-analytic-core.md`, each transcribed verbatim from its pin
  `Theorems/Thm_AutomorphicForm_ComplexIwasawa_<name>.lean` wrapper (the statement authority) and
  proved by a one-line application of the corresponding
  `AutomorphicForm.ComplexIwasawa.Engine.<name>` kernel of the tier-3 engine
  (`Complex/{Core,Decay,UniformDecay,Continuation}.lean`). The engines stay tier 3 and are recorded
  in `spec/UNWIRED-PUBLIC.md`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`.
-/
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Core
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Decay
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.UniformDecay
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Continuation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory ComplexConjugate
open AutomorphicForm.ComplexIwasawa
open scoped ContDiff FourierTransform

namespace AutomorphicForm.ComplexIwasawa

-- pin: contDiff_and_exists_bound_iteratedFDeriv_kC_apply (Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:8)
theorem contDiff_and_exists_bound_iteratedFDeriv_kC_apply
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => kC g w i j)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
        ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C :=
  Engine.contDiff_and_exists_bound_iteratedFDeriv_kC_apply hg

-- pin: exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact (Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:12)
theorem exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C :=
  Engine.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact 𝒢 h𝒢 hdet n

-- pin: kC_mem_specialUnitaryGroup (Theorems/Thm_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:8)
theorem kC_mem_specialUnitaryGroup
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Engine.kC_mem_specialUnitaryGroup hg z

-- pin: weyl_mul_unipotent_mul_eq_borel_mul_kC (Theorems/Thm_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean:8)
theorem weyl_mul_unipotent_mul_eq_borel_mul_kC
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![-g.det / (radC g z : ℂ),
            (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
           0, (radC g z : ℂ)] * kC g z :=
  Engine.weyl_mul_unipotent_mul_eq_borel_mul_kC hg z

-- pin: exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact (Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean:11)
theorem exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (_hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M :=
  Engine.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact 𝒢 _h𝒢 _hdet κ₀ κ₁ _hκ₀

-- pin: norm_fourierIntegral_cpow_radC_mul_le_polyDecay (Theorems/Thm_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:10)
theorem norm_fourierIntegral_cpow_radC_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {u : ℂ} (hu : 2 < u.re)
    {P : ℂ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖iteratedFDeriv ℝ n P z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  Engine.norm_fourierIntegral_cpow_radC_mul_le_polyDecay hg hu hPC hPB L hc hL N

-- pin: contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact (Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:12)
theorem contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (_hU : IsCompact U) (n : ℕ) :
    (∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u)))) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖ ≤ K * radC g z ^ (-u.re) :=
  Engine.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    𝒢 _h𝒢 _hdet U _hU n

-- pin: exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact (Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean:12)
theorem exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU2 : ∀ u ∈ U, 2 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ z : ℂ, ‖iteratedFDeriv ℝ n (P g) z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P g z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  Engine.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
    𝒢 h𝒢 hdet U hU hU2 P hPC hPB L hc hL N

-- pin: continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (Theorems/Thm_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean:11)
theorem continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (a b : ℕ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ContinuousOn (fun p : ℂ × ℂ => j p.1 p.2) ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) ∧
    (∀ ζ : ℂ, DifferentiableOn ℂ (fun w : ℂ => j w ζ) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ‖j w ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  Engine.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral a b

end AutomorphicForm.ComplexIwasawa
