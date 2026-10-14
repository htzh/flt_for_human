/-
  The unramified local intertwining integral: the headline
  `AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion`
  together with the pin's own public implementation lemma `_impl`.

  Ported from the pin's `FinGKFold_Main` section:
  * the proof is `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`
    lines 1959–2085 (`integral_unramifiedWeylIntegrand_impl`), whose statement is also the
    public `solution` at line 2093;
  * the headline's binders are the `Theorems/` wrapper
    `Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`
    verbatim (the checker diffs that text, not the `S_` file's section-variable form).

  The residual prelude it consumes is homed in `TateGlobal/WeylShell.lean`; the rest of the
  prelude is in `TateGlobal/WeylPrelude.lean` and the T1 `TateGlobal` modules. The port keeps
  the pin's `_impl` public (it is the pin's `solution`'s proof and the natural target for a
  consumer), and states the headline at the wrapper's explicit binders.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylShell

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open WithZero Multiplicative
open scoped NNReal ENNReal Pointwise
open LanglandsTunnell.TateLocal

noncomputable section

namespace NumberField

namespace TateGlobal

namespace WeylUnramified

open WeylPrelude WeylShell LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge

set_option linter.style.haveILetI false in
set_option linter.overlappingInstances false in
-- pin: integral_unramifiedWeylIntegrand_impl (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1959)
theorem integral_unramifiedWeylIntegrand_impl
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
  haveI : μ.Regular := inferInstance

  obtain ⟨π, hπ, -⟩ := exists_irreducible_valued (v := v)

  set O : Set (v.adicCompletion F) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  set A : ℂ := ((χ ϖ : ℂˣ) : ℂ) with hA
  set N : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) with hN
  set t : ℂ := A * N ^ (-(2 * s)) with ht
  set g : v.adicCompletion F → ℂ :=
    fun y => charExt χ⁻¹ y * (((modulus y : ℝ)) : ℂ) ^ (-(2 * s + 1)) with hg
  set μO : ℝ := μ.real O with hμO

  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hQN : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) = N := by
    rw [hN, normQ]
    push_cast
    rfl
  have hNR : (1 : ℝ) ≤ ((normQ v : ℝ≥0) : ℝ) := by exact_mod_cast hq1
  have hN0 : N ≠ 0 := by
    rw [← hQN]
    exact_mod_cast (lt_of_lt_of_le one_pos hNR).ne'
  have hAP : ((χ (piUnit hπ) : ℂˣ) : ℂ) = A := by
    rw [hA, char_eq_char_piUnit hπ hχ ϖ hϖ]

  have hpow : N ^ (-(2 * s + 1)) = N ^ (-(2 * s)) * N⁻¹ := by
    rw [show (-(2 * s + 1) : ℂ) = -(2 * s) + (-1) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one]
  have hr : ((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1)) = t * N⁻¹ := by
    rw [hAP, hQN, hpow, ht, mul_assoc]
  have hc0 : (((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ) = 1 - (((normQ v : ℝ≥0) : ℝ))⁻¹ := by
    rw [NNReal.coe_sub (inv_le_one_of_one_le₀ hq1)]
    push_cast
    ring

  have hterm : ∀ m : ℕ, ∫ x in negShell hπ m, g x ∂μ
      = (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * t ^ m) := by
    intro m
    rw [hg, setIntegral_negShell μ hπ hχ (-(2 * s + 1)) m, hr, measureReal_negShell μ hπ m, hc0, ← hμO]
    have hNt : (((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (m + 1) * (t * N⁻¹) ^ (m + 1) = t ^ (m + 1) := by
      rw [← mul_pow, hQN, mul_comm t N⁻¹, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
    push_cast
    calc (((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (m + 1) * (1 - ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) * (μO : ℂ)
          * (t * N⁻¹) ^ (m + 1)
        = (1 - ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) * (μO : ℂ)
          * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (m + 1) * (t * N⁻¹) ^ (m + 1)) := by ring
      _ = (1 - ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) * (μO : ℂ) * (t * t ^ m) := by rw [hNt, pow_succ']
  have hnorm : ∀ m : ℕ, ∫ x in negShell hπ m, ‖g x‖ ∂μ
      = ((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t‖) * ‖t‖ ^ m := by
    intro m
    rw [hg, setIntegral_norm_negShell μ hπ hχ (-(2 * s + 1)) m, hr, measureReal_negShell μ hπ m, hc0, ← hμO]
    have hNn : ‖(N : ℂ)⁻¹‖ = (((normQ v : ℝ≥0) : ℝ))⁻¹ := by
      rw [norm_inv, ← hQN, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    have hNt : (((normQ v : ℝ≥0) : ℝ)) ^ (m + 1) * ‖t * N⁻¹‖ ^ (m + 1) = ‖t‖ ^ (m + 1) := by
      rw [← mul_pow, norm_mul, hNn, mul_comm ‖t‖ _, ← mul_assoc,
        mul_inv_cancel₀ (lt_of_lt_of_le one_pos hNR).ne', one_mul]
    calc (((normQ v : ℝ≥0) : ℝ)) ^ (m + 1) * (1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t * N⁻¹‖ ^ (m + 1)
        = (1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ((((normQ v : ℝ≥0) : ℝ)) ^ (m + 1) * ‖t * N⁻¹‖ ^ (m + 1)) := by
          ring
      _ = ((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t‖) * ‖t‖ ^ m := by rw [hNt, pow_succ']; ring

  have ht1 : ‖t‖ < 1 := by rw [ht, hA, hN]; exact hs

  have hOc : Oᶜ = ⋃ m : ℕ, negShell hπ m := compl_integers_eq_iUnion_negShell hπ
  have hsum : Summable fun m : ℕ => ∫ x in negShell hπ m, ‖g x‖ ∂μ := by
    rw [show (fun m : ℕ => ∫ x in negShell hπ m, ‖g x‖ ∂μ)
        = fun m : ℕ => ((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t‖) * ‖t‖ ^ m from funext hnorm]
    exact (summable_geometric_of_lt_one (norm_nonneg _) ht1).mul_left _
  have hInt : IntegrableOn g Oᶜ μ := by
    rw [hOc]
    exact integrableOn_iUnion_of_summable_integral_norm (fun m => integrableOn_negShell μ hπ hχ _ m) hsum
  have htail : ∫ x in Oᶜ, g x ∂μ
      = (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * (1 - t)⁻¹) := by
    have h1 : HasSum (fun m : ℕ => ∫ x in negShell hπ m, g x ∂μ) (∫ x in Oᶜ, g x ∂μ) := by
      rw [hOc] at hInt ⊢
      exact hasSum_integral_iUnion (fun m => measurableSet_negShell hπ m) (negShell_disjoint hπ) hInt
    have h2 : HasSum (fun m : ℕ => (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * t ^ m))
        ((((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * (1 - t)⁻¹)) :=
      ((hasSum_geometric_of_norm_lt_one ht1).mul_left t).mul_left _
    rw [show (fun m : ℕ => ∫ x in negShell hπ m, g x ∂μ)
        = fun m : ℕ => (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * t ^ m) from funext hterm] at h1
    exact h1.unique h2

  have hOmeas : MeasurableSet O := (isCompact_integers (F := F) (v := v)).isClosed.measurableSet
  have hint1 : Integrable (O.indicator fun _ => (1 : ℂ)) μ :=
    (integrableOn_const ((measure_integers_lt_top' μ).ne)).integrable_indicator hOmeas
  have hint2 : Integrable (Oᶜ.indicator g) μ := hInt.integrable_indicator hOmeas.compl
  have h1t : (1 - t) ≠ 0 := by
    intro h0
    have : ‖t‖ = 1 := by rw [show t = 1 from (sub_eq_zero.mp h0).symm, norm_one]
    linarith
  have hw : (1 - t) * (1 - t)⁻¹ = 1 := mul_inv_cancel₀ h1t
  calc ∫ x, (O.indicator (fun _ => (1 : ℂ)) x + Oᶜ.indicator g x) ∂μ
      = (∫ x, O.indicator (fun _ => (1 : ℂ)) x ∂μ) + ∫ x, Oᶜ.indicator g x ∂μ := integral_add hint1 hint2
    _ = (μO : ℂ) + ∫ x in Oᶜ, g x ∂μ := by
        rw [integral_indicator_const (1 : ℂ) hOmeas, integral_indicator hOmeas.compl, Complex.real_smul,
          mul_one, hμO]
    _ = (μO : ℂ) + (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * (1 - t)⁻¹) := by rw [htail]
    _ = (μO : ℂ) + (1 - N⁻¹) * (μO : ℂ) * (t * (1 - t)⁻¹) := by
        have hC : ((((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ)) : ℂ) = (1 - N⁻¹) * (μO : ℂ) := by
          rw [← hQN]
          push_cast
          ring
        rw [hC]
    _ = (μO : ℂ) * (1 - A * N ^ (-(2 * s + 1))) * (1 - t)⁻¹ := by
        rw [hpow, ← mul_assoc A, ← ht]
        linear_combination (-(μO : ℂ)) * hw

-- pin: integral_unramifiedWeylIntegrand_adicCompletion (Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:11)
theorem integral_unramifiedWeylIntegrand_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
  integral_unramifiedWeylIntegrand_impl F v μ ϖ hϖ χ hχ s hs

end WeylUnramified

end TateGlobal

end NumberField
