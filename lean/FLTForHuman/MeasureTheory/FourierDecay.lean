/-
  A coercive linear map makes the Fourier integral of a `C^n` function decay like `‖w‖^{-n}`.

  For a real-linear `L : V →L[ℝ] W →L[ℝ] ℝ` that is coercive
  (`∀ w, ∃ v, ‖v‖ ≤ 1 ∧ c‖w‖ ≤ ‖L v w‖` with `c ≥ 0`), a `C^n` function `f : V → E` with
  integrable iterated derivative norms satisfies

  `(c‖w‖)^n * ‖∫ f e^{-i⟨L v, w⟩}‖ ≤ 2^n * Σ_{j ≤ n} ∫ ‖D^j f‖`.

  Repeated integration by parts against the coercive direction on the left gives polynomial
  decay of the Fourier integral for free, which is how both the complex-place and the real-place
  archimedean estimates turn the symbol bounds on `rad^{-u}` into rapid decay in the frequency
  variable. `gate_degenerate` is the `c = 0` corner (`L = 0`, witnessed by `v = 0`).

  This is the pin's `M4aP3B.FourierDecay` block, proved separately inside
  `S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean`
  (lines 1512–1564) and `S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean`
  (lines 859–911), statements byte-identical. It is generic measure/Fourier analysis over an
  arbitrary real normed space, so its home is `MeasureTheory/`, not the Iwasawa theory, and the
  two waves import it once instead of each transcribing it (playbook §2.4, §3.7, §5). It rests on
  mathlib's `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`
  (`Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:636`).

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean
-/
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false

noncomputable section

open MeasureTheory Real VectorFourier
open scoped FourierTransform

namespace MeasureTheory.FourierDecay

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

-- pin: pow_mul_norm_fourierIntegral_le_of_coercive (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1524)
theorem pow_mul_norm_fourierIntegral_le_of_coercive (L : V →L[ℝ] W →L[ℝ] ℝ)
    {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) μ)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w : W, ∃ v : V, ‖v‖ ≤ 1 ∧ c * ‖w‖ ≤ ‖L v w‖) (w : W) :
    (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by
  obtain ⟨v, hv1, hvw⟩ := hL w
  have h'f' : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ) → (j : ℕ∞) ≤ (n : ℕ) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) μ := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    subst hk0
    simpa using h'f j (by exact_mod_cast hj)
  have key := pow_mul_norm_iteratedFDeriv_fourierIntegral_le L (K := (0 : ℕ)) (N := (n : ℕ))
    (hf := hf) h'f' (k := 0) (n := n) le_rfl le_rfl v w
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at key
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ∂μ
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
    rw [Finset.sum_product, zero_add, Finset.range_one, Finset.sum_singleton]
    simp
  rw [hsum] at key
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  calc (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ |L v w| ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖ := by
        gcongr
        exact hvw.trans_eq (Real.norm_eq_abs _)
    _ ≤ ‖v‖ ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        simpa using key
    _ ≤ 1 ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        gcongr
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by norm_num

omit [FiniteDimensional ℝ V] [BorelSpace V] in
-- pin: gate_degenerate (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1562)
theorem gate_degenerate (μ : Measure V) [μ.IsAddHaarMeasure] (w : W) :
    ∃ v : V, ‖v‖ ≤ 1 ∧ (0 : ℝ) * ‖w‖ ≤ ‖(0 : V →L[ℝ] W →L[ℝ] ℝ) v w‖ :=
  ⟨0, by simp, by simp⟩

end MeasureTheory.FourierDecay
