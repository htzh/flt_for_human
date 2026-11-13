/-
  Consumer zone for the two AF51A modules:

  * `FLTForHuman/NumberTheory/NumberField/CompletedDedekindZeta/EulerProduct.lean`
    (headline `NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul`);
  * `FLTForHuman/NumberTheory/NumberField/CompletedDedekindZeta/RegularizedZeta.lean`
    (headline `NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero`).

  Both are consumed at the concrete number field `K = ℚ`, where every instance
  (`NumberField ℚ`, `IsDedekindDomain (𝓞 ℚ)`, `Fintype`/`Finite` data) is available
  without hypotheses:

  * `rat_regularized_neg_two` — reads the regularized-zeta headline at `K = ℚ` and
    *executes* its last component at `n = 0`: the entire function `R` supplied for the
    rationals vanishes at `-2` (the first trivial zero of the zeta function);
  * `rat_eulerProduct_differentiableAt_two` — reads the Euler-product headline at
    `K = ℚ`, empty exceptional set `T = ∅`, and composes its `DifferentiableOn`
    conclusion with the openness of the region `{s | 1/2 < re s} \ {1}` to obtain
    differentiability *at* `s = 2`, together with the value of the continued product
    there from the headline's second component evaluated on `re s > 1`.

  Both are real compositions (no `#check`, no `sorry`): the hypotheses of the headline
  are discharged at the concrete field and the conclusion is used, not just stated.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF51AConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.EulerProduct
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.RegularizedZeta

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField Filter Topology Complex
open scoped Topology Classical

namespace NumberFieldSetAF51AConsumer

/-- The regularized zeta function of `ℚ`, at the first negative even integer.

The headline is instantiated at `K = ℚ`; its final component
`∀ n : ℕ, R (-2 * (n + 1)) = 0` is then *applied* at `n = 0`, giving `R (-2) = 0`. -/
theorem rat_regularized_neg_two :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ R 1 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta ℚ s) ∧
      R (-2) = 0 := by
  obtain ⟨R, hd, h1, heq, h0⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero ℚ
  exact ⟨R, hd, h1, heq, by simpa using h0 0⟩

/-- The Euler product of `ℚ` with no exceptional places: differentiability at `s = 2`.

The headline at `K = ℚ`, `T = ∅` supplies `L` differentiable on
`{s : ℂ | 1/2 < re s} \ {1}`; that region is open and contains `2`, so `L` is
differentiable *at* `2`.  The headline's product formula is evaluated there on the
half-plane `1 < re s`. -/
theorem rat_eulerProduct_differentiableAt_two :
    ∃ L : ℂ → ℂ, DifferentiableAt ℂ L 2 ∧
      L 2 = ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) //
          v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ := by
  obtain ⟨L, hd, heq, -⟩ :=
    NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
      ℚ ∅
  have hopen : IsOpen ({s : ℂ | (1 : ℝ) / 2 < s.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hmem : (2 : ℂ) ∈ ({s : ℂ | (1 : ℝ) / 2 < s.re} \ {1}) := by
    refine ⟨?_, by norm_num⟩
    simpa using (by norm_num : (1 : ℝ) / 2 < 2)
  exact ⟨L, hd.differentiableAt (hopen.mem_nhds hmem), heq 2 (by norm_num)⟩

end NumberFieldSetAF51AConsumer
