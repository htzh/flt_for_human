/-
  SET-AF15 consumer: the two places where the three headlines of this set are *used*.

  **Zone 1 — the decomposition meets the induced-section law.** `exists_mem_adelicBorel_mul_eq`
  splits an adelic point as `g = b * k` with `b` in the adelic Borel and `k` integral at the finite
  places with row-isometric archimedean components. `IsInducedSection` (the defining law of
  `AutomorphicForm/Adelic/InducedSection.lean`) says how a section transforms by the Borel: for
  `b ∈ adelicBorel`, `φ (b * g) = χ₁ b₀₀ · χ₂ b₁₁ · φ g`. Composing the two reads the value of an
  induced section at an arbitrary `g` off its `k`-part, with the character factor
  `χ₁ (borelDiagFst b) · χ₂ (borelDiagSnd b)` explicit — the statement the eight rows this set
  readies build on. The `∃ hb : …` in the conclusion is what lets the diagonal characters be
  applied at all: `borelDiagFst`/`borelDiagSnd` are maps on the *subtype* `↥(adelicBorel …)`.

  **Zone 2 — the general evaluations return the special ones.** At `k = 0` the real row
  `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` and at `a = b = 0`,
  `t = 2s + 1` the complex row `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` are exactly
  the integrands of SET-AF14's two special evaluations (`integral_one_add_sq_cpow_neg_eq_GammaReal_div`,
  `integral_one_add_norm_sq_cpow_neg_eq_pi_div`), and their values are the same numbers:
  `Γ_ℝ(2s)·Γ_ℝ(2s+1)/(Γ_ℝ(2s+1)·Γ_ℝ(2s+1)) = Γ_ℝ(2s)/Γ_ℝ(2s+1)` and
  `π·0!·Γ(2s+1-1)/Γ(2s+1) = π/(2s)`. Both reductions are proved, not asserted: the general row's
  value is rewritten *to* the special row's value through those arithmetic identities.

  The file imports the two new modules and `InducedSection.lean`. **Deviation from the order's
  §3 gate 6**, which says the induced-section law is "imported through the new module": it is not —
  neither `AdelicIwasawa` nor `ArchAtomGeneral` imports `InducedSection.lean` (checked with
  `#check @AutomorphicForm.IsInducedSection` against both), so the law's module is named here. No port
  module's import list is touched.
-/
import FLTForHuman.AutomorphicForm.Adelic.AdelicIwasawa
import FLTForHuman.AutomorphicForm.Adelic.ArchAtomGeneral
import FLTForHuman.AutomorphicForm.Adelic.InducedSection

set_option autoImplicit false

noncomputable section

open MeasureTheory
open NumberField NumberField.AdelicLevel NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ComplexConjugate

namespace AutomorphicForm
namespace LocalIntertwining

/-! ### Zone 1 — the Borel decomposition, read through `IsInducedSection` -/

/-- **The decomposition meets the induced-section law.** An induced section is determined by its value
on the `k`-part of the Iwasawa decomposition, with the Borel character factor explicit. -/
example (F : Type) [Field F] [NumberField F]
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ b k : AdelicGL2 (𝓞 F) F,
      b ∈ adelicBorel (𝓞 F) F ∧
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
      ∃ hb : b ∈ adelicBorel (𝓞 F) F,
        φ g = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * φ k := by
  obtain ⟨b, k, hb, hk, harch, hg⟩ := exists_mem_adelicBorel_mul_eq F g
  refine ⟨b, k, hb, hk, harch, hb, ?_⟩
  rw [hg]
  exact hφ b hb k

/-! ### Zone 2 — the general evaluations return the special ones -/

/-- **The real row's value at `k = 0` is the `Γ_ℝ` ratio.** -/
example (s : ℂ) (hs : 0 < s.re) :
    (-Complex.I) ^ (0 : ℤ) * (Complex.Gammaℝ (2 * s) * Complex.Gammaℝ (2 * s + 1))
        / (Complex.Gammaℝ (2 * s + 1 + ((0 : ℤ) : ℂ)) * Complex.Gammaℝ (2 * s + 1 - ((0 : ℤ) : ℂ)))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) := by
  have hB : Complex.Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  simp only [zpow_zero, Int.cast_zero, add_zero, sub_zero, one_mul]
  rw [mul_div_mul_right _ _ hB]

/-- **The real row at `k = 0` *is* SET-AF14's special real evaluation.** -/
example (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (0 : ℤ)
        * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
  rw [integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal 0 s hs,
    integral_one_add_sq_cpow_neg_eq_GammaReal_div s hs]
  have hB : Complex.Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  simp only [zpow_zero, Int.cast_zero, add_zero, sub_zero, one_mul]
  rw [mul_div_mul_right _ _ hB]

/-- **The complex row's value at `a = b = 0`, `t = 2s+1` is `π/(2s)`.** -/
example (s : ℂ) (hs : 0 < s.re) :
    (Real.pi : ℂ) * ((0 : ℕ).factorial : ℂ) * Complex.Gamma ((2 * s + 1) - 1 - ((0 : ℕ) : ℂ))
        / Complex.Gamma (2 * s + 1)
      = (Real.pi : ℂ) / (2 * s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have h2 : (2 * s : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hs0
  have hG : Complex.Gamma (2 * s) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.mul_re]
    norm_num
    linarith
  have hG1 : Complex.Gamma (2 * s + 1) = (2 * s) * Complex.Gamma (2 * s) :=
    Complex.Gamma_add_one (2 * s) h2
  rw [show (2 * s + 1) - 1 - ((0 : ℕ) : ℂ) = 2 * s by push_cast; ring, hG1]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  field_simp

/-- **The complex row at `a = b = 0`, `t = 2s+1` *is* SET-AF14's special complex evaluation.** -/
example (s : ℂ) (hs : 0 < s.re) :
    ∫ z : ℂ, z ^ (0 : ℕ) * (starRingEnd ℂ z) ^ (0 : ℕ)
        * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))
      = ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have ht : (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)) / 2 + 1 < (2 * s + 1).re := by
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  rw [integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg 0 0 (2 * s + 1) ht,
    integral_one_add_norm_sq_cpow_neg_eq_pi_div s hs]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have h2 : (2 * s : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hs0
  have hG : Complex.Gamma (2 * s) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.mul_re]
    norm_num
    linarith
  have hG1 : Complex.Gamma (2 * s + 1) = (2 * s) * Complex.Gamma (2 * s) :=
    Complex.Gamma_add_one (2 * s) h2
  rw [ite_eq_left rfl,
    show (2 * s + 1) - 1 - ((0 : ℕ) : ℂ) = 2 * s by push_cast; ring, hG1]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  field_simp

end LocalIntertwining
end AutomorphicForm
