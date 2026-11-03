/-
  SET-AF14 consumer: the two places, each composing an order-A row with an order-B row.

  The two zones below read the value of the atom's integral at `k = 0` (real place) and at
  `a₀ = b₀ = m = 0` (complex place) by composing

  * the order-A integrability row — `integrable_realAtom_and_integrable_moebiusShift` at
    `(a, b, c, d) = (1, 0, 0, 1)`, `k = 0`, and `integrable_complexAtom_and_integrable_moebiusShift` at
    `(a, b, c, d) = (1, 0, 0, 1)`, `a₀ = b₀ = m = 0` — whose first conjunct is the *integrability* of
    the atom, with
  * the order-B evaluation row — `integral_one_add_sq_cpow_neg_eq_GammaReal_div` (real place, value
    `Γ_ℝ(2s)/Γ_ℝ(2s+1)`) and `integral_one_add_norm_sq_cpow_neg_eq_pi_div` (complex place, value
    `π/(2s)`) — whose integrand is exactly the `k = 0` / `a₀ = b₀ = 0` atom.

  At `k = 0` the atom's phase factor is `1` (`zpow_zero`), and at `a₀ = b₀ = 0` the two power factors are
  `1` and the exponent's `- m/2` vanishes, so the atom *is* the evaluation row's integrand; the two zones
  below say so and hand the evaluation row's statement the integrability the order-A row supplies.
  Both zones are `example`s over the two module imports only: no new hypothesis is needed on the consumer
  side, and no headline is weakened.
-/
import FLTForHuman.AutomorphicForm.Adelic.LocalAtomIntegrable
import FLTForHuman.AutomorphicForm.Adelic.ArchAtomValues

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace AutomorphicForm
namespace LocalIntertwining

/-- **The real place.** With `(a, b, c, d) = (1, 0, 0, 1)` and `k = 0` the real atom is the integrand of
`integral_one_add_sq_cpow_neg_eq_GammaReal_div` at `s = σ`, so it is integrable (order A) and its integral
is `Γ_ℝ(2σ)/Γ_ℝ(2σ+1)` (order B). -/
example (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : ℝ => (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-((σ : ℂ) + 1 / 2)))
      ∧ ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-((σ : ℂ) + 1 / 2))
          = Complex.Gammaℝ (2 * (σ : ℂ)) / Complex.Gammaℝ (2 * (σ : ℂ) + 1) := by
  have hAtom := (integrable_realAtom_and_integrable_moebiusShift 1 0 0 1
    (by norm_num : (1 : ℝ) * 1 - 0 * 0 ≠ 0) 0 σ hσ).1
  refine ⟨?_, integral_one_add_sq_cpow_neg_eq_GammaReal_div (σ : ℂ) (by simpa using hσ)⟩
  refine hAtom.congr (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- **The complex place.** With `(a, b, c, d) = (1, 0, 0, 1)` and `a₀ = b₀ = m = 0` the complex atom is
the integrand of `integral_one_add_norm_sq_cpow_neg_eq_pi_div` at `s = σ`, so it is integrable (order A)
and its integral is `π/(2σ)` (order B). -/
example (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : ℂ => (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1)))
      ∧ ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) = (Real.pi : ℂ) / (2 * (σ : ℂ)) := by
  have hAtom := (integrable_complexAtom_and_integrable_moebiusShift 1 0 0 1
    (by norm_num : (1 : ℂ) * 1 - 0 * 0 ≠ 0) 0 0 0 (by norm_num) σ hσ).1
  refine ⟨?_, integral_one_add_norm_sq_cpow_neg_eq_pi_div (σ : ℂ) (by simpa using hσ)⟩
  refine hAtom.congr (Filter.Eventually.of_forall fun z => ?_)
  simp

end LocalIntertwining
end AutomorphicForm
