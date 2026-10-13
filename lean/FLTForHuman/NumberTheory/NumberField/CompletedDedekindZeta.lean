/-
  The façade of the completed Dedekind zeta package.

  One declaration: the consumed headline `NumberField.exists_completedDedekindZeta_package`.
  Its statement is the pin wrapper
  `Theorems/Thm_NumberField_exists_completedDedekindZeta_package.lean` verbatim
  (playbook §4: the wrapper is the statement authority), and its proof is the
  development's own `exists_completedDedekindZeta_package` in
  `…/CompletedDedekindZeta/Bounds.lean` — the pin's `solution` (pin 7532).

  The rest of the theory stays public in the unlisted development modules
  (`Lattice`, `Poisson`, `Places`, `ThetaKernel`, `Mellin`, `Unfolding`,
  `CompletedZeta`, `Hadamard`, `Bounds`); `spec/UNWIRED-PUBLIC.md` lists what they
  hold, and a consumer that needs one of their declarations imports the module
  directly.  Only this headline is checked, so this module declares nothing else.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrapper is
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_exists_completedDedekindZeta_package.lean
  and the proof's silo is
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Bounds

namespace NumberField

theorem exists_completedDedekindZeta_package (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) :=
  NumberField.CompletedDedekindZeta.exists_completedDedekindZeta_package K

end NumberField
