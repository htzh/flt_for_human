/-
  SET-AF89B consumer: `Kf`-smooth, arch-`K`-finite functions are finite sums of their kind.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/KfSmoothSpan.lean` carries
  `exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth`: for a continuous,
  archimedean-`K`-finite, `Kf`-smooth `φ`, the right translates of `φ` by the compact open
  `Kf = maximalCompactAway ∅` split as finite sums `∑ j, a j k * e j` with each `e j` again
  arch-`K`-finite and `Kf`-smooth.

  **The reading.** The row is evaluated at `k = 1`. The translate hypothesis at the identity is
  vacuous (`glFin 1 = 1` is integral, `glArch 1 = 1`, `IsRowIsometry 1`), so the conclusion reads
  `φ = ∑ j, a j 1 * e j`: the *whole function* is a finite linear combination of functions that
  are themselves arch-`K`-finite and `Kf`-smooth. That is the finite-dimensionality content the
  row is used for, stated without the translate parameter.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF89BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.KfSmoothSpan

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

namespace AutomorphicFormSetAF89BConsumer

/-- **The reading.** A continuous arch-`K`-finite `Kf`-smooth function is a finite ℂ-linear
combination of functions of the same kind, with the combination read off the row at `k = 1`. -/
theorem exists_finite_sum_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) (hφc : Continuous φ) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (e : Fin m → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, IsArchKFinite F (e j) ∧ IsKfSmooth F (e j)) ∧
      ∀ x, φ x = ∑ j, c j * e j x := by
  obtain ⟨m, e, a, he, -, hmain⟩ :=
    exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth F φ hφK hφf hφc
  refine ⟨m, fun j => a j 1, e, fun j => (he j).2, fun x => ?_⟩
  simpa using hmain 1 (by simp) (fun w => by simpa using isRowIsometry_one) x

end AutomorphicFormSetAF89BConsumer
