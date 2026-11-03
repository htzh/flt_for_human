/-
  Cross-module wire test for SET-AF10 (the complex Casimir algebra closes).

  A `spec/` probe, not a library module. **One zone**, and it is a real composition of the set's two
  halves on one and the same function `φ`:

  * the **left-Casimir bridge**
    (`leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` in
    `Adelic/ArchCasimirComplex.lean`) computes the two left-acting complex Casimirs of a
    complex-smooth `φ` — the holomorphic `Ld`-expression and its conjugate — as
    `archCasimirAtComplex hw φ` and `archCasimirBarAtComplex hw φ` at every point `y`;
  * the **Casimir decomposition**
    (`archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex`, same module)
    computes the sum of those two Casimirs in terms of the compact Casimir and the
    `iH`/`E+F⁻`/`iF⁻−iE` derivatives.

  So the zone substitutes the bridge's two pointwise identities into the decomposition and concludes
  that the *explicit left-acting expressions* add up to the decomposition's right-hand side at `y`.
  It dies if either headline loses its statement, and its conclusion is about the left-Casimir
  algebra, not about the Casimir alone. It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimirComplex

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace SetAF10ComplexCasimirConsumer

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

/-- **Zone A — the left complex Casimir sum equals the Casimir decomposition.** For a complex-smooth
`φ`, the pin's left-acting `Ld`-expression and its conjugate, evaluated at any `y`, are the two
Casimirs by the bridge, and by the decomposition their sum is the compact Casimir minus the
`H`/`E`/`F⁻`/`i`-derivative combination. The two headlines are read at the same `φ` and the same
`y`. -/
theorem leftCasimir_add_barCasimir_eq_decomposition
    (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 F) F,
    -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H φ) y + ((-Complex.I) : ℂ) * L .H (L .iH φ) y + ((-Complex.I) : ℂ) * L .iH (L .H φ) y + (-1 : ℂ) * L .iH (L .iH φ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H φ y + ((-Complex.I) : ℂ) * L .iH φ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm φ) y + ((-Complex.I) : ℂ) * L .E (L .iFm φ) y + ((-Complex.I) : ℂ) * L .iE (L .Fm φ) y + (-1 : ℂ) * L .iE (L .iFm φ) y)) +
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H φ) y + (Complex.I : ℂ) * L .H (L .iH φ) y + (Complex.I : ℂ) * L .iH (L .H φ) y + (-1 : ℂ) * L .iH (L .iH φ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H φ y + (Complex.I : ℂ) * L .iH φ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm φ) y + (Complex.I : ℂ) * L .E (L .iFm φ) y + (Complex.I : ℂ) * L .iE (L .Fm φ) y + (-1 : ℂ) * L .iE (L .iFm φ) y)) =
      ((1 / 8 : ℂ) • archKCasimirAtComplex hw φ
        - (1 / 8 : ℂ) • (archDerivAtComplex hw .H (archDerivAtComplex hw .H φ) +
            (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ) +
              archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ)) +
            (archDerivAtComplex hw .iFm (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ) -
              archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ)))) y := by
  intro L y
  obtain ⟨hleft, hbar⟩ :=
    leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex F w hw φ hφ y
  have hdec := congrFun
    (archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex F hw φ hφ) y
  rw [Pi.add_apply] at hdec
  rw [hleft, hbar]
  exact hdec

end SetAF10ComplexCasimirConsumer
