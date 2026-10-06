/-
  The level-one `j`-invariant and its surjectivity.

  `j τ = E₄ τ ^ 3 / Δ τ` is the Hauptmodul of `SL(2, ℤ)`, and every complex number
  is `j τ` for some `τ ∈ ℍ`.  Both are **generic** level-one modular-form
  mathematics — not API of the weight-one package — so they are exported here at
  the neutral `ModularForm` namespace.  `ModularForms/WeightOne/LevelField.lean`
  keeps the pin's `WLight.j` / `WLight.j_surjective` as a shim over these, so the
  weight-one consumers are unchanged.

  Provenance.  The pin inlines both in
  `P2M/Sol/S_WLight_levelN_structure_package.lean:44` / `:46`
  (`anthropics/fermats-last-theorem@aa2d8b3`), where `WLight.j_surjective` is the
  third conjunct of the already-ported
  `WLight.levelOne_hauptmodul_package` (the `A4_j_surjective` pencil argument).
  This module restates that conjunct at the generic name; it does **not** re-prove
  it.  The pin's `E₄` / `discriminant` are mathlib's `ModularForm.E₄` /
  `ModularForm.discriminant`.

  Reference (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_levelN_structure_package.lean#L44-L47>
-/
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul

open scoped UpperHalfPlane

noncomputable section

namespace ModularForm

/-- The level-one `j`-invariant `j τ = E₄ τ ^ 3 / Δ τ`. -/
def j : ℍ → ℂ := fun τ => E₄ τ ^ 3 / discriminant τ

/-- Every complex number is the `j`-invariant of a point of `ℍ`.  (The pin's
`WLight.j_surjective`, restated at the generic name; the proof is the third
conjunct of `WLight.levelOne_hauptmodul_package`.) -/
theorem j_surjective : Function.Surjective j :=
  WLight.levelOne_hauptmodul_package.2.2.1

end ModularForm
