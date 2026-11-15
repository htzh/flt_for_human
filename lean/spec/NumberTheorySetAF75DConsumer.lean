/-
  Cross-module wire test for the circle of a global additive character and the uniqueness of the
  adelic Haar measure (`AF75D`).

  A `spec/` probe, not a library module. Two executed zones:

  * **Zone 1** reads `AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar` at `F = ℚ` and the
    port's standard global character (`NumberField.StandardAddChar.psiQ`, whose global-character
    structure is `isGlobalAddChar_psiQ`) at two concrete adèles of `𝔸_ℚ`: the origin, and the
    adèle that is `1/2` at the infinite place and `0` at every finite place. The second is not
    principal, so the modulus `1` there is the power argument of `norm_apply_le_one_of_bounded`
    rather than principal invariance; and the circle factorisation
    (`toCircleAddChar`, `coe_toCircleAddChar_apply`, `exists_compAddChar_eq_of_isGlobalAddChar`)
    is read at the same two points.
  * **Zone 2** reads
    `NumberField.AdelicHaar.exists_smul_eq_of_isAddHaarMeasure_adeleRing` at `F = ℚ` with
    `μ = ν = adelicAddHaar (𝓞 ℚ) ℚ`, and identifies the scalar as `1` by evaluating the
    proportionality on a nonempty open subset of the fundamental adelic box, which has finite and
    nonzero Haar measure.

  Every zone is a real composition — no `#check` — so deleting either module (or leaving a hole
  in it) breaks this file.
-/
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.NumberTheory.AdelicHaar.Uniqueness
import FLTForHuman.NumberTheory.NumberField.StandardGlobalAddCharRat
import FLTForHuman.NumberTheory.AdelicBox

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm MeasureTheory NumberField.AdelicHaar
open scoped NNReal ENNReal Pointwise

namespace NumberTheorySetAF75DConsumer

/-! ### Zone 1 — the global character `ψ_ℚ` takes values on the unit circle -/

/-- The adèle that is `1/2` at the unique infinite place of `ℚ` and `0` at every finite place:
the concrete non-principal point Zone 1 reads the modulus at. -/
private def halfAdele : AdeleRing (𝓞 ℚ) ℚ :=
  ((algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ) / 2), (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    AdeleRing (𝓞 ℚ) ℚ)

/-- Zone 1, first point: the standard global character of `ℚ` has modulus `1` at the origin. -/
theorem norm_psiQ_zero : ‖NumberField.StandardAddChar.psiQ (0 : AdeleRing (𝓞 ℚ) ℚ)‖ = 1 :=
  norm_apply_eq_one_of_isGlobalAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ 0

/-- Zone 1, second point: modulus `1` at the non-principal adèle `(1/2)_∞`. -/
theorem norm_psiQ_halfAdele : ‖NumberField.StandardAddChar.psiQ halfAdele‖ = 1 :=
  norm_apply_eq_one_of_isGlobalAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ halfAdele

/-- Zone 1, circle side: the `Circle`-valued character attached to `ψ_ℚ` has the same values, read
at both points through the inclusion `Circle → ℂ`. -/
theorem circle_values_at_two_points :
    ((toCircleAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ
          (0 : AdeleRing (𝓞 ℚ) ℚ) : Circle) : ℂ) = NumberField.StandardAddChar.psiQ 0 ∧
      ((toCircleAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ
          halfAdele : Circle) : ℂ) = NumberField.StandardAddChar.psiQ halfAdele :=
  ⟨coe_toCircleAddChar_apply ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ 0,
    coe_toCircleAddChar_apply ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ halfAdele⟩

/-- Zone 1, factorisation: `ψ_ℚ` is the composition of a `Circle`-valued additive character with
the inclusion `Circle → ℂ`. -/
theorem exists_circle_char :
    ∃ e : AddChar (AdeleRing (𝓞 ℚ) ℚ) Circle,
      Circle.coeHom.compAddChar e = NumberField.StandardAddChar.psiQ :=
  exists_compAddChar_eq_of_isGlobalAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ

/-! ### Zone 2 — the adelic Haar measure is unique up to a scalar, and the scalar is `1` -/

/-- Zone 2: at `F = ℚ` and `μ = ν = adelicAddHaar`, the scalar of the uniqueness row is `1`. It
is read off the row on a nonempty open subset `U` of the fundamental adelic box: finiteness of
the box gives `μ U ≠ ⊤` and `IsOpenPosMeasure` gives `μ U ≠ 0`, so the proportionality
`μ = c • μ` forces `c = 1` on `U`. -/
theorem scalar_eq_one_of_smul_self :
    ∃ c : NNReal, c = 1 ∧ adelicAddHaar (𝓞 ℚ) ℚ = c • adelicAddHaar (𝓞 ℚ) ℚ := by
  let : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
  have : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have hμ : (adelicAddHaar (𝓞 ℚ) ℚ).IsAddHaarMeasure :=
    isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  obtain ⟨c, -, hc⟩ :=
    exists_smul_eq_of_isAddHaarMeasure_adeleRing ℚ (adelicAddHaar (𝓞 ℚ) ℚ)
      (adelicAddHaar (𝓞 ℚ) ℚ)
  -- a nonempty open subset of the fundamental box, hence of finite and nonzero Haar measure
  obtain ⟨U, hUopen, hUne, hUbox⟩ := AdelicBox.exists_isOpen_subset_adelicBox (K := ℚ)
  have hbox : adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ) ≠ ⊤ :=
    ne_of_lt (AdelicBox.measure_adelicBox_lt_top ℚ (adelicAddHaar (𝓞 ℚ) ℚ))
  have hfin : adelicAddHaar (𝓞 ℚ) ℚ U ≠ ⊤ :=
    ne_top_of_le_ne_top hbox (measure_mono hUbox)
  have hpos : adelicAddHaar (𝓞 ℚ) ℚ U ≠ 0 :=
    (hμ.toIsOpenPosMeasure).open_pos U hUopen hUne
  have hU : adelicAddHaar (𝓞 ℚ) ℚ U = (c : ℝ≥0∞) * adelicAddHaar (𝓞 ℚ) ℚ U := by
    conv_lhs => rw [hc]
    rw [Measure.smul_apply]
    rfl
  have hc1 : (c : ℝ≥0∞) = 1 := by
    rw [mul_comm (c : ℝ≥0∞)] at hU
    refine (ENNReal.mul_right_inj hpos hfin).mp ?_
    rw [mul_one]
    exact hU.symm
  exact ⟨c, by exact_mod_cast hc1, hc⟩

end NumberTheorySetAF75DConsumer

end
