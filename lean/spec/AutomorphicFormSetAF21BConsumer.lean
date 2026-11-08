/-
  SET-AF21B consumer: the centre box sheet of `ℚ`, read at a concrete field.

  `Adelic/RationalUnipotentBoxSheet.lean` proves, for an arbitrary number field `K`, that the box
  read inside `rationalCentreUnipotent K` is a fundamental domain for the centre-unipotent
  subgroup, that it is measurable, and how integration over it reads against the normalised
  additive Haar measure of the box.

  **This zone.** One chain, at `K = ℚ`, where every instance is concrete. The five conjuncts of
  `isFundamentalDomain_boxSheet_rationalCentreUnipotent ℚ` are destructured, and the three
  measure-theoretic ones are put to work:

  * the `IsFundamentalDomain` supplies `ae_covers` — almost every point of
    `rationalCentreUnipotent ℚ` is moved into the sheet by a subgroup element — and
    `iUnion_smul_ae_eq` — the translates of the sheet cover almost everything; each translate is
    again null-measurable (`nullMeasurableSet_smul`), which needs the left-invariance of
    `rationalCentreUnipotentHaar ℚ` (AF20's headline) to turn into an `SMulInvariantMeasure`;
  * the integral formula, evaluated at the constant function `1`, computes the measure of the
    sheet: `(rationalCentreUnipotentHaar ℚ) T = 1`, so the measurable set `T` carries a finite
    (indeed unit) measure — the normalisation `(adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ))⁻¹` cancels the
    mass of the box.

  `IsFundamentalDomain.measure_eq` is *not* usable here: it carries a `[Countable G]` hypothesis,
  and the acting group is `rationalCentreUnipotent ℚ`, which contains a copy of the profinite
  adèles and is uncountable. The covering and null-measurability lemmas above replace it.
-/
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentBoxSheet

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open scoped ENNReal Pointwise

namespace AutomorphicForm

namespace SetAF21B

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-- **The zone.** For `K = ℚ`: the box sheet `T` is measurable, it is a fundamental domain for the
centre-unipotent subgroup `P`, it has measure exactly `1` (so finite), almost every point of the
ambient group reaches `T` by a subgroup element, its translates cover almost everything, and each
translate is null-measurable. -/
theorem consumer_zone_centreBoxSheet_rat :
    let P : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) :=
      rationalCentre ℚ ⊔ ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range
    let T : Set (rationalCentreUnipotent ℚ) :=
      (fun u : AdeleRing (𝓞 ℚ) ℚ =>
        Subgroup.inclusion le_sup_right (toAdelicUnipotent ℚ u)) '' adelicBox ℚ
    MeasurableSet T ∧
      IsFundamentalDomain (P.subgroupOf (rationalCentreUnipotent ℚ)) T
        (rationalCentreUnipotentHaar ℚ) ∧
      (rationalCentreUnipotentHaar ℚ) T = 1 ∧
      (rationalCentreUnipotentHaar ℚ) T ≠ ⊤ ∧
      (∀ᵐ x ∂(rationalCentreUnipotentHaar ℚ),
        ∃ g : P.subgroupOf (rationalCentreUnipotent ℚ), g • x ∈ T) ∧
      (⋃ g : P.subgroupOf (rationalCentreUnipotent ℚ), g • T
        =ᵐ[(rationalCentreUnipotentHaar ℚ)] (Set.univ : Set (rationalCentreUnipotent ℚ))) ∧
      (∀ g : P.subgroupOf (rationalCentreUnipotent ℚ), NullMeasurableSet (g • T)
        (rationalCentreUnipotentHaar ℚ)) := by
  intro P T
  -- the measure is left-invariant (`IsHaarMeasure`, AF20), so subgroup translates preserve it
  have hLeft : (rationalCentreUnipotentHaar ℚ).IsMulLeftInvariant :=
    (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant ℚ).1.toIsMulLeftInvariant
  obtain ⟨-, -, hT, hFD, hint⟩ :=
    isFundamentalDomain_boxSheet_rationalCentreUnipotent ℚ
  -- the normalisation of the box measure is invertible and finite
  have hpos : adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ) ≠ 0 :=
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
  have hlt : adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ) ≠ ⊤ :=
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne
  -- the integral formula at the constant function `1` computes the measure of the sheet
  have hmeas : (rationalCentreUnipotentHaar ℚ) T = 1 := by
    have h := hint (1 : rationalCentreUnipotent ℚ → ℝ≥0∞) measurable_const
    simp only [Pi.one_apply, setLIntegral_one] at h
    rw [h, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hlt]
  exact ⟨hT, hFD, hmeas, hmeas ▸ ENNReal.one_ne_top, hFD.ae_covers, hFD.iUnion_smul_ae_eq,
    fun g => hFD.nullMeasurableSet_smul g⟩

end SetAF21B
end AutomorphicForm
