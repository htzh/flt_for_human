/-
  SET-AF90D consumer: the box indicator, its measure, and its arithmetic support.

  **The rows.** `FLTForHuman/NumberTheory/AdelicBox/Measure.lean` carries
  `isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` (the indicator of
  a translate/dilate of the integral finite adèles is locally constant and compactly supported) and
  `absNorm_mul_measure_image_integralFiniteAdeles` (its Haar measure is `1 / absNorm d` times the
  measure of the integral finite adèles), together with the membership criterion
  `algebraMap_mem_image_integralFiniteAdeles_iff`.

  **The readings.** Zone 1 is the two rows composed into the interface a Haar integral uses: the
  indicator is a legitimate test function (locally constant, compactly supported) and its measure
  is the scaled one. Zone 2 reads the indicator at a principal adèle through the arithmetic
  membership criterion — the value is `1` exactly on the arithmetic progression `k + d·𝓞_F`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF90DConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.AdelicBox.Measure

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped ENNReal BigOperators

namespace NumberFieldSetAF90DConsumer

/-- **Zone 1.** The translated/dilated integral finite adèles have a locally constant, compactly
supported indicator and scaled Haar measure. -/
theorem locallyConstant_hasCompactSupport_and_measure_image
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (IsLocallyConstant (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      ∧ HasCompactSupport (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))) ∧
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F) :=
  ⟨isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd k,
   absNorm_mul_measure_image_integralFiniteAdeles F ν d hd k⟩

open Classical in
/-- **Zone 2.** The indicator read at a principal adèle: it is `1` exactly when the principal
coordinate lies in the arithmetic progression `k + d·𝓞_F`. -/
theorem indicator_image_integralFiniteAdeles_apply
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)
      = if ∃ a : 𝓞 F, ξ = k + (d : F) * (a : F) then 1 else 0 := by
  by_cases h : ∃ a : 𝓞 F, ξ = k + (d : F) * (a : F)
  · rw [ite_eq_left h]
    have hm : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈
        (fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F :=
      (algebraMap_mem_image_integralFiniteAdeles_iff F d hd k ξ).mpr h
    rw [Set.indicator_of_mem hm]
    rfl
  · rw [ite_eq_right h]
    have hm : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∉
        (fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F :=
      fun hh => h ((algebraMap_mem_image_integralFiniteAdeles_iff F d hd k ξ).mp hh)
    rw [Set.indicator_of_notMem hm]

end NumberFieldSetAF90DConsumer
