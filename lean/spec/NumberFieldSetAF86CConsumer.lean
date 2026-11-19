/-
  SET-AF86C consumer: the balanced idèle decomposition at `ℚ`, and the Haar measure's right invariance.

  **The rows.** `FLTForHuman/NumberTheory/NumberField/TateGlobal/BalancedCompact.lean` carries
  `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` (one compact norm-one set
  such that every idèle is a principal idèle times a balanced archimedean dilation times a member of it);
  `FLTForHuman/NumberTheory/AdelicHaar/ProductMeasure.lean` carries
  `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing`.

  **The readings.**

  * Zone 1 — **the decomposition at `ℚ`**: the row instantiated at the smallest number field, in the shape
    the norm-one/compactness arguments use;
  * Zone 2 — **the right invariance, extracted**: the row read through mathlib's
    `MeasureTheory.map_mul_right_eq_self`, i.e. as invariance of the measure under a right translation.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF86CConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.BalancedCompact
import FLTForHuman.NumberTheory.AdelicHaar.ProductMeasure

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal Classical

namespace NumberFieldSetAF86CConsumer

/-! ### Zone 1 — the balanced decomposition at `ℚ` -/

/-- **Zone 1.** Every idèle of `ℚ` is a principal idèle times a balanced archimedean dilation times an
element of one compact norm-one set. -/
theorem exists_isCompact_balanced_decomposition_rat :
    let α : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ))).toHomUnits
    ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ, IsCompact U ∧ (∀ u ∈ U, ((α u : ℝˣ) : ℝ) = 1) ∧
      ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∃ (η : ℚˣ) (z u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (r : ℝ),
        u ∈ U ∧ 0 < r ∧
        y = Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) η * z * u ∧
        (z : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
        (∀ w : InfinitePlace ℚ, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 ℚ) ℚ).1 w) = (r : ℂ)) ∧
        ((α z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ ℚ :=
  NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul ℚ

/-! ### Zone 2 — the right invariance of a Haar measure on the infinite-adele `GL₂` -/

/-- **Zone 2.** A Haar measure on `GL₂` of the infinite adèles is invariant under every right
translation — the row read through mathlib's `map_mul_right_eq_self`. -/
theorem map_mul_right_eq_self_infiniteAdeleRing (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (k : GL (Fin 2) (InfiniteAdeleRing K)) :
    Measure.map (· * k) μa = μa := by
  have : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing K μa
  exact MeasureTheory.map_mul_right_eq_self μa k

end NumberFieldSetAF86CConsumer
