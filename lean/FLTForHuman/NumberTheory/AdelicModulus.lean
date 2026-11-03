/-
  The adelic-modulus façade: the `distribHaarChar` product formula, place by place.

  This is the tier-1 wire for the family of
  `topics/numberTheory/adelicModulus/TOPIC-adelic-modulus.md`. It declares only the
  consumed headlines, each stated from its pin `Theorems/` wrapper and proved by the
  corresponding engine module:

  * `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` —
    the modulus of an idele as the product of the local norms
    (`NumberTheory/AdelicHaar/AdelicModulus.lean`);
  * `NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult` — its
    archimedean half (`NumberTheory/AdelicHaar/ArchModulus.lean`);
  * `NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`,
    `NumberField.AdeleRing.measurePreserving_mul_algebraMap`,
    `NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar` and
    `NumberField.AdeleRing.distribHaarChar_algebraMap` — the principal-idele product
    formula (`NumberTheory/AdelicHaar/ProductFormula.lean`).

  **State.** All six headlines are landed. The four principal-idele ones read
  `NumberTheory/AdelicHaar/ProductFormula.lean`; the modulus headline reads
  `NumberTheory/AdelicHaar/AdelicModulus.lean` and the archimedean one
  `NumberTheory/AdelicHaar/ArchModulus.lean`.

  The principal-idele engine `ProductFormula` is wired by its own header (its four pin `S_`
  files are its `spec-pin:` line), so its declarations are statement-checked; the two
  definition engines (`AdelicModulus`, `ArchModulus`) stay tier 3 and are recorded in
  `spec/UNWIRED-PUBLIC.md`.

  **Wiring.** `spec/check_port.py` owns this façade: the six `spec-pin:` lines below name the
  six pin `Theorems/` wrappers the headlines are stated from.
  spec-pin: Theorems/Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean
  spec-pin: Theorems/Thm_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean
  spec-pin: Theorems/Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean
  spec-pin: Theorems/Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean
  spec-pin: Theorems/Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean
  spec-pin: Theorems/Thm_NumberField_AdeleRing_distribHaarChar_algebraMap.lean

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrappers are the
  `Theorems/Thm_NumberField_{AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm,
  InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult,
  AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox,
  AdeleRing_measurePreserving_mul_algebraMap,
  AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar,
  AdeleRing_distribHaarChar_algebraMap}.lean` files of the same pin.
-/
import FLTForHuman.NumberTheory.AdelicHaar.AdelicModulus
import FLTForHuman.NumberTheory.AdelicHaar.ArchModulus
import FLTForHuman.NumberTheory.AdelicHaar.ProductFormula

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure

noncomputable section

namespace NumberField

namespace AdelicBox

theorem isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0) :
    MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ :=
  AdelicHaar.isAddFundamentalDomain_preimage_mul F μ a ha

end AdelicBox

namespace AdeleRing

theorem measurePreserving_mul_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ :=
  AdelicHaar.measurePreserving_mul F μ a ha
    (AdelicHaar.isAddFundamentalDomain_preimage_mul F μ a ha)

-- Spelled with the wrapper's long names (`NumberField.RingOfIntegers F` for `𝓞 F`): the
-- statement checker diffs the wrapper's text, and this wrapper does not use the shorthand.
theorem distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = (∏ w : NumberField.InfinitePlace F,
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult)
        * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 v‖ :=
  ZhatModulus.distribHaarChar_eq_placeModulus (ZhatModulus.hasTransversal F) a

theorem distribHaarChar_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 :=
  AdelicHaar.distribHaarChar_algebraMap_impl F a

end AdeleRing

namespace AdelicHaar

section

-- The pin's `S_` file for this headline carries the same local instance: the statement's
-- `adelicAddHaar` pins the `adeleBorel` measurable space, so the ambient instance must be it.
attribute [local instance] NumberField.AdelicHaar.adeleBorel

-- The three local instances are the pin's: `adelicAddHaar`'s `Regular` companion, its
-- `IsAddHaarMeasure`, and the `BorelSpace` of its measurable space. They are bound with `have`
-- rather than `haveI`: in Lean 4 `have` registers a local instance itself, so the inlining
-- behaviour of `haveI` is the only difference and proofs are irrelevant.
theorem measurePreserving_mul_algebraMap_adelicAddHaar
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicHaar.adelicAddHaar (𝓞 F) F) := by
  have h1 := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  have h2 := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have h3 := AdelicHaar.regular_adelicAddHaar F
  exact NumberField.AdeleRing.measurePreserving_mul_algebraMap F _ a ha

end

end AdelicHaar

namespace InfiniteAdeleRing

-- `distribHaarChar` stays unqualified, as in the wrapper (the checker diffs its text).
theorem distribHaarChar_eq_prod_norm_pow_mult
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (a : (InfiniteAdeleRing K)ˣ) :
    (distribHaarChar (InfiniteAdeleRing K) a : ℝ)
      = ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult :=
  ArchModS44.distribHaarChar_infiniteAdeleRing a

end InfiniteAdeleRing

end NumberField
