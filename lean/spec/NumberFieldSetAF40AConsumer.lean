/-
  Consumer zone for `FLTForHuman/NumberTheory/NumberField/IdeleProductMeasure.lean`.

  The two headline items of that module are the Tonelli decomposition
  `NumberField.Idele.integrableOn_and_integral_eq` and the bundle
  `NumberField.Idele.productMeasureData` that packages it as an
  `UnramifiedWhittaker.ProductMeasureData`. Everything below is stated at the *concrete*
  instance `S = ∅` (no finite places kept in the `S`-part) and `L = []` (no places moved
  out of the unit idèles), where the bundle's four fields become checkable facts rather
  than hypotheses:

  * `pmd` — the bundle at `S = ∅`, i.e. `productMeasureData F ∅`, with its `c`, `νS`,
    `projS`, `ord` read back by `pmd_c`/`pmd_νS`/`pmd_projS`/`pmd_ord`: the constant is
    `1`, the `S`-part measure is `sPartMeasure F ∅`, the projection is `partAt F ∅` and
    the order is `ord F`;
  * `pmd_projS_off` — the field `projS_off` at `S = ∅`: *every* finite component of
    `partAt F ∅ a` is `1`, so the `∅`-part of an idèle is purely archimedean (this is what
    makes the `S = ∅` case of the decomposition collapse);
  * `decomp_empty` — the field `decomp` at `L = []`: a unit idèle outside `∅` factors as
    `partAt F ∅ a * u` with `u` a unit idèle whose archimedean part is `1` — the empty
    product makes the decomposition trivial, which is exactly the sanity check the field
    has to pass;
  * `tonelli_empty` — the field `tonelli` at `L = []`, where the identity reads
    `∫ a in unitIdelesOutside ∅, f (projS a) ∂ν = c * ∫ a, f a ∂νS` and, with `c = 1`,
    becomes `∫ a, f (partAt F ∅ a) ∂ν = ∫ a, f a ∂(sPartMeasure F ∅)`;
  * `pmd_measurableSet` — the field `measurableSet` at `L = []`: `unitIdelesOutside ∅` is
    measurable for `idelicHaar`, via the ported openness
    `NumberField.Idele.isOpen_unitIdelesOutside`;
  * `sPartMeasure_empty_ne_zero` — `sPartMeasure F ∅ ≠ 0`, so the `νS` the bundle carries is
    not the zero measure (the Tonelli identity is not vacuous).

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF40AConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.IdeleProductMeasure

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdeleRing
open scoped Classical

namespace NumberFieldSetAF40AConsumer

variable (F : Type) [Field F] [NumberField F]

/-! ### The instances the bundle's type mentions

`productMeasureData` is stated against the module's *own* Borel structure `ideleBorel` on
the idèles (the pin's `attribute [local instance] ideleBorel borelSpace_ideleBorel`, which
is local to that module). A consumer must re-install the same two instances to name the
bundle at all, exactly as the module does. -/

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

/-- The idèles at the empty set of finite places, no places moved out. -/
abbrev unitIdelesEmpty : Set (AdeleRing (𝓞 F) F)ˣ :=
  (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F
    (∅ : Set (HeightOneSpectrum (𝓞 F))) : Set (AdeleRing (𝓞 F) F)ˣ)

/-- The product-measure bundle at `S = ∅`. -/
abbrev pmd : @UnramifiedWhittaker.ProductMeasureData F _ _ (NumberField.Idele.ideleBorel F)
    (∅ : Finset (HeightOneSpectrum (𝓞 F))) (NumberField.Idele.idelicHaar F) :=
  NumberField.Idele.productMeasureData F ∅

/-! ### Reading the bundle's parameters back

The four numeric/structural fields, at `S = ∅`: each is the module's own object, so the
`S`-part analysis below is about `sPartMeasure F ∅`/`partAt F ∅`/`ord F` and nothing else. -/

/-- The Tonelli constant is `1` at `S = ∅`. -/
theorem pmd_c : (pmd F).c = 1 := rfl

/-- The `S`-part measure is `sPartMeasure F ∅`. -/
theorem pmd_νS : (pmd F).νS = NumberField.Idele.sPartMeasure F ∅ := rfl

/-- The projection is `partAt F ∅`. -/
theorem pmd_projS : (pmd F).projS = NumberField.Idele.partAt F ∅ := rfl

/-- The order function is `ord F`. -/
theorem pmd_ord : (pmd F).ord = NumberField.Idele.ord F := rfl

/-! ### The four fields, instantiated -/

/-- The field `projS_off` at `S = ∅`: *every* finite component of `partAt F ∅ a` is `1`.
So the `∅`-part of an idèle carries only archimedean information. -/
theorem pmd_projS_off (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((NumberField.Idele.partAt F ∅ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 :=
  (pmd F).projS_off a v (by simp)

/-- The field `decomp` at `L = []`: a unit idèle outside `∅` is `partAt F ∅ a` times a unit
idèle with trivial archimedean part — the empty product makes the decomposition trivial. -/
theorem decomp_empty (a : (AdeleRing (𝓞 F) F)ˣ) (ha : a ∈ unitIdelesEmpty F) :
    ∃ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 ∧
        (∀ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F))), (u : AdeleRing (𝓞 F) F).2 v = 1) ∧
        finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F ∧
        a = NumberField.Idele.partAt F ∅ a * u := by
  obtain ⟨u, h1, h2, h3, h4⟩ := (pmd F).decomp [] (by simp) List.nodup_nil a (by simpa using ha)
  exact ⟨u, h1, h2, h3, by simpa only [pmd_projS, List.map_nil, List.prod_nil, mul_one] using h4⟩

/-- The field `tonelli` at `L = []`: the Tonelli identity of the bundle at no places moved
out of the unit idèles, with the constant `c = 1` multiplied away. -/
theorem tonelli_empty (f : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hf : Integrable f (NumberField.Idele.sPartMeasure F ∅)) :
    IntegrableOn (fun a => f (NumberField.Idele.partAt F ∅ a)) (unitIdelesEmpty F)
        (NumberField.Idele.idelicHaar F) ∧
      (∫ a in unitIdelesEmpty F, f (NumberField.Idele.partAt F ∅ a)
          ∂(NumberField.Idele.idelicHaar F)) =
        ∫ a, f a ∂(NumberField.Idele.sPartMeasure F ∅) := by
  obtain ⟨h1, h2⟩ :=
    (pmd F).tonelli [] (by simp) List.nodup_nil f (fun _ _ => 0) hf (by simp)
  have hset :
      ((NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F
        (↑(∅ : Finset (HeightOneSpectrum (𝓞 F))) ∪
          {v | v ∈ ([] : List (HeightOneSpectrum (𝓞 F)))})) : Set (AdeleRing (𝓞 F) F)ˣ) =
        unitIdelesEmpty F := by
    simp [unitIdelesEmpty]
  rw [hset] at h1 h2
  refine ⟨?_, ?_⟩
  · simpa only [pmd_projS, List.map_nil, List.prod_nil, mul_one] using h1
  · simpa only [pmd_projS, pmd_c, pmd_νS, List.map_nil, List.prod_nil, mul_one,
      Complex.ofReal_one, one_mul] using h2

/-- The field `measurableSet` at `L = []`, through the ported openness of the domain. -/
theorem pmd_measurableSet : MeasurableSet (unitIdelesEmpty F) := by
  have h := (pmd F).measurableSet [] (by simp) List.nodup_nil
  simpa [unitIdelesEmpty] using h

/-- The `νS` the bundle carries at `S = ∅` is not the zero measure. -/
theorem sPartMeasure_empty_ne_zero : NumberField.Idele.sPartMeasure F (∅ : Finset (HeightOneSpectrum (𝓞 F))) ≠ 0 :=
  NumberField.Idele.sPartMeasure_ne_zero F ∅

end NumberFieldSetAF40AConsumer
