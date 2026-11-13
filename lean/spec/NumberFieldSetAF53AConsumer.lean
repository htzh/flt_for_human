/-
  Consumer for `SET-AF53` §1–§2: the adelic Haar measure of `GL2(A)` as a product of the
  local measures, and the vanishing of the additive Haar measure on the two coordinate
  hyperplanes of `𝔸_K`.

  Each headline is *applied* below — the composition is a real term, not a `#check` — with
  the chart/measure data taken as hypotheses (they cannot be instantiated concretely here:
  a Haar measure is an arbitrary datum, and an infinite place of a general number field
  is a hypothesis).
-/
import FLTForHuman.NumberTheory.AdelicHaar.ProductMeasure

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicHaar NumberField.AdelicLevel
open scoped NNReal Pointwise

namespace NumberFieldSetAF53AConsumer

/-- The product formula headline, applied at `GL₂` over `ℚ`: a `GL₂(𝔸_ℚ)`-Haar measure,
pushed to the product of the archimedean and finite `GL₂`-factors, is a positive multiple
of the product of the two local Haar measures. -/
example
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    [BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing ℚ))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
       Measure.map
           (fun x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) =>
             (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) x,
               Matrix.GeneralLinearGroup.map (adeleFin (𝓞 ℚ) ℚ) x))
           (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = c • μa.prod μf) :=
  NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod (Fin 2) ℚ μa μf

/-- The first coordinate hyperplane is null: the `{x | x.fst w = c}` slice of `𝔸_F` has
additive Haar measure zero, applied here after peeling off the ambient set `univ`. -/
example (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (c : w.Completion) :
    adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.1 w = c} ∩ Set.univ) = 0 := by
  rw [Set.inter_univ]
  exact NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero F w c

/-- The second coordinate hyperplane is null, at an arbitrary finite place `v`. -/
example (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ Set.univ) = 0 := by
  rw [Set.inter_univ]
  exact NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero F v

end NumberFieldSetAF53AConsumer
