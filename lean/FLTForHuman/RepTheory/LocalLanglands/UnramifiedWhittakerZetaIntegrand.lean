/-
  The zeta integrand and the product-measure data of the idèle group.

  `zetaIntegrand W χ s a = W (diagOne a) · χ a · ‖a‖ ^ (s - 1)` is the integrand of the local zeta
  integral, read on the idèles.

  `ProductMeasureData S ν` is the bundle that a product-measure decomposition of the idèle measure `ν`
  at a finite set `S` consists of: a constant `c > 0`, a measure `νS` on the `S`-part, the projection
  `projS` off the `S`-places, the order function `ord`, the off-`S`-triviality of `projS`, the
  decomposition of an idèle as `projS a · ∏ v ∈ L, ϖ_v ^ ord v a · u` with `u` a unit idèle, the
  Tonelli/Fubini identity for functions of `a ↦ (projS a, ord v a)`, and the measurability of the unit
  idèles outside a finite set. It is the interface the Tate/Whittaker zeta-integral layer consumes.

  Transcribed whole from `Definitions/Def_UnramifiedWhittaker_ZetaIntegrand.lean` (pinned `aa2d8b3`, 53
  lines / 2 declarations). The pin's `import Mathlib` and its four `Def_` imports are replaced by the port
  modules below.

  spec-pin: Definitions/Def_UnramifiedWhittaker_ZetaIntegrand.lean
-/
import FLTForHuman.NumberTheory.NumberField.UnitIdelesOutside
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.NumberField.FiniteIdeles
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing
open NumberField.TateGlobal AutomorphicForm

namespace UnramifiedWhittaker

def zetaIntegrand {F : Type} [Field F] [NumberField F] (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  W (diagOne a) * ((χ a : ℂˣ) : ℂ) * ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)

structure ProductMeasureData {F : Type} [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) where

  c : ℝ
  c_pos : 0 < c

  νS : Measure (AdeleRing (𝓞 F) F)ˣ

  projS : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 F) F)ˣ

  ord : HeightOneSpectrum (𝓞 F) → (AdeleRing (𝓞 F) F)ˣ → ℤ
  projS_off : ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
    ((projS a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1
  decomp : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}),
      ∃ u : (AdeleRing (𝓞 F) F)ˣ, (u : AdeleRing (𝓞 F) F).1 = 1 ∧
        (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) ∧
        finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F ∧
        a = projS a * (L.map fun v => uniformizerIdele F v ^ ord v a).prod * u
  tonelli : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℂ),
      Integrable f νS → (∀ v ∈ L, Summable fun m : ℤ => ‖φ v m‖) →
        IntegrableOn (fun a => f (projS a) * (L.map fun v => φ v (ord v a)).prod)
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ) ν ∧
        (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ),
            f (projS a) * (L.map fun v => φ v (ord v a)).prod ∂ν) =
          c * (∫ a, f a ∂νS) * (L.map fun v => ∑' m : ℤ, φ v m).prod

  measurableSet : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    MeasurableSet (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ)

end UnramifiedWhittaker
