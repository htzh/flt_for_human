/-
  The production pins.

  The `productionPinsOf` bundle at the standard windowed-Siegel parameters: centre-cut Siegel set, `levelOne` level, `heckeGen` generators, `adelicBox`; its Borel/Haar/measure components are exposed by the `productionPins_*` projection lemmas, and the Haar, probability, measurability and finite-positive-measure properties are carried over from `productionPinsOf` and the Siegel-volume estimates.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_ProductionPins.lean` (pinned
  `aa2d8b3`, 79 lines / 15 declarations). The pin's stub imports are replaced by the
  port modules below; the pin namespaces are kept. mathlib `v4.34.0` has no counterpart.
  The only addition is `import …AdelicLevel.HeckeGen` (the pin reaches `heckeGen`
  transitively through its AdelicBox import, which the port's `AdelicBox` does not carry),
  and the two `letI`/`haveI` walls in `measurableSet_productionPins_D` are spelled
  `let`/`have` (they still feed instance search and avoid the `haveI`/`letI` linter).
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.SiegelVolume
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def productionPins : CarrierPins F :=
  productionPinsOf F
    (centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2)
    (fun N => levelOne (𝓞 F) F N)
    (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

@[simp] theorem productionPins_mS :
    (productionPins F).mS = glBorel (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPins_μ :
    (productionPins F).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPins_D :
    (productionPins F).D = centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2 := rfl

@[simp] theorem productionPins_Z :
    (productionPins F).Z = (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := rfl

@[simp] theorem productionPins_U (N : Ideal (𝓞 F)) :
    (productionPins F).U N = levelOne (𝓞 F) F N := rfl

@[simp] theorem productionPins_gen (v : HeightOneSpectrum (𝓞 F)) :
    (productionPins F).gen v = heckeGen (𝓞 F) F v := rfl

@[simp] theorem productionPins_nS :
    (productionPins F).nS = adeleBorel (𝓞 F) F := rfl

@[simp] theorem productionPins_ν :
    (productionPins F).ν =
      @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  rfl

theorem isHaarMeasure_productionPins_μ :
    @Measure.IsHaarMeasure _ _ _ (productionPins F).mS (productionPins F).μ :=
  isHaarMeasure_productionPinsOf_μ F _ _ _ _

theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPins F).nS (productionPins F).ν :=
  isProbabilityMeasure_productionPinsOf_ν F _ _ _ _
    (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne

theorem measurableSet_productionPins_D :
    @MeasurableSet _ (productionPins F).mS (productionPins F).D := by
  let _ := glBorel (Fin 2) (𝓞 F) F
  have := borelSpace_glBorel (Fin 2) (𝓞 F) F
  exact measurableSet_centreCutSiegelSet (F := F) (1/2) 1 (1/2) 2

theorem productionPins_μ_D_pos_lt_top :
    (letI := (productionPins F).mS;
      0 < (productionPins F).μ (productionPins F).D ∧
        (productionPins F).μ (productionPins F).D < ⊤) :=
  adelicGLHaar_centreCutSiegelSet_pos_lt_top (F := F)
    (by norm_num) (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num)

theorem productionPins_μ_D_pos :
    (letI := (productionPins F).mS; 0 < (productionPins F).μ (productionPins F).D) :=
  (productionPins_μ_D_pos_lt_top F).1

theorem productionPins_μ_D_lt_top :
    (letI := (productionPins F).mS; (productionPins F).μ (productionPins F).D < ⊤) :=
  (productionPins_μ_D_pos_lt_top F).2

end AutomorphicForm

end
