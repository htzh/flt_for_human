/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/WeylIntegrable/FiniteSlice.lean`.

  The row under test is exercised in composition, never by `#check`:

  * `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` is instantiated at the
    concrete character `alphaOf = NNReal.toRealHom ∘ distribHaarChar` — the `let α` of its own
    statement, whose positivity `alphaOf_pos` is `distribHaarChar_pos` — and at the *right-translated*
    point `k * g`, then closed under scalar multiplication: the Euler-product layer evaluates the
    scaled slice, not the bare one. The conclusion is then cashed out as the finiteness of the
    `lintegral` of the slice's norm, which is the form the analytic layer consumes;
  * `measure_addSubgroup_eq_relIndex_mul` and `distribHaarChar_yUnit_zero` compose into the measure
    identity `σ (dilate yUnit) = distribHaarChar (yUnit) * σ (integralFiniteAdeles)`: the Haar
    character of the finite part of `yUnit (selRel F 0 t)` is exactly the measure ratio of the dilated
    lattice. Both side conditions are the pinned ones — `one_le_valued_selY_snd`
    (`WeylIntegrable/Assembly.lean`) fed through `intLattice_le_dilate` and `relIndex_dilate_ne_zero`
    (`WeylIntegrable/LatticeEstimates.lean`), and the port's `isClosed_intLattice` — so deleting any of
    those three modules breaks the zone;
  * `ofReal_rpow_le_domGf` and `lintegral_domGf_lt_top` compose into the integrability of the single
    weight `distribHaarChar ^ (-(2 Re s + 1))` for `Re s > 1/2`: the pin's `domGf` majorant is a
    majorant in the measure, not a formal one;
  * `continuous_unipotentGL2_slice` is composed with the continuity of `φ` to recover the
    measurability half of the headline independently of the majorant.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF33AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.FiniteSlice

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicHaar
  NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WeylIntegrable
open scoped NNReal ENNReal Pointwise

namespace AutomorphicFormSetAF33AConsumer

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

/-- The `let α` of the headline, named so that the zone can instantiate it concretely. -/
def alphaOf : (𝔸)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar 𝔸)).toHomUnits

/-- The positivity the headline asks of `alphaOf`, discharged from `distribHaarChar_pos`. -/
theorem alphaOf_pos : ∀ x, 0 < ((alphaOf F x : ℝˣ) : ℝ) := fun x => by
  show 0 < ((distribHaarChar 𝔸 x : ℝ≥0) : ℝ)
  exact NNReal.coe_pos.mpr (distribHaarChar_pos (A := 𝔸) (g := x))

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]

/-- The headline at a right-translated point and a scalar: the Euler-product layer evaluates the
scaled slice `c · φ (w · n(0,t) · (k * g))`, and this is its integrability. -/
theorem integrable_finSlice_const_mul (σ : Measure 𝔸f) [σ.IsAddHaarMeasure]
    (μ ν : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (s : ℂ) (hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ (alphaOf F) (alphaOf_pos F) s)
      (etaSnd ν (alphaOf F) (alphaOf_pos F) s) φ)
    (hφc : Continuous φ) (c : ℂ) (k g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun t : 𝔸f =>
      c * φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := 𝔸) (0, t) * (k * g))) σ :=
  (weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half F σ (alphaOf_pos F) μ ν hμ hν
    s hs φ hφ hφc (k * g)).const_mul c

/-- The same slice read as a finite `lintegral` of its norm. -/
theorem lintegral_finSlice_lt_top (σ : Measure 𝔸f) [σ.IsAddHaarMeasure]
    (μ ν : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (s : ℂ) (hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ (alphaOf F) (alphaOf_pos F) s)
      (etaSnd ν (alphaOf F) (alphaOf_pos F) s) φ)
    (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    (∫⁻ t : 𝔸f, ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := 𝔸) (0, t) * g)‖ₑ ∂σ) < ∞ :=
  (weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half F σ (alphaOf_pos F) μ ν hμ
    hν s hs φ hφ hφc g).2

/-- The Haar character of the finite part of `yUnit (selRel F 0 t)` is the measure ratio of the
dilated lattice: `measure_addSubgroup_eq_relIndex_mul` at `A = intLattice`, `B = dilate (yUnit …)`,
composed with `distribHaarChar_yUnit_zero`. -/
theorem measure_dilate_eq_distribHaarChar_mul (σ : Measure 𝔸f) [σ.IsAddHaarMeasure] (t : 𝔸f) :
    σ (dilate F (finPart F (yUnit (selRel F 0 t)))) =
      (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0∞) *
        σ (integralFiniteAdeles (𝓞 F) F) := by
  have hv : ∀ v, 1 ≤ Valued.v (((finPart F (yUnit (selRel F 0 t)) : (𝔸f)ˣ) : 𝔸f) v) :=
    fun v => one_le_valued_selY_snd F 0 t v
  have h := measure_addSubgroup_eq_relIndex_mul F σ (intLattice F)
    (dilate F (finPart F (yUnit (selRel F 0 t)))) (intLattice_le_dilate F hv)
    (isClosed_intLattice F) (relIndex_dilate_ne_zero F _)
  rw [coe_intLattice, ← distribHaarChar_yUnit_zero] at h
  exact h

/-- The single weight `distribHaarChar ^ (-(2 Re s + 1))` is integrable against any Haar measure on
the finite adèles once `Re s > 1/2`: `domGf` is a majorant in the measure. -/
theorem lintegral_haarWeight_lt_top (σ : Measure 𝔸f) [σ.IsAddHaarMeasure] (s : ℂ)
    (hs : 1 / 2 < s.re) :
    (∫⁻ t : 𝔸f, ENNReal.ofReal
      ((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ) ^ (-(2 * s.re + 1))) ∂σ) < ∞ := by
  have ha2 : 2 < 2 * s.re + 1 := by linarith
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) (lintegral_domGf_lt_top F σ ha2)
  exact ofReal_rpow_le_domGf F (2 * s.re + 1) t

/-- The measurability half of the headline, recovered from `continuous_unipotentGL2_slice`. -/
theorem aestronglyMeasurable_finSlice (σ : Measure 𝔸f) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    AEStronglyMeasurable (fun t : 𝔸f =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := 𝔸) (0, t) * g)) σ :=
  (hφc.comp ((continuous_const.mul (continuous_unipotentGL2_slice F)).mul
    continuous_const)).aestronglyMeasurable

end AutomorphicFormSetAF33AConsumer
