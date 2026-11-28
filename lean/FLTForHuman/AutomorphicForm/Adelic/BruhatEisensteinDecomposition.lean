/-
The Bruhat–Eisenstein series is its constant term plus its Whittaker sum.

For `Re s > 1`, a unitary pair of Hecke characters and an induced section family `φ`, the
Bruhat–Eisenstein series

  `E g = φ s g + ∑' ξ : F, φ s (w * u(ξ) * g)`

is the sum of its **constant term** and the **Whittaker sum** over `ξ ≠ 0`:

  `E g = constantTerm (productionPins F).ν unipotentGL2 E g
        + ∑' ξ : {ξ : F // ξ ≠ 0}, w(E) ξ g`.

SET-AF112B's summability row is what makes the `∑'` well-defined, `WhittakerSum`'s HasSum identity is
what identifies each coefficient with the unfolded integral, and `continuous_bruhatTransversal_tsum_
of_re_gt_half` is the continuity that lets the sum be split at `ξ ≠ 0`. The row is the decomposition
the Euler-product rows consume (SET-AF113A/B/C read the `diagOne` coefficient of this `E`).

Assumes, from earlier modules: `BruhatEisenstein` (the series and its constant term),
`BruhatEisensteinWhittakerSummability` (the summability), `WhittakerSum` (`hasSum_whittakerCoefficient`),
`ProductionPins`, `InducedSection`, `EtaFamily`, and `ConstantTerm`.

Transcribed from the pin below (pinned `aa2d8b3`, 102 `S_` lines).

## The rows

* `AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary` — 102 pin `S_` lines.

## Port deltas

* The pin's `private def eisF_j1` (`S_…:24`, `noncomputable section`) is reproduced verbatim as
  `AutomorphicForm.eisF_j1`, `private` and inside a `noncomputable section`, so the module's public
  surface is the headline alone. It is the pin's own abbreviation for the series
  `g' ↦ φ s g' + ∑' ξ, φ s (w * u(ξ) * g')`, used only to make the `show` and the two `set`s readable.
* The pin's premises are the port's public declarations at the same binder names, applied as-is:
  `AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary`
  (`BruhatEisensteinWhittakerSummability.lean`, SET-AF112B),
  `AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half` (`WeylIntegrable.lean`),
  `AutomorphicForm.hasSum_whittakerCoefficient` (`WhittakerSum.lean`) and
  `AutomorphicForm.whittakerCoefficient_zero_eq_constantTerm` (`WhittakerCoefficient.lean`).
* `AutomorphicForm.continuous_unipotentGL2` (`ConstantTerm.lean`, the `[ContinuousNeg R]` form) is the
  port's copy of the pin's continuity of `x ↦ u(x)`; the pin's `IsTopologicalRing` variant lives at
  `AutomorphicForm.LocalIntertwining.UnipDeriv.continuous_unipotentGL2` and is not needed here.
* `hasSum_whittakerCoefficient` is stated for `productionPinsOf F D U gen (adelicBox F)`; the `rfl`
  projections `productionPins_{D,U,gen}` (`ProductionPins.lean`) identify it with `productionPins F`,
  which is exactly how the pin passes `(productionPins F).D`, `.U`, `.gen`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary.lean>

spec-pin: Theorems/Thm_AutomorphicForm_bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary.lean
spec-pin: P2M/Sol/S_AutomorphicForm_bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisenstein
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisensteinWhittakerSummability
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSum
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicModulus

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox
open MeasureTheory AutomorphicForm
open scoped Classical NNReal

namespace AutomorphicForm

noncomputable section

/-- The pin's abbreviation for the Bruhat–Eisenstein series at `s`: `φ s` plus the sum of its
`w · u(ξ)`-translates. Kept `private`, as in the pin. -/
private def eisF_j1 (F : Type) [Field F] [NumberField F] (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (s : ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
  φ s g' + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')

theorem bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφc : ∀ s, Continuous (φ s))
      (g : AdelicGL2 (𝓞 F) F) (s : ℂ) (_hs : 1 < s.re),
    letI := (productionPins F).nS
    φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
      = constantTerm (productionPins F).ν unipotentGL2
          (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) g
        + ∑' ξ : {ξ : F // ξ ≠ 0},
            whittakerCoefficient F (productionPins F) ψ
              (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                  * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by
  intro α hα μ ν _hμ _hν ψ _hψ φ _hφ _hφK _hφf _hφc g s _hs
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := (productionPins F).nS

  show eisF_j1 F φ s g = constantTerm (productionPins F).ν unipotentGL2 (eisF_j1 F φ s) g
    + ∑' ξ : {ξ : F // ξ ≠ 0},
        whittakerCoefficient F (productionPins F) ψ (eisF_j1 F φ s) (ξ : F) g
  set W : F → ℂ := fun α' =>
    whittakerCoefficient F (productionPins F) ψ (eisF_j1 F φ s) α' g with hW

  have hsum : Summable W :=
    summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary F hα μ ν
      _hμ _hν ψ _hψ s _hs (φ s) (_hφ s) (_hφK s) (_hφf s) (_hφc s) g

  have hhalf : (1 : ℝ) / 2 < s.re := lt_trans (by norm_num) _hs
  have hEc : Continuous (eisF_j1 F φ s) :=
    (_hφc s).add (continuous_bruhatTransversal_tsum_of_re_gt_half F hα μ ν
      _hμ _hν s hhalf (φ s) (_hφ s) (_hφc s))
  have hcont : Continuous (fun x => eisF_j1 F φ s (unipotentGL2 x * g)) :=
    hEc.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)

  have hHS : HasSum W (eisF_j1 F φ s g) :=
    hasSum_whittakerCoefficient F
      (productionPins F).D (productionPins F).U (productionPins F).gen ψ _hψ (eisF_j1 F φ s) g
      hcont hsum

  have hsplit :
      (∑' x : ({0} : Set F), W (x : F)) + ∑' x : (({0} : Set F)ᶜ : Set F), W (x : F)
        = ∑' α', W α' :=
    (hsum.subtype _).tsum_add_tsum_compl (hsum.subtype _)
  have hzero : (∑' x : ({0} : Set F), W (x : F)) = W 0 := tsum_singleton 0 W
  have hW0 : W 0 = constantTerm (productionPins F).ν unipotentGL2 (eisF_j1 F φ s) g := by
    simp only [hW]
    exact whittakerCoefficient_zero_eq_constantTerm F (productionPins F) ψ (eisF_j1 F φ s) g
  have hcompl :
      (∑' x : (({0} : Set F)ᶜ : Set F), W (x : F))
        = ∑' ξ : {ξ : F // ξ ≠ 0}, W (ξ : F) := by
    refine tsum_congr_set_coe W ?_
    ext x; exact ⟨fun h => h, fun h => h⟩
  calc eisF_j1 F φ s g = ∑' α', W α' := hHS.tsum_eq.symm
    _ = (∑' x : ({0} : Set F), W (x : F)) + ∑' x : (({0} : Set F)ᶜ : Set F), W (x : F) :=
        hsplit.symm
    _ = constantTerm (productionPins F).ν unipotentGL2 (eisF_j1 F φ s) g
          + ∑' ξ : {ξ : F // ξ ≠ 0}, W (ξ : F) := by rw [hzero, hW0, hcompl]

end

end AutomorphicForm
