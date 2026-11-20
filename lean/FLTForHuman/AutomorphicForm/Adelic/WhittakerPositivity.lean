/-
Positivity and integral identities for the Whittaker coefficient.

Two consequences of the Whittaker expansion: the coefficient is not identically zero at `1` for a
nonzero cusp form (the Bessel positivity input), and the integral of `φ` against a conjugate is the
`tsum` of the corresponding coefficient products (the unfolding identity).

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj.lean

Both rows are the pins' `solution`s, at the rows' names. The first pin's engine is transcribed in
`namespace WhittakerGenericity` (the pin's own namespace; 15 `private` declarations) and the second
pin's two wire declarations missing from the import closure in `namespace WhittakerUnfolding` (the
pin's search-stage label `RS9P` renamed). The rest of the second pin's engine
(`setIntegral_adelicBox_comp_add_right`, `integral_cond_adelicBox_comp_add_right`,
`whittakerCoefficient_unipotentGL2_mul`) is AF91's, in
`AutomorphicForm/Adelic/WhittakerCoefficient.lean`, and is imported rather than re-declared; the
first pin's engine is re-declared here because AF91's copies of the same block are `private`.

## Port deltas

No `import` line was added: the scaffold's six imports carry the whole closure both rows need
(`hasSum_whittakerCoefficient` and `whittakerCoefficient_unipotentGL2_mul` from `WhittakerSum`/
`WhittakerCoefficient`, the box lemmas from `AdelicBox`, `norm_apply_eq_one_of_isGlobalAddChar` from
`GlobalAddChar/Circle`, `distribHaarChar_algebraMap` from `AdelicModulus`, `diagOne`/`unipotentGL2`
from `ConstantTerm*`, all inside the six).

Proof-side only, no statement touched:

* five `attribute [local instance]` lines (the pin's own two plus `isAddHaarMeasure_adelicAddHaar`,
  `regular_adelicAddHaar`, `countable_principalSubgroup`, which the pin's proofs supply as `haveI`s
  and AF91's `WhittakerCoefficient` registers the same way);
* the pin's `haveI`s are written `have` (`linter.style.haveILetI`), and its `push_neg` is the v4.34
  name `push Not`.

## Heartbeat probe

Never installed (no `set_option maxHeartbeats` in this module). Measured with

    lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/…/WhittakerPositivity.lean

silent at `N = 10 000`, fails at `N = 5 000` with `(deterministic) timeout at whnf` at `:110` (the
`unipotentGL2_mul_globalPoints_diagGL2` `simp`); the module's own cap is the playbook's 200 000, so
≈20× the natural cost.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSum
import FLTForHuman.AutomorphicForm.Adelic.BesselInequality
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.NumberTheory.NumberField.IntegralAdeles

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace AutomorphicForm

/- The pin's own local instances (`S_…one_ne_zero.lean:24–25`), plus the three its proofs supply as
`haveI`s and this module registers as local instances the way AF91's `WhittakerCoefficient` does
(the box's fundamental-domain lemmas need them). -/
attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdelicHaar.regular_adelicAddHaar
  NumberField.AdelicHaar.countable_principalSubgroup

/-! ## I: positivity at `1`

The engine of `exists_whittakerCoefficient_one_ne_zero`: the coefficient is not identically zero
(`exists_coefficient_ne_zero`, from AF91's `hasSum_whittakerCoefficient`), the diagonal
`diagGL2 α` moves `α` to `1` (`whittakerCoefficient_eq_one_diagGL2_mul`), and the invariance of
`φ` under `GL₂(F)` makes the two integrals equal by the fundamental-domain identity of the box. -/

namespace WhittakerGenericity

variable (F : Type) [Field F] [NumberField F]

private theorem exists_coefficient_ne_zero
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g))
    (hg : φ g ≠ 0) :
    ∃ α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g ≠ 0  := by
  by_contra h
  push Not at h
  have hD := hasSum_whittakerCoefficient F D U gen ψ hψ φ g hcont hsum
  have h0 : HasSum (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) 0 := by
    simp only [h]
    exact hasSum_zero
  exact hg (hD.unique h0)

private theorem globalPoints_coe_apply (γ : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2) :
    (globalPoints (𝓞 F) F γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = algebraMap F (AdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j)  := rfl

private def diagGL2 (α : F) (hα : α ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hα])

private theorem unipotentGL2_mul_globalPoints_diagGL2 (α : F) (hα : α ≠ 0) (x : AdeleRing (𝓞 F) F) :
    unipotentGL2 x * globalPoints (𝓞 F) F (diagGL2 F α hα)
      = globalPoints (𝓞 F) F (diagGL2 F α hα)
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x)  := by
  have hinv : algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPoints_coe_apply, diagGL2, Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc, hinv]

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)  := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints_coe_apply]

private theorem integrand_vadd (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (g : AdelicGL2 (𝓞 F) F) (γ : AdeleRing.principalSubgroup (𝓞 F) F)
    (x : AdeleRing (𝓞 F) F) :
    φ (unipotentGL2 (γ +ᵥ x) * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * (γ +ᵥ x)))
      = φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))  := by
  obtain ⟨_, β, rfl⟩ := γ
  have hv : ((⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F) +ᵥ x)
      = algebraMap F (AdeleRing (𝓞 F) F) β + x := rfl
  rw [hv]
  congr 1
  · rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hleft]
  · rw [mul_add, neg_add, ψ.map_add_eq_mul]
    have h1 :
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
      rw [← map_mul, ← map_neg]
      exact hψ.principalInvariant (-(α * β))
    rw [h1, one_mul]

private def principalIdeleOf (a : Fˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a

private theorem principalIdeleOf_smul (a : Fˣ) (x : AdeleRing (𝓞 F) F) :
    principalIdeleOf F a • x = algebraMap F (AdeleRing (𝓞 F) F) (a : F) * x  := rfl

private theorem distribHaarChar_principalIdeleOf (a : Fˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (principalIdeleOf F a) = 1  :=
  NumberField.AdeleRing.distribHaarChar_algebraMap F a

private theorem measurePreserving_principalIdeleOf_smul (a : Fˣ) :
    MeasurePreserving (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x)
      (adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F)  := by
  have hmeas : Measurable (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x) := by
    simp only [principalIdeleOf_smul]
    exact (continuous_const.mul continuous_id).measurable
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Set.preimage_smul,
    ← distribHaarChar_mul (adelicAddHaar (𝓞 F) F) (principalIdeleOf F a)⁻¹ s]
  have h1 : distribHaarChar (AdeleRing (𝓞 F) F) (principalIdeleOf F a)⁻¹ = 1 := by
    rw [map_inv, distribHaarChar_principalIdeleOf, inv_one]
  rw [h1, ENNReal.coe_one, one_mul]

private theorem measurableEmbedding_principalIdeleOf_smul (a : Fˣ) :
    MeasurableEmbedding (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x)  :=
  (Homeomorph.smul (α := AdeleRing (𝓞 F) F) (principalIdeleOf F a)).measurableEmbedding

private theorem whittakerCoefficient_productionPinsOf_eq
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ x in adelicBox F,
            φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
              ∂(adelicAddHaar (𝓞 F) F)  := by
  show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) = _
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]

private theorem image_principalIdeleOf_inv_smul_adelicBox (α : F) (hα : α ≠ 0) :
    (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) '' adelicBox F
      = (fun x : AdeleRing (𝓞 F) F => algebraMap F (AdeleRing (𝓞 F) F) α * x) ⁻¹' adelicBox F  := by
  refine congrFun (Set.image_eq_preimage_of_inverse ?_ ?_) (adelicBox F)
  · intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  · intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ hα, map_one, one_mul]

private theorem whittakerCoefficient_eq_one_diagGL2_mul
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (diagGL2 F α hα) * g)  := by
  rw [whittakerCoefficient_productionPinsOf_eq, whittakerCoefficient_productionPinsOf_eq]

  have hpt : ∀ x : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagGL2 F α hα) * g))
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x))
        = φ (unipotentGL2 (principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α
                * (principalIdeleOf F (Units.mk0 α hα)⁻¹ • x))) := by
    intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, map_one, one_mul]
    rw [← mul_assoc, unipotentGL2_mul_globalPoints_diagGL2 F α hα x, mul_assoc, hleft]
    have hx :
        algebraMap F (AdeleRing (𝓞 F) F) α * (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) = x := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
    rw [hx]

  have himg := (measurePreserving_principalIdeleOf_smul F (Units.mk0 α hα)⁻¹).setIntegral_image_emb
    (measurableEmbedding_principalIdeleOf_smul F (Units.mk0 α hα)⁻¹)
    (fun y => φ (unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y))) (adelicBox F)
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x : AdeleRing (𝓞 F) F => principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) '' adelicBox F)
      (adelicAddHaar (𝓞 F) F) := by
    rw [image_principalIdeleOf_inv_smul_adelicBox F α hα]
    exact NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F
      (adelicAddHaar (𝓞 F) F) α hα
  have hdom := (isAddFundamentalDomain_adelicBox_adelicAddHaar F).setIntegral_eq hFD
    (f := fun y => φ (unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y)))
    (fun γ x => integrand_vadd F ψ hψ φ hleft α g γ x)
  have hint :
      (∫ x in adelicBox F, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
          ∂(adelicAddHaar (𝓞 F) F))
        = ∫ x in adelicBox F,
            φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagGL2 F α hα) * g))
              * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x)) ∂(adelicAddHaar (𝓞 F) F) := by
    rw [funext hpt]
    exact hdom.trans himg
  rw [hint]

private theorem genericity_one
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hcusp : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g₀ = 0)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g₀)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g₀))
    (hg₀ : φ g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 g ≠ 0  := by
  obtain ⟨α, hα⟩ := exists_coefficient_ne_zero F D U gen ψ hψ φ g₀ hcont hsum hg₀
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα hcusp
  refine ⟨globalPoints (𝓞 F) F (diagGL2 F α hα0) * g₀, ?_⟩
  rw [← whittakerCoefficient_eq_one_diagGL2_mul F D U gen ψ hψ φ hleft α hα0 g₀]
  exact hα

end WhittakerGenericity

/-! ## II: the unfolding identity

The two declarations of the unfolding pin that are not already in the import closure: the
countable number field (`countable_numberField`) and the norm-one additive character's
conjugation law (`addChar_neg_eq_conj`). The engine of the unfolding itself
(`setIntegral_adelicBox_comp_add_right`, `integral_cond_adelicBox_comp_add_right`,
`whittakerCoefficient_unipotentGL2_mul`) is AF91's, in
`AutomorphicForm/Adelic/WhittakerCoefficient.lean`. -/

namespace WhittakerUnfolding

variable (F : Type) [Field F] [NumberField F]

theorem countable_numberField : Countable F  :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem addChar_neg_eq_conj (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (y : AdeleRing (𝓞 F) F) : ψ (-y) = (starRingEnd ℂ) (ψ y)  := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ1 y)]

end WhittakerUnfolding

theorem exists_whittakerCoefficient_one_ne_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hcusp : whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 0 g₀
      = 0)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g₀)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ α g₀))
    (hg₀ : φ g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 1 g ≠ 0
  :=
  WhittakerGenericity.genericity_one F D U gen ψ hψ φ hleft g₀ hcusp hcont hsum hg₀

theorem integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper₁ : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ₁ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ₁ (unipotentGL2 u * g))
    (hcont₁ : Continuous fun x : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 x * g))
    (hcont₂ : Continuous fun x : AdeleRing (𝓞 F) F => φ₂ (unipotentGL2 x * g))
    (hbdd₂ : ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F, ‖φ₂ (unipotentGL2 x * g)‖ ≤ C)
    (hsum₁ : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g‖) :
    ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g)
  := by
  have hF : Countable F := WhittakerUnfolding.countable_numberField F
  have hψ1 : ∀ y, ‖ψ y‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hν
  have hνeq : (productionPinsOf F D U gen (adelicBox F)).ν = ν := rfl
  have hprob : IsProbabilityMeasure ν := isProbabilityMeasure_cond_adelicBox F
  set W₁ : F → ℂ := fun α =>
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g with hW₁
  set W₂ : F → ℂ := fun α =>
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g with hW₂
  set h₂ : AdeleRing (𝓞 F) F → ℂ := fun x => φ₂ (unipotentGL2 x * g) with hh₂
  obtain ⟨C, hC⟩ := hbdd₂
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)

  have hA : ∀ x : AdeleRing (𝓞 F) F,
      HasSum (fun α : F => ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * W₁ α)
        (φ₁ (unipotentGL2 x * g)) := by
    intro x
    have hcov : ∀ α : F,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α
            (unipotentGL2 x * g) =
          ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * W₁ α :=
      fun α => whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant φ₁ g hper₁ α x
    have hcontx : Continuous fun y : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 y * (unipotentGL2 x * g)) := by
      have : (fun y : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 y * (unipotentGL2 x * g))) =
          (fun y => φ₁ (unipotentGL2 y * g)) ∘ fun y => y + x := by
        funext y; simp only [Function.comp, ← mul_assoc, ← unipotentGL2_add]
      rw [this]; exact hcont₁.comp (continuous_add_const x)
    have hsumx : Summable fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α
          (unipotentGL2 x * g) := by
      refine Summable.of_norm ?_
      refine hsum₁.congr fun α => ?_
      rw [hcov α, norm_mul, hψ1, one_mul]
    have := hasSum_whittakerCoefficient F D U gen ψ hψ φ₁ (unipotentGL2 x * g) hcontx hsumx
    simpa only [hcov] using this

  have hB : ∀ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (h₂ x) =
      ∑' α : F, W₁ α *
        (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x)) := by
    intro x
    rw [← (hA x).tsum_eq, ← tsum_mul_right]
    exact tsum_congr fun α => by ring

  have hmeas : ∀ α : F, AEStronglyMeasurable
      (fun x => W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))) ν := by
    intro α
    refine (continuous_const.mul ((hψ.continuous.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_conj.comp hcont₂))).aestronglyMeasurable
  have hbound : ∀ (α : F) (x : AdeleRing (𝓞 F) F),
      ‖W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))‖ ≤
        ‖W₁ α‖ * C := by
    intro α x
    rw [norm_mul, norm_mul, hψ1, one_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
  have hint : ∀ α : F, Integrable
      (fun x => W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))) ν :=
    fun α => (integrable_const (‖W₁ α‖ * C)).mono' (hmeas α) (Filter.Eventually.of_forall (hbound α))
  have hsumint : Summable fun α : F =>
      ∫ x, ‖W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun α => integral_nonneg fun x => norm_nonneg _) (fun α => ?_)
      (hsum₁.mul_right C)
    calc ∫ x, ‖W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))‖ ∂ν
        ≤ ∫ x, ‖W₁ α‖ * C ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall (hbound α))
      _ = ‖W₁ α‖ * C := by simp

  have hC' : ∀ α : F,
      ∫ x, ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x) ∂ν =
        (starRingEnd ℂ) (W₂ α) := by
    intro α
    have : W₂ α = ∫ x, h₂ x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂ν := rfl
    rw [this, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, WhittakerUnfolding.addChar_neg_eq_conj F ψ hψ1, Complex.conj_conj]
    ring

  rw [hνeq]
  calc ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g)) ∂ν
      = ∫ x, ∑' α : F, W₁ α *
          (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x)) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hB)
    _ = ∑' α : F, ∫ x, W₁ α *
          (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x)) ∂ν :=
        (integral_tsum_of_summable_integral_norm hint hsumint).symm
    _ = ∑' α : F, W₁ α * (starRingEnd ℂ) (W₂ α) := by
        refine tsum_congr fun α => ?_
        rw [integral_const_mul, hC' α]

end AutomorphicForm

end
