/-
  The Haar measure of the adèlic Borel subgroup, disintegrated.

  Every locally finite, open-positive, left-invariant measure `μB` on the Borel subgroup of `GL₂(𝔸_K)`
  is, up to a single constant `c ∈ (0, ∞)`, the product of the additive Haar measure on the unipotent
  radical, two copies of the idèle Haar measure, and the `‖t‖⁻¹` density:

  `∫⁻ b, F b ∂μB = c · ∫⁻ x ∫⁻ u ∫⁻ t, F (n(x) · z(u) · diag(t)) · ‖t‖⁻¹`.

  This is the measure-theoretic form of the Iwasawa/Bruhat decomposition of the Borel — the identity that
  turns an integral over `B(𝔸_K)` into iterated integrals over `𝔸_K`, the idèles, and the idèles again.
  It is the standard first step of the unfolding arguments (the cuspidal unfolding, the Rankin–Selberg
  integral, the constant term) and it is the row SET-AF39 deferred because the port lacked the idèle
  measure `NumberField.Idele.idelicHaar` (now ported in the definition layer of SET-AF40).

  Transcribed whole from the pin's proof file
  `P2M/Sol/S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean`
  (pinned `aa2d8b3`, 429 lines / 36 declarations) and its statement from the wrapper
  `Theorems/Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean`.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.NumberTheory.NumberField.IdeleProductMeasure
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
-- Three imports beyond the scaffold, each carrying one of the pin's own `Theorems/` imports:
-- `TateGlobalContinuousIdeleNorm` = the pin's `Thm_NumberField_TateGlobal_continuous_ideleNorm`
-- (pin `:189`), `AdelicLevel.Countability` = the pin's second-countability theorems (pin `:209`,
-- `:215`), `AdelicHaar.ProductFormula` = the port's `regular_adelicAddHaar` for the pin's
-- `unfold adelicAddHaar Measure.addHaar; infer_instance` (pin `:252`).
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicHaar.ProductFormula

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicForm

-- The pin's local instance wall (its `S_` file sets the same six).
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace BorelCoord

variable (K : Type) [Field K] [NumberField K]

-- The pin's `haveI : <class> := …` are the port's named `have`: mathlib `v4.34.0`'s
-- `linter.style.haveILetI` warns on them (the goal is a proposition), and the module builds
-- warning-free. `have` registers the local instance just the same (playbook, `AdelicModulus.lean`).

/-! ### Block 1 — the Borel coordinate maps -/

-- pin `:32` `continuous_unipotentGL2` is the port's `AutomorphicForm.continuous_unipotentGL2`
-- (`ConstantTerm.lean`), stated for a general topological ring: it is reused, not restated.

-- pin `:44`
private theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((centralScalar (𝓞 K) K u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

-- pin `:55`
private theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((diagOne u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.diagonal ![(u : AdeleRing (𝓞 K) K), 1]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

-- pin `:68`
private def psiG (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    AdelicGL2 (𝓞 K) K :=
  unipotentGL2 p.1 * centralScalar (𝓞 K) K p.2.1 * diagOne p.2.2

-- pin `:71`
private theorem psiG_apply (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)
    (i j : Fin 2) :
    ((psiG K p : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      !![(p.2.1 : AdeleRing (𝓞 K) K) * p.2.2, p.1 * p.2.1; 0,
        (p.2.1 : AdeleRing (𝓞 K) K)] i j := by
  rw [psiG, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  change (!![1, p.1; 0, 1] * Matrix.scalar (Fin 2) (p.2.1 : AdeleRing (𝓞 K) K) *
    Matrix.diagonal ![(p.2.2 : AdeleRing (𝓞 K) K), 1]) i j = _
  rw [Matrix.scalar_apply, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

-- pin `:81`
private theorem psiG_mem (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    psiG K p ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff, psiG_apply]; rfl

-- pin `:85`
private theorem continuous_psiG : Continuous (psiG K) :=
  (((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp continuous_fst).mul
    ((continuous_centralScalar K).comp (continuous_fst.comp continuous_snd))).mul
    ((continuous_diagOne K).comp (continuous_snd.comp continuous_snd))

-- pin `:90`
private def psi (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    adelicBorel (𝓞 K) K :=
  ⟨psiG K p, psiG_mem K p⟩

-- pin `:93`
private theorem continuous_psi : Continuous (psi K) := (continuous_psiG K).subtype_mk _

-- pin `:95`
private def theta (b : adelicBorel (𝓞 K) K) :
    AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
  (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 *
      ((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ),
    borelDiagSnd b, borelDiagFst b * (borelDiagSnd b)⁻¹)

-- pin `:99`
private theorem continuous_borelDiagSnd :
    Continuous (borelDiagSnd : adelicBorel (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
  have hent : ∀ i j : Fin 2, Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp
      continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hent 1 1, ?_⟩
  simp_rw [← map_inv]
  exact (hent 1 1).comp continuous_inv

-- pin `:107`
private theorem continuous_borelDiagFst :
    Continuous (borelDiagFst : adelicBorel (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
  have hent : ∀ i j : Fin 2, Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp
      continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hent 0 0, ?_⟩
  simp_rw [← map_inv]
  exact (hent 0 0).comp continuous_inv

-- pin `:115`
private theorem continuous_theta : Continuous (theta K) := by
  have h01 : Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) :=
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0 1).comp
      continuous_subtype_val
  refine (h01.mul (Units.continuous_val.comp ((continuous_borelDiagSnd K).inv))).prodMk
    ((continuous_borelDiagSnd K).prodMk ((continuous_borelDiagFst K).mul (continuous_borelDiagSnd K).inv))

-- pin `:122`
private theorem theta_psi (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    theta K (psi K p) = p := by
  obtain ⟨x, u, t⟩ := p
  have hsnd : borelDiagSnd (psi K (x, u, t)) = u := Units.ext (by
    change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = (u : AdeleRing (𝓞 K) K)
    rw [psiG_apply]; rfl)
  have hfst : borelDiagFst (psi K (x, u, t)) = u * t := Units.ext (by
    change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = (u : AdeleRing (𝓞 K) K) * t
    rw [psiG_apply]; rfl)
  simp only [theta, hsnd, hfst]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 * _ = x
    rw [psiG_apply]
    change x * (u : AdeleRing (𝓞 K) K) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = x
    rw [mul_assoc, Units.mul_inv, mul_one]
  · change u * t * u⁻¹ = t
    rw [mul_comm u t, mul_inv_cancel_right]

-- pin `:140`
private theorem psi_theta (b : adelicBorel (𝓞 K) K) : psi K (theta K b) = b := by
  have h10 : (((b : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := b.2
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change ((psiG K (theta K b) : AdelicGL2 (𝓞 K) K) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = _
  rw [psiG_apply]
  set M := (((b : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) with hM
  have hu : ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 1 1 := rfl
  have ht : ((borelDiagFst b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 0 := rfl
  have hinv : M 1 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by
    rw [← hu, Units.mul_inv]
  have e00 : ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
      ((borelDiagFst b * (borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K) = M 0 0 := by
    rw [Units.val_mul, hu, ht, mul_left_comm, hinv, mul_one]
  have e01 : M 0 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
      ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 1 := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  simp only [theta]
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact h10.symm
  · exact hu

-- pin `:162`
private def psiHomeo :
    (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ adelicBorel (𝓞 K) K where
  toFun := psi K
  invFun := theta K
  left_inv := theta_psi K
  right_inv := psi_theta K
  continuous_toFun := continuous_psi K
  continuous_invFun := continuous_theta K

-- pin `:170`
private def lmul (p q : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
  (p.1 + (p.2.2 : AdeleRing (𝓞 K) K) * q.1, p.2.1 * q.2.1, p.2.2 * q.2.2)

-- pin `:174`
private theorem psi_mul (p q : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    psi K p * psi K q = psi K (lmul K p q) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change (((psiG K p : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
      ((psiG K q : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) i j =
    ((psiG K (lmul K p q) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, psiG_apply, psiG_apply, psiG_apply, psiG_apply, psiG_apply]
  simp only [lmul, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-! ### Block 2 — the densities and the measures -/

-- pin `:184`
private def dens (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

-- pin `:186`
private theorem continuous_dens : Continuous (dens K) := by
  unfold dens
  refine ENNReal.continuous_ofReal.comp ?_
  exact (NumberField.TateGlobal.continuous_ideleNorm K).inv₀ fun t =>
    (NumberField.TateGlobal.ideleNorm_pos t).ne'

-- pin `:191`
private theorem measurable_dens : Measurable (dens K) := (continuous_dens K).measurable

-- pin `:193`
private theorem dens_pos (t : (AdeleRing (𝓞 K) K)ˣ) : 0 < dens K t :=
  ENNReal.ofReal_pos.mpr (inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos t))

-- pin `:196`
private theorem dens_mul (t₀ t : (AdeleRing (𝓞 K) K)ˣ) :
    dens K (t₀⁻¹ * t) = (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) * dens K t := by
  unfold dens NumberField.TateGlobal.ideleNorm
  rw [map_mul, map_inv, NNReal.coe_mul, mul_inv, NNReal.coe_inv, inv_inv,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

-- pin `:202`
private def idelicHaarW : Measure (AdeleRing (𝓞 K) K)ˣ :=
  (NumberField.Idele.idelicHaar K).withDensity (dens K)

-- pin `:204`
private def rho : Measure (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
  (adelicAddHaar (𝓞 K) K).prod ((NumberField.Idele.idelicHaar K).prod (idelicHaarW K))

-- pin `:207`
private def kappa : Measure (adelicBorel (𝓞 K) K) := (rho K).map (psi K)

-- pin `:209`
scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

-- pin `:211`
scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  have hop : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

-- pin `:215`
scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

-- pin `:218`
scoped instance secondCountableTopology_borel : SecondCountableTopology (adelicBorel (𝓞 K) K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

-- pin `:221`
private theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) := by
  have : (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) =
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0) ⁻¹' {0} := by
    -- Adapted (pin `:224`): the port's `mem_borelSubgroup_iff` has `A` as an explicit binder,
    -- so the pin's `mem_borelSubgroup_iff _` is spelled `(A := …)` here.
    ext g; exact mem_borelSubgroup_iff (A := AdeleRing (𝓞 K) K)
  rw [this]
  exact isClosed_singleton.preimage
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 1 0)

-- pin `:228`
scoped instance locallyCompactSpace_borel : LocallyCompactSpace (adelicBorel (𝓞 K) K) :=
  (isClosed_adelicBorel K).locallyCompactSpace

-- pin `:230`
scoped instance sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 K) K) := by
  have hhaar := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  infer_instance

-- pin `:234`
scoped instance locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

-- pin `:237`
scoped instance sigmaCompactSpace_idele : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  @sigmaCompactSpace_of_locallyCompact_secondCountable _ _ (locallyCompactSpace_idele K)
    (secondCountableTopology_idele K)

-- pin `:240`
scoped instance sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  infer_instance

-- pin `:244`
scoped instance sFinite_idelicHaarW : SFinite (idelicHaarW K) := by
  unfold idelicHaarW; infer_instance

-- pin `:246`
scoped instance sFinite_rho : SFinite (rho K) := by unfold rho; infer_instance

/-! ### Block 3 — the invariance laws -/

-- pin `:248` (the pin's `unfold adelicAddHaar Measure.addHaar; infer_instance` for `Regular` is the
-- port's `regular_adelicAddHaar`)
private theorem map_mul_left_adelicAddHaar (x₀ : AdeleRing (𝓞 K) K)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    (adelicAddHaar (𝓞 K) K).map (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) t₀)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
  have hadd := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hreg : (adelicAddHaar (𝓞 K) K).Regular := NumberField.AdelicHaar.regular_adelicAddHaar K
  have h1 : (adelicAddHaar (𝓞 K) K).map (fun x => (t₀ : AdeleRing (𝓞 K) K) * x) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) t₀)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
    refine Measure.ext fun s hs => ?_
    open scoped Pointwise in
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul,
      show (fun y => (t₀ : AdeleRing (𝓞 K) K) * y) ⁻¹' s = t₀⁻¹ • s from Set.preimage_smul t₀ s,
      ← distribHaarChar_mul (adelicAddHaar (𝓞 K) K) t₀⁻¹ s, map_inv]
  have hcomp : (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) =
      (fun x => x₀ + x) ∘ (fun x => (t₀ : AdeleRing (𝓞 K) K) * x) := rfl
  -- Adapted (pin `:264`): mathlib `v4.34.0`'s `Measure.map_smul` takes its `AEMeasurable`
  -- argument explicitly (`map_smul (c) {μ} {f} (hf)`), where `v4.33.0`'s was bare.
  rw [hcomp, ← Measure.map_map (measurable_const_add x₀) (measurable_const_mul _), h1,
    Measure.map_smul _ (measurable_const_add x₀).aemeasurable, map_add_left_eq_self]

-- pin `:266`
private theorem map_mul_left_idelicHaarW (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    (idelicHaarW K).map (fun t => t₀ * t) =
      (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) • idelicHaarW K := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul, idelicHaarW,
    withDensity_apply _ (measurable_const_mul _ hs), withDensity_apply _ hs]
  have h := lintegral_mul_left_eq_self (μ := NumberField.Idele.idelicHaar K)
    (fun t => s.indicator (dens K ∘ fun t => t₀⁻¹ * t) t) t₀
  have hind : ∀ t, s.indicator (dens K ∘ fun t => t₀⁻¹ * t) (t₀ * t) =
      ((fun t => t₀ * t) ⁻¹' s).indicator (dens K) t := by
    intro t
    simp only [Set.indicator, Set.mem_preimage, Function.comp_apply, inv_mul_cancel_left]
    rfl
  simp_rw [hind] at h
  rw [← lintegral_indicator (measurable_const_mul _ hs), h, ← lintegral_indicator hs]
  have hdens : ∀ t, s.indicator (dens K ∘ fun t => t₀⁻¹ * t) t =
      (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) * s.indicator (dens K) t := by
    intro t
    simp only [Set.indicator, Function.comp_apply, dens_mul]
    split_ifs <;> simp
  simp_rw [hdens]
  rw [lintegral_const_mul _ ((measurable_dens K).indicator hs)]

-- pin `:290`
private theorem map_lmul_rho
    (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    (rho K).map (lmul K p) = rho K := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨x₀, u₀, t₀⟩ := p
  have hl : lmul K (x₀, u₀, t₀) = Prod.map (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x)
      (Prod.map (fun u => u₀ * u) (fun t => t₀ * t)) := rfl
  have hmx : Measurable (fun x : AdeleRing (𝓞 K) K => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) :=
    (measurable_const_add x₀).comp (measurable_const_mul _)
  have hmu : Measurable (fun u : (AdeleRing (𝓞 K) K)ˣ => u₀ * u) := measurable_const_mul u₀
  have hmt : Measurable (fun t : (AdeleRing (𝓞 K) K)ˣ => t₀ * t) := measurable_const_mul t₀
  rw [hl, rho, ← Measure.map_prod_map _ _ hmx (hmu.prodMap hmt), ← Measure.map_prod_map _ _ hmu hmt,
    map_mul_left_adelicAddHaar, map_mul_left_eq_self, map_mul_left_idelicHaarW,
    Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul,
    ← ENNReal.coe_mul, mul_inv_cancel₀ (distribHaarChar_pos (g := t₀)).ne', ENNReal.coe_one,
    one_smul]

-- pin `:304`
private theorem continuous_lmul
    (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    Continuous (lmul K p) := by
  unfold lmul
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_const.mul (continuous_snd.comp continuous_snd)))

-- pin `:310`
scoped instance isMulLeftInvariant_kappa : (kappa K).IsMulLeftInvariant := by
  refine ⟨fun b₀ => ?_⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀, psi K p₀ = b₀ := ⟨theta K b₀, psi_theta K b₀⟩
  rw [kappa, Measure.map_map (measurable_const_mul _) (continuous_psi K).measurable]
  have hmul : (fun b => psi K p₀ * b) ∘ psi K = psi K ∘ lmul K p₀ :=
    funext fun q => psi_mul K p₀ q
  rw [hmul, ← Measure.map_map (continuous_psi K).measurable, map_lmul_rho]
  exact (continuous_lmul K p₀).measurable

-- pin `:318`
scoped instance isFiniteMeasureOnCompacts_idelicHaarW : IsFiniteMeasureOnCompacts (idelicHaarW K) := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  refine ⟨fun C hC => ?_⟩
  rw [idelicHaarW, withDensity_apply _ hC.measurableSet]
  rcases C.eq_empty_or_nonempty with h | h
  · simp [h]
  obtain ⟨t₁, _, ht₁⟩ := hC.exists_isMaxOn h (continuous_dens K).continuousOn
  calc ∫⁻ t in C, dens K t ∂(NumberField.Idele.idelicHaar K)
      ≤ ∫⁻ _ in C, dens K t₁ ∂(NumberField.Idele.idelicHaar K) :=
        setLIntegral_mono measurable_const fun t ht => ht₁ ht
    _ = dens K t₁ * (NumberField.Idele.idelicHaar K) C := setLIntegral_const C _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

-- pin `:330`
scoped instance isFiniteMeasureOnCompacts_rho : IsFiniteMeasureOnCompacts (rho K) := by
  have hadd := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  unfold rho; infer_instance

-- pin `:335`
scoped instance isFiniteMeasureOnCompacts_kappa : IsFiniteMeasureOnCompacts (kappa K) := by
  refine ⟨fun C hC => ?_⟩
  rw [kappa, Measure.map_apply (continuous_psi K).measurable hC.measurableSet]
  exact ((psiHomeo K).isCompact_preimage.mpr hC).measure_lt_top

/-! ### Block 4 — the assembly -/

-- pin `:340`
private theorem idelicHaarW_univ_ne_zero : idelicHaarW K Set.univ ≠ 0 := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  rw [idelicHaarW, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h
  rw [lintegral_eq_zero_iff (measurable_dens K)] at h
  have h2 : (NumberField.Idele.idelicHaar K) Set.univ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact h.mono fun t ht htU => (dens_pos K t).ne' ht
  exact isOpen_univ.measure_ne_zero (NumberField.Idele.idelicHaar K) Set.univ_nonempty h2

-- pin `:350`
private theorem kappa_univ_ne_zero : kappa K Set.univ ≠ 0 := by
  have hadd := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  rw [kappa, Measure.map_apply (continuous_psi K).measurable MeasurableSet.univ, Set.preimage_univ, rho,
    ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  refine mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    (mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty) (idelicHaarW_univ_ne_zero K))

-- pin `:358`
private theorem exists_eq_mul_lintegral_kappa (μB : Measure (adelicBorel (𝓞 K) K))
    [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB] [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ F : adelicBorel (𝓞 K) K → ℝ≥0∞,
      ∫⁻ b, F b ∂μB = c * ∫⁻ b, F b ∂(kappa K) := by
  have hμB : μB.IsHaarMeasure := ⟨⟩
  set c' := Measure.haarScalarFactor (kappa K) μB with hc'
  have hκ : kappa K = c' • μB := Measure.isMulLeftInvariant_eq_smul (kappa K) μB
  have hc0 : c' ≠ 0 := by
    intro h0
    apply kappa_univ_ne_zero K
    rw [hκ, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  refine ⟨((c' : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hc0), fun F => ?_⟩
  have h1 : ∫⁻ b, F b ∂(kappa K) = (c' : ℝ≥0∞) * ∫⁻ b, F b ∂μB := by
    rw [hκ, lintegral_smul_measure]
    rfl
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top,
    one_mul]

end BorelCoord

open BorelCoord in
theorem exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
    (K : Type) [Field K] [NumberField K]
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : AdelicGL2 (𝓞 K) K) ∂μB =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t,
                F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K) := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨c, hc0, hctop, hc⟩ := exists_eq_mul_lintegral_kappa K μB
  refine ⟨c, hc0, hctop, fun F hF => ?_⟩
  rw [hc (fun b => F b)]
  congr 1
  set Φ : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ :=
    fun p => F (psiG K p) with hΦ_def
  have hΦ : Measurable Φ := hF.comp (continuous_psiG K).measurable
  have hFb : Measurable fun b : adelicBorel (𝓞 K) K => F (b : AdelicGL2 (𝓞 K) K) :=
    hF.comp measurable_subtype_coe
  rw [kappa, lintegral_map hFb (continuous_psi K).measurable]
  change ∫⁻ p, Φ p ∂(rho K) = _
  rw [rho, lintegral_prod _ hΦ.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hΦx : Measurable fun q : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => Φ (x, q) :=
    hΦ.comp measurable_prodMk_left
  rw [lintegral_prod _ hΦx.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hΦxu : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => Φ (x, u, t) :=
    hΦx.comp measurable_prodMk_left
  rw [idelicHaarW, lintegral_withDensity_eq_lintegral_mul _ (measurable_dens K) hΦxu]
  refine lintegral_congr fun t => ?_
  simp only [Pi.mul_apply, hΦ_def, dens, psiG, mul_comm]

end AutomorphicForm
