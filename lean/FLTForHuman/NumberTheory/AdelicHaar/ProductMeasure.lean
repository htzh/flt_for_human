/-
  The adelic Haar measure: the product formula and the measure of the coordinate hyperplanes.

  Three statements about the Haar measure on `GL2(A)` and on the adeles:

  * the `GL2`-Haar measure is a constant times a product of local and archimedean factors
    (`exists_map_adelicGLHaar_eq_smul_prod`);
  * the adelic Haar measure of the hyperplane `{x | x.fst = 0}` is zero
    (`adelicAddHaar_setOf_fst_apply_eq_eq_zero`);
  * the same for `{x | x.snd = 0}` (`adelicAddHaar_setOf_snd_apply_eq_zero`).

  These are the measure-theoretic facts the factorizable-test-function and Bruhat-Eisenstein integrals
  consume.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod.lean` (215 lines),
  `..._adelicAddHaar_setOf_fst_apply_eq_eq_zero.lean` (128) and `..._adelicAddHaar_setOf_snd_apply_eq_zero.lean`
  (119), with the statements from their wrappers.

  Assumes from earlier modules: the adelic Haar measure and its modulus character
  (`NumberTheory/AdelicHaar/*`), the adelic level structure (`NumberTheory/AdelicLevel/*`) and
  mathlib's Haar measure API.

  spec-pin: Theorems/Thm_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod.lean
  spec-pin: Theorems/Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero.lean
  spec-pin: Theorems/Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero.lean
-/
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicHaar.ProductFormula
import FLTForHuman.NumberTheory.AdelicHaar.AdelicModulus
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar Topology
open scoped NNReal Pointwise Classical

namespace ProductMeasure
namespace L1

section SC

variable (K : Type) [Field K] [NumberField K]

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have hf : IsEmbedding (fun a : InfiniteAdeleRing K => ((a, 0) : AdeleRing (𝓞 K) K)) :=
    IsEmbedding.of_comp (continuous_id.prodMk continuous_const) continuous_fst IsEmbedding.id
  hf.secondCountableTopology

theorem secondCountableTopology_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have hf : IsEmbedding (fun b : FiniteAdeleRing (𝓞 K) K => ((0, b) : AdeleRing (𝓞 K) K)) :=
    IsEmbedding.of_comp (continuous_const.prodMk continuous_id) continuous_snd IsEmbedding.id
  hf.secondCountableTopology

theorem secondCountableTopology_gl (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R] :
    SecondCountableTopology (GL n R) :=
  haveI : SecondCountableTopology (Matrix n n R) := inferInstanceAs (SecondCountableTopology (n → n → R))
  haveI : SecondCountableTopology (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_gl (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] :
    LocallyCompactSpace (GL n R) :=
  haveI : LocallyCompactSpace (Matrix n n R) := inferInstanceAs (LocallyCompactSpace (n → n → R))
  haveI : T2Space (Matrix n n R) := inferInstanceAs (T2Space (n → n → R))
  haveI : LocallyCompactSpace (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end SC

section Split

variable (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]

def fwd : GL n (AdeleRing (𝓞 K) K) →* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  MonoidHom.prod (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K))
    (Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K))

def glue (a : Matrix n n (InfiniteAdeleRing K)) (b : Matrix n n (FiniteAdeleRing (𝓞 K) K)) :
    Matrix n n (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => ((a i j, b i j) : AdeleRing (𝓞 K) K)

omit [DecidableEq n] in
theorem glue_mul (a a' : Matrix n n (InfiniteAdeleRing K)) (b b' : Matrix n n (FiniteAdeleRing (𝓞 K) K)) :
    glue n K a b * glue n K a' b' = glue n K (a * a') (b * b') := by
  ext i j
  simp only [glue, Matrix.mul_apply]
  change (_ : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) = _
  refine Prod.ext ?_ ?_
  · show (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (∑ x, _) = _
    exact map_sum (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) _ Finset.univ
  · show (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (∑ x, _) = _
    exact map_sum (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) _ Finset.univ

omit [Fintype n] in
theorem glue_one : glue n K (1 : Matrix n n (InfiniteAdeleRing K)) (1 : Matrix n n (FiniteAdeleRing (𝓞 K) K)) = 1 := by
  ext i j
  change ((1 : Matrix n n (InfiniteAdeleRing K)) i j, (1 : Matrix n n (FiniteAdeleRing (𝓞 K) K)) i j) =
    ((1 : Matrix n n (AdeleRing (𝓞 K) K)) i j)
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, Matrix.one_apply_ne h]
    rfl

def bwd (p : GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) : GL n (AdeleRing (𝓞 K) K) where
  val := glue n K (p.1 : Matrix n n (InfiniteAdeleRing K)) (p.2 : Matrix n n (FiniteAdeleRing (𝓞 K) K))
  inv := glue n K ((p.1⁻¹ : GL n (InfiniteAdeleRing K)) : Matrix n n (InfiniteAdeleRing K))
    ((p.2⁻¹ : GL n (FiniteAdeleRing (𝓞 K) K)) : Matrix n n (FiniteAdeleRing (𝓞 K) K))
  val_inv := by rw [glue_mul, Units.mul_inv, Units.mul_inv, glue_one]
  inv_val := by rw [glue_mul, Units.inv_mul, Units.inv_mul, glue_one]

theorem fwd_bwd (p : GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) : fwd n K (bwd n K p) = p :=
  Prod.ext (Units.ext (Matrix.ext fun _ _ => rfl)) (Units.ext (Matrix.ext fun _ _ => rfl))

theorem bwd_fwd (x : GL n (AdeleRing (𝓞 K) K)) : bwd n K (fwd n K x) = x :=
  Units.ext (Matrix.ext fun _ _ => Prod.ext rfl rfl)

def splitMulEquiv : GL n (AdeleRing (𝓞 K) K) ≃* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  { toFun := fwd n K
    invFun := bwd n K
    left_inv := bwd_fwd n K
    right_inv := fwd_bwd n K
    map_mul' := map_mul (fwd n K) }

theorem continuous_fwd : Continuous (fwd n K) := by
  refine Continuous.prodMk ?_ ?_
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.matrix_map continuous_fst).comp Units.continuous_val
    · have : (fun x : GL n (AdeleRing (𝓞 K) K) =>
          ((↑(Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x)⁻¹ : Matrix n n (InfiniteAdeleRing K))))
          = fun x => (RingHom.mapMatrix (adeleArch (𝓞 K) K)) ((x⁻¹ : GL n (AdeleRing (𝓞 K) K)) : Matrix _ _ _) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_id.matrix_map continuous_fst).comp Units.continuous_coe_inv
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.matrix_map continuous_snd).comp Units.continuous_val
    · have : (fun x : GL n (AdeleRing (𝓞 K) K) =>
          ((↑(Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x)⁻¹ : Matrix n n (FiniteAdeleRing (𝓞 K) K))))
          = fun x => (RingHom.mapMatrix (adeleFin (𝓞 K) K)) ((x⁻¹ : GL n (AdeleRing (𝓞 K) K)) : Matrix _ _ _) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_id.matrix_map continuous_snd).comp Units.continuous_coe_inv

omit [Fintype n] [DecidableEq n] in
theorem continuous_glue : Continuous (fun p : Matrix n n (InfiniteAdeleRing K) × Matrix n n (FiniteAdeleRing (𝓞 K) K) =>
    glue n K p.1 p.2) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_apply_apply i j).comp continuous_fst).prodMk ((continuous_apply_apply i j).comp continuous_snd)

theorem continuous_bwd : Continuous (bwd n K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_glue n K).comp
      ((Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd))
  · exact (continuous_glue n K).comp
      ((Units.continuous_coe_inv.comp continuous_fst).prodMk (Units.continuous_coe_inv.comp continuous_snd))

def splitEquiv : GL n (AdeleRing (𝓞 K) K) ≃ₜ* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  { splitMulEquiv n K with
    continuous_toFun := continuous_fwd n K
    continuous_invFun := continuous_bwd n K }

theorem splitEquiv_apply (x : GL n (AdeleRing (𝓞 K) K)) :
    splitEquiv n K x = (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x,
      Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x) := rfl

end Split

section Main

variable (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]

theorem main
    [MeasurableSpace (GL n (InfiniteAdeleRing K))] [BorelSpace (GL n (InfiniteAdeleRing K))]
    [MeasurableSpace (GL n (FiniteAdeleRing (𝓞 K) K))] [BorelSpace (GL n (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL n (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL n (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (letI := glBorel n (𝓞 K) K
       Measure.map
           (fun x : GL n (AdeleRing (𝓞 K) K) =>
             (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x,
               Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x))
           (adelicGLHaar n (𝓞 K) K) = c • μa.prod μf) :=
  letI : MeasurableSpace (GL n (AdeleRing (𝓞 K) K)) := glBorel n (𝓞 K) K
  haveI : BorelSpace (GL n (AdeleRing (𝓞 K) K)) := borelSpace_glBorel n (𝓞 K) K
  haveI : (adelicGLHaar n (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar n (𝓞 K) K
  haveI : SecondCountableTopology (InfiniteAdeleRing K) := secondCountableTopology_infiniteAdeleRing K
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := secondCountableTopology_finiteAdeleRing K
  haveI : SecondCountableTopology (GL n (InfiniteAdeleRing K)) := secondCountableTopology_gl n (InfiniteAdeleRing K)
  haveI : SecondCountableTopology (GL n (FiniteAdeleRing (𝓞 K) K)) :=
    secondCountableTopology_gl n (FiniteAdeleRing (𝓞 K) K)
  haveI : LocallyCompactSpace (GL n (InfiniteAdeleRing K)) := locallyCompactSpace_gl n (InfiniteAdeleRing K)
  haveI : LocallyCompactSpace (GL n (FiniteAdeleRing (𝓞 K) K)) := locallyCompactSpace_gl n (FiniteAdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) := Prod.borelSpace
  let ν : Measure (GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) :=
    Measure.map (splitEquiv n K) (adelicGLHaar n (𝓞 K) K)
  haveI : ν.IsHaarMeasure := (splitEquiv n K).isHaarMeasure_map _
  haveI : (μa.prod μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μa μf
  haveI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  haveI : (μa.prod μf).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  by
    have h := Measure.isMulLeftInvariant_eq_smul_of_regular ν (μa.prod μf)
    refine ⟨ν.haarScalarFactor (μa.prod μf), Measure.haarScalarFactor_pos_of_isHaarMeasure ν (μa.prod μf), ?_⟩
    have hfun : (fun x : GL n (AdeleRing (𝓞 K) K) =>
        (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x, Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x))
        = (splitEquiv n K : GL n (AdeleRing (𝓞 K) K) → _) := rfl
    rw [hfun]
    exact h

end Main

end ProductMeasure.L1

namespace FstHyperplane

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private theorem norm_two : ‖(2 : w.Completion)‖ = 2 := by
  have hfin : Fintype (InfinitePlace F) := inferInstance
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (2 : w.Completion)
  rw [← h, map_ofNat]; norm_num

private theorem two_ne : (2 : w.Completion) ≠ 0 := by
  intro h; have := norm_two F w; rw [h, norm_zero] at this; norm_num at this

private def aAd : AdeleRing (𝓞 F) F := (Function.update 1 w 2, 1)
private def aInv : AdeleRing (𝓞 F) F := (Function.update 1 w 2⁻¹, 1)

private theorem aAd_fst_self : (aAd F w).1 w = 2 := by simp [aAd]

private theorem aAd_fst_of_ne {w' : InfinitePlace F} (h : w' ≠ w) : (aAd F w).1 w' = 1 := by simp [aAd, h]

private theorem aInv_fst_self : (aInv F w).1 w = 2⁻¹ := by simp [aInv]

private theorem aInv_fst_of_ne {w' : InfinitePlace F} (h : w' ≠ w) : (aInv F w).1 w' = 1 := by simp [aInv, h]

private theorem aAd_mul_aInv : aAd F w * aInv F w = 1 := by
  refine Prod.ext (funext fun w' => ?_) (by change (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1; rw [mul_one])
  change (aAd F w).1 w' * (aInv F w).1 w' = 1
  by_cases h : w' = w
  · subst h; rw [aAd_fst_self, aInv_fst_self, mul_inv_cancel₀ (two_ne F w')]
  · rw [aAd_fst_of_ne F w h, aInv_fst_of_ne F w h, mul_one]

private def aU : (AdeleRing (𝓞 F) F)ˣ := ⟨aAd F w, aInv F w, aAd_mul_aInv F w, by rw [mul_comm]; exact aAd_mul_aInv F w⟩

private theorem distribHaarChar_aU : (distribHaarChar (AdeleRing (𝓞 F) F) (aU F w) : ℝ) = 2 ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl F (aU F w) rfl]
  change (∏ w' : InfinitePlace F, ‖(aAd F w).1 w'‖ ^ w'.mult) = _
  rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [aAd_fst_of_ne F w hw', norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ w) h),
    aAd_fst_self, norm_two]

private theorem smul_eq_self_of_mem {x : AdeleRing (𝓞 F) F} (hx : x.1 w = 0) :
    ((aU F w : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • x = x := by
  change aAd F w * x = x
  refine Prod.ext (funext fun w' => ?_) (by change (1 : FiniteAdeleRing (𝓞 F) F) * x.2 = x.2; rw [one_mul])
  change (aAd F w).1 w' * x.1 w' = x.1 w'
  by_cases h : w' = w
  · subst h; rw [hx, mul_zero]
  · rw [aAd_fst_of_ne F w h, one_mul]

private theorem smul_inter (C : Set (AdeleRing (𝓞 F) F)) :
    (aU F w) • ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C) = {x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ((aU F w : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • x ∈ _
    rw [smul_eq_self_of_mem F w hx.1]; exact hx
  · intro hy
    exact ⟨y, hy, smul_eq_self_of_mem F w hy.1⟩

private theorem piece_null (C : Set (AdeleRing (𝓞 F) F)) (hfin : adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C) ≠ ⊤) :
    adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C) = 0 :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := NumberField.AdelicHaar.regular_adelicAddHaar F
  by
    have h := distribHaarChar_mul (adelicAddHaar (𝓞 F) F) (aU F w) ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C)
    rw [smul_inter] at h
    by_contra hne
    have hδ : ((distribHaarChar (AdeleRing (𝓞 F) F) (aU F w) : NNReal) : ENNReal) = 1 := by
      have := (ENNReal.mul_left_inj hne hfin).mp (h.trans (one_mul _).symm)
      exact_mod_cast this
    have hδ' : (distribHaarChar (AdeleRing (𝓞 F) F) (aU F w) : ℝ) = 1 := by exact_mod_cast hδ
    rw [distribHaarChar_aU] at hδ'
    have : (1 : ℝ) < 2 ^ w.mult := one_lt_pow₀ (by norm_num) (InfinitePlace.mult_pos).ne'
    exact this.ne' hδ'

private theorem null_zero : adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = 0} = 0 :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  by
    have hcov : {x : AdeleRing (𝓞 F) F | x.1 w = 0} = ⋃ n, ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ compactCovering (AdeleRing (𝓞 F) F) n) := by
      rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [hcov]
    refine measure_iUnion_null fun n => piece_null F w _ ?_
    exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (isCompact_compactCovering _ n).measure_lt_top).ne

theorem main (c : w.Completion) : adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = c} = 0 :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  by
    set y : AdeleRing (𝓞 F) F := (Function.update 0 w c, 0) with hy
    have hyw : y.1 w = c := by
      show (Function.update (0 : InfiniteAdeleRing F) w c) w = c
      exact Function.update_self w c 0
    have hset : {x : AdeleRing (𝓞 F) F | x.1 w = c} = (fun x => -y + x) ⁻¹' {x : AdeleRing (𝓞 F) F | x.1 w = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      show x.1 w = c ↔ (-y + x).1 w = 0
      rw [show (-y + x).1 w = - y.1 w + x.1 w from rfl, hyw]
      constructor
      · intro h; rw [h, neg_add_cancel]
      · intro h; exact (neg_add_eq_zero.mp h).symm
    rw [hset, measure_preimage_add]
    exact null_zero F w

end FstHyperplane

namespace SndHyperplane

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem exists_small : ∃ π : v.adicCompletion F, π ≠ 0 ∧ ‖π‖ < 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hvπ : Valued.v ((π : F) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  refine ⟨(π : F), fun h => ?_, ?_⟩
  · rw [h, Valuation.map_zero] at hvπ; exact WithZero.zero_ne_coe hvπ
  · rw [Valued.toNormedField.norm_lt_one_iff, hvπ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num

private def π : v.adicCompletion F := (exists_small F v).choose
private theorem π_ne : π F v ≠ 0 := (exists_small F v).choose_spec.1
private theorem π_lt : ‖π F v‖ < 1 := (exists_small F v).choose_spec.2

private def aAd : AdeleRing (𝓞 F) F := (1, AdelicDock.splice (𝓞 F) F v 1 (π F v))
private def aInv : AdeleRing (𝓞 F) F := (1, AdelicDock.splice (𝓞 F) F v 1 (π F v)⁻¹)

private theorem aAd_snd_self : (aAd F v).2 v = π F v := AdelicDock.splice_apply_self _ _ _ _ _

private theorem aAd_snd_of_ne {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) : (aAd F v).2 u = 1 := by
  change AdelicDock.splice (𝓞 F) F v 1 (π F v) u = 1
  rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu]; rfl

private theorem aInv_snd_self : (aInv F v).2 v = (π F v)⁻¹ := AdelicDock.splice_apply_self _ _ _ _ _

private theorem aInv_snd_of_ne {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) : (aInv F v).2 u = 1 := by
  change AdelicDock.splice (𝓞 F) F v 1 (π F v)⁻¹ u = 1
  rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu]; rfl

private theorem aAd_mul_aInv : aAd F v * aInv F v = 1 := by
  refine Prod.ext (by change (1 : InfiniteAdeleRing F) * 1 = 1; rw [mul_one])
    (RestrictedProduct.ext _ _ fun u => ?_)
  change (aAd F v).2 u * (aInv F v).2 u = 1
  by_cases hu : u = v
  · subst hu; rw [aAd_snd_self, aInv_snd_self, mul_inv_cancel₀ (π_ne F u)]
  · rw [aAd_snd_of_ne F v hu, aInv_snd_of_ne F v hu, mul_one]

private def aU : (AdeleRing (𝓞 F) F)ˣ := ⟨aAd F v, aInv F v, aAd_mul_aInv F v, by rw [mul_comm]; exact aAd_mul_aInv F v⟩

private theorem distribHaarChar_aU : (distribHaarChar (AdeleRing (𝓞 F) F) (aU F v) : ℝ) = ‖π F v‖ := by
  have hT : ∀ y : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (y : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F →
        M4aS4.HasTransversal (y : FiniteAdeleRing (𝓞 F) F) :=
    fun y hy => ZhatModulus.hasTransversal F y hy
  rw [ZhatModulus.distribHaarChar_eq_placeModulus (F := F) hT (aU F v)]
  rw [PlaceModulus.placeModulus]
  change (∏ w : InfinitePlace F, ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult) *
    ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(aAd F v).2 u‖ = _
  rw [Finset.prod_eq_one fun w _ => by change ‖(1 : w.Completion)‖ ^ w.mult = 1; rw [norm_one, one_pow],
    one_mul]
  rw [finprod_eq_single _ v fun u hu => by rw [aAd_snd_of_ne F v hu, norm_one], aAd_snd_self]

private theorem smul_eq_self_of_mem {x : AdeleRing (𝓞 F) F} (hx : x.2 v = 0) :
    ((aU F v : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • x = x := by
  change aAd F v * x = x
  refine Prod.ext (by change (1 : InfiniteAdeleRing F) * x.1 = x.1; rw [one_mul])
    (RestrictedProduct.ext _ _ fun u => ?_)
  change (aAd F v).2 u * x.2 u = x.2 u
  by_cases hu : u = v
  · subst hu; rw [hx, mul_zero]
  · rw [aAd_snd_of_ne F v hu, one_mul]

private theorem smul_inter (C : Set (AdeleRing (𝓞 F) F)) :
    (aU F v) • ({x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ C) = {x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ((aU F v : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • x ∈ _
    rw [smul_eq_self_of_mem F v hx.1]; exact hx
  · intro hy
    exact ⟨y, hy, smul_eq_self_of_mem F v hy.1⟩

private theorem piece_null (C : Set (AdeleRing (𝓞 F) F)) (hfin : adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ C) ≠ ⊤) :
    adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ C) = 0 :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := NumberField.AdelicHaar.regular_adelicAddHaar F
  by
    have h := distribHaarChar_mul (adelicAddHaar (𝓞 F) F) (aU F v) ({x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ C)
    rw [smul_inter] at h
    by_contra hne
    have hδ : ((distribHaarChar (AdeleRing (𝓞 F) F) (aU F v) : NNReal) : ENNReal) = 1 := by
      have := (ENNReal.mul_left_inj hne hfin).mp (h.trans (one_mul _).symm)
      exact_mod_cast this
    have hδ' : (distribHaarChar (AdeleRing (𝓞 F) F) (aU F v) : ℝ) = 1 := by exact_mod_cast hδ
    rw [distribHaarChar_aU] at hδ'
    exact (π_lt F v).ne hδ'

theorem main : adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.2 v = 0} = 0 :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  by
    have hcov : {x : AdeleRing (𝓞 F) F | x.2 v = 0} = ⋃ n, ({x : AdeleRing (𝓞 F) F | x.2 v = 0} ∩ compactCovering (AdeleRing (𝓞 F) F) n) := by
      rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [hcov]
    refine measure_iUnion_null fun n => piece_null F v _ ?_
    exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (isCompact_compactCovering _ n).measure_lt_top).ne

end SndHyperplane

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar
open scoped NNReal

theorem NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod
    (n : Type) [Fintype n] [DecidableEq n]
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL n (InfiniteAdeleRing K))] [BorelSpace (GL n (InfiniteAdeleRing K))]
    [MeasurableSpace (GL n (FiniteAdeleRing (𝓞 K) K))] [BorelSpace (GL n (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL n (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL n (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (letI := glBorel n (𝓞 K) K
       Measure.map
           (fun x : GL n (AdeleRing (𝓞 K) K) =>
             (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x,
               Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x))
           (adelicGLHaar n (𝓞 K) K) = c • μa.prod μf) :=
  ProductMeasure.L1.main n K μa μf

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (c : w.Completion) :
    adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = c} = 0 :=
  FstHyperplane.main F w c

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.2 v = 0} = 0 :=
  SndHyperplane.main F v
