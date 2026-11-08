/-
  The centre-cut Siegel set as a cover modulo the centre.

  `centreCutSiegelSet K c u d₁ d₂` is the archimedean-height cut of the Siegel set with the finite
  part integral; `CoversModCentre K D` says every point of `GL₂(𝔸_K)` is, modulo the centre and a
  rational point, in `D`. This module is the cover's quantitative core:

  * `exists_coversModCentre_centreCutSiegelSetAmple`: for an *ample* centre-cut Siegel set (parameters
    `c`, `u` past the threshold) the finite union of its right translates by a class-representative
    set covers `GL₂(𝔸_K)` modulo the centre;
  * `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero`: with `u = 0` the same union does *not*
    cover — the threshold hypothesis is not vacuous;
  * `memLp_iUnion_centreCutSiegelSet_of_detWindow_le`: the union has finite measure against the
    determinant-window density, which is what makes the `L²` estimates over the cover converge;
  * `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat`: a nonnegative
    archimedean test factor with support inside a prescribed set, invariant under conjugation and
    *flat* (zero derivatives of order `1` and `2` at the identity) — the smoothing factor the covering
    argument convolves with.

  Transcribed from the pin's four `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  905 + 520 + 432 + 346 lines).

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple.lean
  spec-pin: Theorems/Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le.lean
  spec-pin: Theorems/Thm_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Covering
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSiegelSetAmple
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CentreCutEngine
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel MeasureTheory
open IsDedekindDomain Filter ComplexConjugate
open scoped ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace AutomorphicForm

/-! ## 520 — the ample cover

The pin's `S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple` prelude: the finite
integrality of rational translates, the archimedean unit balancing (Dirichlet), the archimedean
integer translation, and the per-place step computation. Transcribed at the pin's names and at the
pin's visibility (these twenty declarations are public in the pin file); statements unchanged. -/

namespace Ws1
namespace Cover

open NumberField.InfinitePlace NumberField.AdelicVolume NumberField.AdelicCentre
open AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

variable (F : Type) [Field F] [NumberField F]

theorem algebraMap_coe_mem_integralFiniteAdeles (r : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (r : F) ∈ integralFiniteAdeles (𝓞 F) F := by
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem glFin_globalPoints_mem_of_integral (γ : GL (Fin 2) F)
    (h : ∀ i j, ∃ r : 𝓞 F, (γ : Matrix (Fin 2) (Fin 2) F) i j = r)
    (h' : ∀ i j, ∃ r : 𝓞 F, ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = r) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [glFin_globalPoints_apply]
    obtain ⟨r, hr⟩ := h i j
    rw [hr]
    exact algebraMap_coe_mem_integralFiniteAdeles F r
  · intro i j
    rw [← map_inv, ← map_inv, glFin_globalPoints_apply]
    obtain ⟨r, hr⟩ := h' i j
    rw [hr]
    exact algebraMap_coe_mem_integralFiniteAdeles F r

def unitF (ε : (𝓞 F)ˣ) : Fˣ := Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) ε

omit [NumberField F] in
theorem unitF_val (ε : (𝓞 F)ˣ) : ((unitF F ε : Fˣ) : F) = ((ε : 𝓞 F) : F) := rfl

theorem glFin_globalPoints_diagOne_mem (ε : (𝓞 F)ˣ) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (diagOne (unitF F ε))) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine glFin_globalPoints_mem_of_integral F _ (fun i j => ?_) (fun i j => ?_)
  · rw [diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · exact ⟨ε, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rw [← map_inv, diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · exact ⟨((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), by simp [unitF]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem glFin_globalPoints_unipotentGL2_mem (β : 𝓞 F) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (unipotentGL2 (β : F))) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine glFin_globalPoints_mem_of_integral F _ (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨β, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · have hinv : ((unipotentGL2 (β : F))⁻¹ : GL (Fin 2) F) = unipotentGL2 (-(β : F)) := by
      rw [inv_eq_iff_mul_eq_one, ← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
    rw [hinv, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨-β, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

def archIdele (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (fun w => (a w : w.Completion), 1)
  inv := (fun w => ((a w)⁻¹ : (w.Completion)ˣ), 1)
  val_inv := Prod.ext (funext fun w => (a w).mul_inv) (one_mul 1)
  inv_val := Prod.ext (funext fun w => (a w).inv_mul) (one_mul 1)

theorem glFin_centralScalar_archIdele (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [centralScalar_apply_ne _ h, Matrix.one_apply_ne h]
    rfl

theorem archComponent_centralScalar_archIdele (w : InfinitePlace F)
    (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) :
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (a w : w.Completion)) ∧
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0) ∧
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) ∧
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (a w : w.Completion)) := by
  simp only [archComponent_apply, glArch_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [centralScalar_apply_eq]; rfl
  · rw [centralScalar_apply_ne _ (by decide)]; rfl
  · rw [centralScalar_apply_ne _ (by decide)]; rfl
  · rw [centralScalar_apply_eq]; rfl

omit [NumberField F] in
open NumberField.InfinitePlace.Completion in
theorem norm_ringEquivRealOfIsReal' {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖ringEquivRealOfIsReal hw x‖ = ‖x‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x

omit [NumberField F] in
open NumberField.InfinitePlace.Completion in
theorem norm_ringEquivComplexOfIsComplex' {w : InfinitePlace F} (hw : w.IsComplex)
    (x : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

open NumberField.InfinitePlace.Completion in
open scoped Classical in

noncomputable def ofRealAt (w : InfinitePlace F) : ℝ →+* w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm.toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm.toRingHom).comp Complex.ofRealHom

omit [NumberField F] in
open NumberField.InfinitePlace.Completion in
theorem norm_ofRealAt (w : InfinitePlace F) (t : ℝ) : ‖ofRealAt F w t‖ = |t| := by
  classical
  unfold ofRealAt
  split_ifs with hw
  · have h := norm_ringEquivRealOfIsReal' F hw ((ringEquivRealOfIsReal hw).symm t)
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs] at h
    show ‖(ringEquivRealOfIsReal hw).symm t‖ = |t|
    exact h.symm
  · have h := norm_ringEquivComplexOfIsComplex' F (not_isReal_iff_isComplex.mp hw)
      ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (t : ℂ))
    rw [RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs] at h
    show ‖(ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (t : ℂ)‖ = |t|
    exact h.symm

omit [NumberField F] in
theorem step_place (w : InfinitePlace F) (S U Z : GL (Fin 2) w.Completion) (a b z : w.Completion)
    (ha : a ≠ 0) (hz : z ≠ 0)
    (hU00 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = a)
    (hU01 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = b)
    (hU10 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0)
    (hU11 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = 1)
    (hZ00 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = z)
    (hZ01 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0)
    (hZ10 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0)
    (hZ11 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = z) :
    localHeight (Z * (U * S)) = ‖a‖ * localHeight S ∧
    ‖((Z * (U * S) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ =
      ‖z‖ ^ 2 * ‖a‖ * ‖(S : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ∧
    xWindowSq (Z * (U * S)) =
      ‖InfinitePlace.Completion.extensionEmbedding w a *
          xCoord (((S : Matrix (Fin 2) (Fin 2) w.Completion)).map (InfinitePlace.Completion.extensionEmbedding w)) +
        InfinitePlace.Completion.extensionEmbedding w b‖ ^ 2 := by
  set φ := InfinitePlace.Completion.extensionEmbedding w with hφ
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := norm_extensionEmbedding w
  have ha0 : a ≠ 0 := ha
  refine ⟨?_, ?_, ?_⟩
  · rw [localHeight_scalar_entries_mul hz hZ00 hZ01 hZ10 hZ11,
      localHeight_upper_entries_mul one_ne_zero hU00 hU10 hU11, norm_one, div_one]
  · rw [det_upper_entries_mul hZ00 hZ10 hZ11, det_upper_entries_mul hU00 hU10 hU11, norm_mul, norm_mul,
      norm_mul, norm_mul, norm_one, mul_one, sq]
    ring
  · rw [xWindowSq_scalar_entries_mul hz hZ00 hZ01 hZ10 hZ11, xWindowSq_eq_norm_xCoord_map_sq φ hφn,
      ← coe_map φ (U * S), map_mul]
    have h := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ U) (g := Matrix.GeneralLinearGroup.map φ S)
      (a := φ a) (b := φ b) (t := 1) one_ne_zero
      (by rw [coe_map, Matrix.map_apply, hU00]) (by rw [coe_map, Matrix.map_apply, hU01])
      (by rw [coe_map, Matrix.map_apply, hU10, map_zero]) (by rw [coe_map, Matrix.map_apply, hU11, map_one])
    rw [h, coe_map, div_one, div_one]

open NumberField.Units NumberField.Units.dirichletUnitTheorem in

theorem exists_unit_log_balance (K : Type) [Field K] [NumberField K] :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ t : InfinitePlace K → ℝ, ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |t w + Real.log (w ((ε : 𝓞 K) : K)) -
        (∑ w' : InfinitePlace K, (w'.mult : ℝ) * t w') / (∑ w' : InfinitePlace K, (w'.mult : ℝ))| ≤ ρ := by
  classical

  let b : Module.Basis (Fin (rank K)) ℝ (logSpace K) := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR'' : ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R' := fun y hy => (hR y hy).trans (le_max_left _ _)
  set N : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  refine ⟨N * R', mul_nonneg (by linarith) hR'0, fun t => ?_⟩

  set M : ℝ := ∑ w' : InfinitePlace K, (w'.mult : ℝ) with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Finset.sum_pos (fun w _ => by exact_mod_cast (mult_pos (w := w))) Finset.univ_nonempty
  set s : ℝ := (∑ w' : InfinitePlace K, (w'.mult : ℝ) * t w') / M with hs
  set d : InfinitePlace K → ℝ := fun w => t w - s with hd
  have hdsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * d w = 0 := by
    simp only [hd, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hs, ← hM, mul_div_cancel₀ _ hM0.ne', sub_self]

  set x : logSpace K := fun w => (w.1.mult : ℝ) * d w.1 with hx
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  have hvL : (v : logSpace K) ∈ unitLattice K := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K) (basisUnitLattice K)]
    exact v.2
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp hvL
  set u : (𝓞 K)ˣ := Additive.toMul y with hu
  have hyu : logEmbedding K (Additive.ofMul u) = (v : logSpace K) := by rw [hu, ofMul_toMul]; exact hy
  have hnorm : ‖(v : logSpace K) + x‖ ≤ R' := hR'' _ hv

  have hoff : ∀ w : InfinitePlace K, w ≠ w₀ → |(w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) + (w.mult : ℝ) * d w| ≤ R' := by
    intro w hw
    have h := (norm_le_pi_norm ((v : logSpace K) + x) ⟨w, hw⟩).trans hnorm
    rw [Pi.add_apply, Real.norm_eq_abs, ← hyu, logEmbedding_component] at h
    exact h

  have hprod : ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) = 0 := sum_mult_mul_log u
  have hall : ∑ w : InfinitePlace K, ((w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) + (w.mult : ℝ) * d w) = 0 := by
    rw [Finset.sum_add_distrib, hprod, hdsum, add_zero]
  have hw₀ : |((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ ((u : 𝓞 K) : K)) + ((w₀ : InfinitePlace K).mult : ℝ) * d w₀|
      ≤ N * R' := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hall
    rw [hall, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : {w : InfinitePlace K // w ≠ w₀}, |(w.1.mult : ℝ) * Real.log (w.1 ((u : 𝓞 K) : K)) + (w.1.mult : ℝ) * d w.1|
        ≤ ∑ _w : {w : InfinitePlace K // w ≠ w₀}, R' := Finset.sum_le_sum fun w _ => hoff w.1 w.2
      _ ≤ N * R' := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hN]
          refine mul_le_mul_of_nonneg_right ?_ hR'0
          exact_mod_cast Fintype.card_subtype_le _

  have hcoord : ∀ w : InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K)) + d w| ≤ N * R' := by
    intro w
    have hm1 : (1 : ℝ) ≤ w.mult := by exact_mod_cast (mult_pos (w := w))
    have hm0 : (0 : ℝ) < w.mult := lt_of_lt_of_le one_pos hm1
    have key : |(w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) + (w.mult : ℝ) * d w| ≤ N * R' := by
      by_cases hw : w = w₀
      · subst hw
        exact hw₀
      · exact (hoff w hw).trans (le_mul_of_one_le_left hR'0 hN1)
    rw [← mul_add, abs_mul, abs_of_pos hm0] at key
    calc |Real.log (w ((u : 𝓞 K) : K)) + d w| = 1 * |Real.log (w ((u : 𝓞 K) : K)) + d w| := (one_mul _).symm
      _ ≤ (w.mult : ℝ) * |Real.log (w ((u : 𝓞 K) : K)) + d w| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
      _ ≤ N * R' := key

  refine ⟨u, fun w => ?_⟩
  have h := hcoord w
  rw [hd] at h
  dsimp only at h
  rw [show t w + Real.log (w ((u : 𝓞 K) : K)) - s = Real.log (w ((u : 𝓞 K) : K)) + (t w - s) by ring]
  exact h

section L3
open NumberField.mixedEmbedding

open scoped Classical in

theorem exists_int_translate_le :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : InfinitePlace F → ℂ, (∀ w : InfinitePlace F, w.IsReal → (y w).im = 0) →
      ∃ β : 𝓞 F, ∀ w : InfinitePlace F, ‖y w + (w.embedding : F →+* ℂ) (β : F)‖ ≤ R := by
  classical
  set b := mixedEmbedding.latticeBasis F with hb
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩

  set x : mixedSpace F := (fun w => (y w.1).re, fun w => y w.1) with hx
  have hmem : ((ZSpan.floor b x : Submodule.span ℤ (Set.range b)) : mixedSpace F) ∈ mixedEmbedding.integerLattice F :=
    (mixedEmbedding.mem_span_latticeBasis F).mp (ZSpan.floor b x).2
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : 𝓞 F, mixedEmbedding F (β₀ : F) = (ZSpan.floor b x : mixedSpace F) :=
    Set.mem_range.mp hmem
  have hfr : ‖x - mixedEmbedding F (β₀ : F)‖ ≤ R := by
    rw [hβ₀, ← ZSpan.fract_apply]
    exact hR _ (ZSpan.fract_mem_fundamentalDomain b x)
  refine ⟨-β₀, fun w => ?_⟩
  have hneg : (w.embedding : F →+* ℂ) (((-β₀ : 𝓞 F) : F)) = -(w.embedding (β₀ : F)) := by
    push_cast
    exact map_neg _ _
  rw [hneg, ← sub_eq_add_neg]
  refine le_trans ?_ (le_trans hfr (le_max_left _ _))
  by_cases hw : w.IsReal
  ·
    have h1 : ‖(x - mixedEmbedding F (β₀ : F)).1 ⟨w, hw⟩‖ ≤ ‖x - mixedEmbedding F (β₀ : F)‖ :=
      (norm_le_pi_norm _ _).trans (le_max_left _ _)
    refine le_trans (le_of_eq ?_) h1
    rw [Prod.fst_sub, Pi.sub_apply, mixedEmbedding_apply_isReal]
    have hyw : y w = ((y w).re : ℂ) := by
      apply Complex.ext <;> simp [hy w hw]
    have hemb : w.embedding (β₀ : F) = ((embedding_of_isReal hw (β₀ : F) : ℝ) : ℂ) :=
      (embedding_of_isReal_apply hw _).symm
    rw [hyw, hemb, ← Complex.ofReal_sub, Complex.norm_real]
  ·
    have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have h1 : ‖(x - mixedEmbedding F (β₀ : F)).2 ⟨w, hw'⟩‖ ≤ ‖x - mixedEmbedding F (β₀ : F)‖ :=
      (norm_le_pi_norm _ _).trans (le_max_right _ _)
    refine le_trans (le_of_eq ?_) h1
    rw [Prod.snd_sub, Pi.sub_apply, mixedEmbedding_apply_isComplex]

end L3

open ComplexConjugate

omit [NumberField F] in
theorem im_extensionEmbedding_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    (InfinitePlace.Completion.extensionEmbedding w x).im = 0 := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x, Complex.ofReal_im]

omit [NumberField F] in
theorem im_xCoord_eq_zero (M : Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ i j, (M i j).im = 0) :
    (xCoord M).im = 0 := by
  unfold xCoord
  rw [Complex.div_ofReal_im]
  have hnum : (M 0 0 * conj (M 1 0) + M 0 1 * conj (M 1 1)).im = 0 := by
    simp [Complex.add_im, Complex.mul_im, Complex.conj_im, Complex.conj_re, h]
  rw [hnum, zero_div]

omit [NumberField F] in
theorem redElt_coe (ε : (𝓞 F)ˣ) (β : 𝓞 F) :
    ((unipotentGL2 ((β : F)) * diagOne (unitF F ε) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((ε : 𝓞 F) : F), (β : F); 0, 1] := by
  rw [Units.val_mul, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, diagOne_coe_apply, Matrix.diagonal, unitF_val]

end Cover
end Ws1

/-! ## 905 — the flat, conjugation-invariant archimedean test factor

The pin's `S_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat`
construction: the bump `cut` on the mixed archimedean coordinates, the distance to the identity
`S`, its inversion symmetry, the determinant weight `Nrm` with the flatness exponent `-σ`, and the
compactness of the sublevel tube. Transcribed at the pin's names and at the pin's visibility (the
pin's `BumpAux` is entirely public); statements unchanged. -/

namespace BumpAux

open NumberField.InfinitePlace
open scoped Matrix Classical

noncomputable def cut (ε t : ℝ) : ℝ := Real.smoothTransition (2 - 2 * t / ε)

theorem cut_nonneg (ε t : ℝ) : 0 ≤ cut ε t := Real.smoothTransition.nonneg _

theorem cut_le_one (ε t : ℝ) : cut ε t ≤ 1 := Real.smoothTransition.le_one _

theorem cut_zero {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) : cut ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 * t / ε ≥ 2 := by rw [ge_iff_le, le_div_iff₀ hε]; linarith
  linarith

theorem cut_at_zero (ε : ℝ) : cut ε 0 = 1 := by
  simp only [cut, mul_zero, zero_div, sub_zero]
  exact Real.smoothTransition.one_of_one_le (by norm_num)

theorem contDiff_cut (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cut ε) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 2 - 2 * t / ε) := by
    have : (fun t : ℝ => 2 - 2 * t / ε) = fun t => 2 + (-(2 / ε)) * t := by
      funext t; ring
    rw [this]
    exact contDiff_const.add (contDiff_const.mul contDiff_id)
  exact Real.smoothTransition.contDiff.comp h

theorem contDiff_of_contDiffOn_of_eventuallyEq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (h0 : ∀ x ∉ U, f =ᶠ[nhds x] 0) : ContDiff ℝ (⊤ : ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq (h0 x hx)

section HS

variable {𝕜 : Type*} [RCLike 𝕜]

def hs (N : Matrix (Fin 2) (Fin 2) 𝕜) : ℝ := ∑ i, ∑ j, ‖N i j‖ ^ 2

theorem hs_nonneg (N : Matrix (Fin 2) (Fin 2) 𝕜) : 0 ≤ hs N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem norm_sq_le_hs (N : Matrix (Fin 2) (Fin 2) 𝕜) (i j : Fin 2) : ‖N i j‖ ^ 2 ≤ hs N := by
  unfold hs
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖N i j‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖N i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem hs_eq_re_trace (N : Matrix (Fin 2) (Fin 2) 𝕜) :
    hs N = RCLike.re (Matrix.trace (N * Nᴴ)) := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    RCLike.star_def, RCLike.mul_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  norm_cast

theorem hs_conj_of_mul_conjTranspose_eq_one (U N : Matrix (Fin 2) (Fin 2) 𝕜) (hU : U * Uᴴ = 1) :
    hs (U * N * Uᴴ) = hs N := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [hs_eq_re_trace, hs_eq_re_trace]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have : U * N * Uᴴ * (U * (Nᴴ * Uᴴ)) = U * (N * Nᴴ) * Uᴴ := by
    calc U * N * Uᴴ * (U * (Nᴴ * Uᴴ)) = U * N * (Uᴴ * U) * (Nᴴ * Uᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = U * (N * Nᴴ) * Uᴴ := by rw [hU']; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_cycle, hU', Matrix.one_mul]

theorem mul_conjTranspose_eq_one_of_rowIsometry (k : Matrix (Fin 2) (Fin 2) 𝕜)
    (hk : ∀ x y : 𝕜, ‖x * k 0 0 + y * k 1 0‖ ^ 2 + ‖x * k 0 1 + y * k 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2) :
    k * kᴴ = 1 := by

  have e : ∀ x y : 𝕜,
      (x * k 0 0 + y * k 1 0) * conj (x * k 0 0 + y * k 1 0) +
        (x * k 0 1 + y * k 1 1) * conj (x * k 0 1 + y * k 1 1) = x * conj x + y * conj y := by
    intro x y
    have h := hk x y
    simp only [RCLike.mul_conj]
    exact_mod_cast congrArg (fun r : ℝ => (r : 𝕜)) h

  set a := k 0 0; set b := k 0 1; set c := k 1 0; set d := k 1 1
  have h00 : a * conj a + b * conj b = 1 := by
    have := e 1 0; simpa using this
  have h11 : c * conj c + d * conj d = 1 := by
    have := e 0 1; simpa using this

  set s := a * conj c + b * conj d with hs_def
  have hre : s + conj s = 0 := by
    have h := e 1 1
    simp only [one_mul, map_add, map_one, mul_one] at h

    have : (a + c) * (conj a + conj c) + (b + d) * (conj b + conj d)
        = (a * conj a + b * conj b) + (c * conj c + d * conj d) + (s + conj s) := by
      simp only [hs_def, map_add, map_mul, RCLike.conj_conj]; ring
    rw [this, h00, h11] at h

    have h2 : (1 : 𝕜) + 1 + (s + conj s) = 1 + 1 := by simpa using h
    exact add_left_cancel (a := (1 : 𝕜) + 1) (by rw [h2, add_zero])
  have him : RCLike.I * (conj s - s) = 0 := by
    have h := e 1 RCLike.I
    simp only [one_mul, map_add, map_one, map_mul, RCLike.conj_I, mul_one] at h
    have : (a + RCLike.I * c) * (conj a + -RCLike.I * conj c)
        + (b + RCLike.I * d) * (conj b + -RCLike.I * conj d)
        = (a * conj a + b * conj b) + (-(RCLike.I * RCLike.I)) * (c * conj c + d * conj d)
          + RCLike.I * (conj s - s) := by
      simp only [hs_def, map_add, map_mul, RCLike.conj_conj]; ring
    rw [this, h00, h11, mul_one] at h

    have h' : (1 : 𝕜) + -(RCLike.I * RCLike.I) + RCLike.I * (conj s - s) = 1 + -(RCLike.I * RCLike.I) := by
      rw [h]; ring
    exact add_left_cancel (a := (1 : 𝕜) + -(RCLike.I * RCLike.I)) (by rw [h', add_zero])
  have hs0 : s = 0 := by
    apply RCLike.ext
    · have := congrArg RCLike.re hre
      simp only [map_add, RCLike.conj_re, map_zero] at this
      simp only [map_zero]; linarith
    · have h2 := congrArg RCLike.re him
      rw [RCLike.mul_re, RCLike.I_re, zero_mul, zero_sub, map_zero, neg_eq_zero] at h2

      have h3 : RCLike.im (conj s - s) = 0 := by
        have hI := RCLike.I_im (conj s - s)
        rw [← hI, mul_comm]
        exact h2
      rw [map_sub, RCLike.conj_im] at h3
      simp only [map_zero]
      linarith
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, RCLike.star_def] using h00
  · show ∑ l, k 0 l * star (k 1 l) = 0
    simpa [Fin.sum_univ_two, RCLike.star_def, hs_def] using hs0
  · show ∑ l, k 1 l * star (k 0 l) = 0
    have : conj s = 0 := by rw [hs0, map_zero]
    simpa [Fin.sum_univ_two, RCLike.star_def, hs_def, map_add, map_mul, mul_comm] using this
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, RCLike.star_def] using h11

theorem det_ne_zero_of_hs_sub_one_lt (P : Matrix (Fin 2) (Fin 2) 𝕜) (hP : hs (P - 1) < 1 / 16) :
    P.det ≠ 0 := by
  have hb : ∀ i j, ‖(P - 1) i j‖ < 1 / 4 := by
    intro i j
    have h := (norm_sq_le_hs (P - 1) i j).trans_lt hP
    have h0 : 0 ≤ ‖(P - 1) i j‖ := norm_nonneg _
    nlinarith
  have e00 : P 0 0 = 1 + (P - 1) 0 0 := by simp
  have e11 : P 1 1 = 1 + (P - 1) 1 1 := by simp
  have e01 : P 0 1 = (P - 1) 0 1 := by simp
  have e10 : P 1 0 = (P - 1) 1 0 := by simp
  rw [Matrix.det_fin_two, e00, e11, e01, e10]
  set a := (P - 1) 0 0; set b := (P - 1) 0 1; set c := (P - 1) 1 0; set d := (P - 1) 1 1
  have ha := hb 0 0; have hb' := hb 0 1; have hc := hb 1 0; have hd := hb 1 1
  intro h

  have h1 : (1 : 𝕜) = -(a + d + a * d) + b * c := by linear_combination h
  have := congrArg (fun z : 𝕜 => ‖z‖) h1
  simp only [norm_one] at this
  have hle : ‖-(a + d + a * d) + b * c‖ ≤ ‖a‖ + ‖d‖ + ‖a‖ * ‖d‖ + ‖b‖ * ‖c‖ := by
    calc ‖-(a + d + a * d) + b * c‖ ≤ ‖-(a + d + a * d)‖ + ‖b * c‖ := norm_add_le _ _
      _ ≤ (‖a‖ + ‖d‖ + ‖a‖ * ‖d‖) + ‖b‖ * ‖c‖ := by
        gcongr
        · rw [norm_neg]
          calc ‖a + d + a * d‖ ≤ ‖a + d‖ + ‖a * d‖ := norm_add_le _ _
            _ ≤ ‖a‖ + ‖d‖ + ‖a‖ * ‖d‖ := by gcongr; exacts [norm_add_le _ _, norm_mul_le _ _]
        · exact norm_mul_le _ _
  have hn : 0 ≤ ‖a‖ := norm_nonneg _
  have hn' : 0 ≤ ‖b‖ := norm_nonneg _
  nlinarith

end HS


variable (K : Type*) [Field K] [NumberField K]

abbrev ES : Type _ := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

def blkR (v : {w : InfinitePlace K // w.IsReal}) (m : ES K) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (m i j).1 v

def blkC (v : {w : InfinitePlace K // w.IsComplex}) (m : ES K) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (m i j).2 v

theorem contDiff_blkR (v : {w : InfinitePlace K // w.IsReal}) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => blkR K v m i j := by
  unfold blkR
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => m i j := contDiff_apply_apply ℝ _ i j
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => (m i j).1 := contDiff_fst.comp h1
  exact (contDiff_apply ℝ ℝ v).comp h2

theorem contDiff_blkC (v : {w : InfinitePlace K // w.IsComplex}) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => blkC K v m i j := by
  unfold blkC
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => m i j := contDiff_apply_apply ℝ _ i j
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => (m i j).2 := contDiff_snd.comp h1
  exact (contDiff_apply ℝ ℂ v).comp h2

noncomputable def S (m : ES K) : ℝ :=
  (∑ v, hs (blkR K v m - 1)) + ∑ v, hs (blkC K v m - 1)

theorem S_nonneg (m : ES K) : 0 ≤ S K m :=
  add_nonneg (Finset.sum_nonneg fun _ _ => hs_nonneg _) (Finset.sum_nonneg fun _ _ => hs_nonneg _)

theorem hsR_le_S (m : ES K) (v : {w : InfinitePlace K // w.IsReal}) :
    hs (blkR K v m - 1) ≤ S K m :=
  le_add_of_le_of_nonneg (Finset.single_le_sum (f := fun v => hs (blkR K v m - 1))
    (fun _ _ => hs_nonneg _) (Finset.mem_univ v)) (Finset.sum_nonneg fun _ _ => hs_nonneg _)

theorem hsC_le_S (m : ES K) (v : {w : InfinitePlace K // w.IsComplex}) :
    hs (blkC K v m - 1) ≤ S K m :=
  le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => hs_nonneg _)
    (Finset.single_le_sum (f := fun v => hs (blkC K v m - 1)) (fun _ _ => hs_nonneg _) (Finset.mem_univ v))

theorem contDiff_S : ContDiff ℝ (⊤ : ℕ∞) (S K) := by
  unfold S hs
  apply ContDiff.add
  · refine ContDiff.sum fun v _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    have h : ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => blkR K v m i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j :=
      (contDiff_blkR K v i j).sub contDiff_const
    exact (contDiff_norm_sq ℝ (E := ℝ)).comp h
  · refine ContDiff.sum fun v _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    have h : ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => blkC K v m i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j :=
      (contDiff_blkC K v i j).sub contDiff_const
    exact (contDiff_norm_sq ℝ (E := ℂ)).comp h

theorem continuous_S : Continuous (S K) := (contDiff_S K).continuous

noncomputable def INV (m : ES K) : ES K :=
  fun i j => (fun v => (blkR K v m)⁻¹ i j, fun v => (blkC K v m)⁻¹ i j)

omit [NumberField K] in
@[scoped simp] theorem blkR_INV (v : {w : InfinitePlace K // w.IsReal}) (m : ES K) :
    blkR K v (INV K m) = (blkR K v m)⁻¹ := rfl

omit [NumberField K] in
@[scoped simp] theorem blkC_INV (v : {w : InfinitePlace K // w.IsComplex}) (m : ES K) :
    blkC K v (INV K m) = (blkC K v m)⁻¹ := rfl

def U : Set (ES K) := {m | (∀ v, (blkR K v m).det ≠ 0) ∧ ∀ v, (blkC K v m).det ≠ 0}

theorem contDiff_detR (v : {w : InfinitePlace K // w.IsReal}) :
    ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => (blkR K v m).det := by
  simp only [Matrix.det_fin_two]
  exact ((contDiff_blkR K v 0 0).mul (contDiff_blkR K v 1 1)).sub
    ((contDiff_blkR K v 0 1).mul (contDiff_blkR K v 1 0))

theorem contDiff_detC (v : {w : InfinitePlace K // w.IsComplex}) :
    ContDiff ℝ (⊤ : ℕ∞) fun m : ES K => (blkC K v m).det := by
  simp only [Matrix.det_fin_two]
  exact ((contDiff_blkC K v 0 0).mul (contDiff_blkC K v 1 1)).sub
    ((contDiff_blkC K v 0 1).mul (contDiff_blkC K v 1 0))

theorem isOpen_U : IsOpen (U K) := by
  have h : U K = (⋂ v, (fun m : ES K => (blkR K v m).det) ⁻¹' {0}ᶜ) ∩
      ⋂ v, (fun m : ES K => (blkC K v m).det) ⁻¹' {0}ᶜ := by
    ext m; simp [U]
  rw [h]
  exact (isOpen_iInter_of_finite fun v => isOpen_compl_singleton.preimage (contDiff_detR K v).continuous).inter
    (isOpen_iInter_of_finite fun v => isOpen_compl_singleton.preimage (contDiff_detC K v).continuous)

theorem S_ge_of_not_mem_U {m : ES K} (hm : m ∉ U K) : 1 / 16 ≤ S K m := by
  simp only [U, Set.mem_ofPred_eq, not_and_or, not_forall, not_not] at hm
  rcases hm with ⟨v, hv⟩ | ⟨v, hv⟩
  · by_contra h
    push Not at h
    exact det_ne_zero_of_hs_sub_one_lt _ ((hsR_le_S K m v).trans_lt h) hv
  · by_contra h
    push Not at h
    exact det_ne_zero_of_hs_sub_one_lt _ ((hsC_le_S K m v).trans_lt h) hv

theorem mem_U_of_S_lt {m : ES K} (h : S K m < 1 / 16) : m ∈ U K := by
  by_contra hm
  exact absurd (S_ge_of_not_mem_U K hm) (not_le.mpr h)

theorem contDiffOn_invR (v : {w : InfinitePlace K // w.IsReal}) (i j : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun m : ES K => (blkR K v m)⁻¹ i j) (U K) := by
  intro m hm
  have hdet : (blkR K v m).det ≠ 0 := hm.1 v
  have heq : ∀ m' : ES K, (blkR K v m')⁻¹ i j = ((blkR K v m').det)⁻¹ * (blkR K v m').adjugate i j := by
    intro m'
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp_rw [heq]
  refine ContDiffWithinAt.mul ?_ ?_
  · exact (((contDiff_detR K v).contDiffAt).inv hdet).contDiffWithinAt
  · apply ContDiffAt.contDiffWithinAt
    apply ContDiff.contDiffAt
    simp only [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      first | exact contDiff_blkR K v _ _ | exact (contDiff_blkR K v _ _).neg

theorem contDiffOn_invC (v : {w : InfinitePlace K // w.IsComplex}) (i j : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun m : ES K => (blkC K v m)⁻¹ i j) (U K) := by
  intro m hm
  have hdet : (blkC K v m).det ≠ 0 := hm.2 v
  have heq : ∀ m' : ES K, (blkC K v m')⁻¹ i j = ((blkC K v m').det)⁻¹ * (blkC K v m').adjugate i j := by
    intro m'
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp_rw [heq]
  refine ContDiffWithinAt.mul ?_ ?_
  · exact (((contDiff_detC K v).contDiffAt).inv hdet).contDiffWithinAt
  · apply ContDiffAt.contDiffWithinAt
    apply ContDiff.contDiffAt
    simp only [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      first | exact contDiff_blkC K v _ _ | exact (contDiff_blkC K v _ _).neg

theorem contDiffOn_S_INV : ContDiffOn ℝ (⊤ : ℕ∞) (fun m => S K (INV K m)) (U K) := by
  unfold S hs
  apply ContDiffOn.add
  · refine ContDiffOn.sum fun v _ => ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    have h : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun m : ES K => blkR K v (INV K m) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (U K) := by
      simp only [blkR_INV]
      exact (contDiffOn_invR K v i j).sub contDiffOn_const
    exact (contDiff_norm_sq ℝ (E := ℝ)).comp_contDiffOn h
  · refine ContDiffOn.sum fun v _ => ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    have h : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun m : ES K => blkC K v (INV K m) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) (U K) := by
      simp only [blkC_INV]
      exact (contDiffOn_invC K v i j).sub contDiffOn_const
    exact (contDiff_norm_sq ℝ (E := ℂ)).comp_contDiffOn h

noncomputable def Nrm (m : ES K) : ℝ := (∏ v, |(blkR K v m).det|) * ∏ v, ‖(blkC K v m).det‖ ^ 2

theorem Nrm_pos {m : ES K} (hm : m ∈ U K) : 0 < Nrm K m :=
  mul_pos (Finset.prod_pos fun v _ => abs_pos.mpr (hm.1 v))
    (Finset.prod_pos fun v _ => by have := hm.2 v; positivity)

theorem contDiffOn_Nrm : ContDiffOn ℝ (⊤ : ℕ∞) (Nrm K) (U K) := by
  intro m hm
  unfold Nrm
  refine ContDiffWithinAt.mul ?_ ?_
  · refine contDiffWithinAt_prod (fun v _ => ?_)
    exact ((contDiffAt_abs (hm.1 v)).comp m (contDiff_detR K v).contDiffAt).contDiffWithinAt
  · refine contDiffWithinAt_prod (fun v _ => ?_)
    exact ((contDiff_norm_sq ℝ (E := ℂ)).comp (contDiff_detC K v)).contDiffAt.contDiffWithinAt

theorem contDiffOn_Nrm_rpow (p : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun m => Nrm K m ^ p) (U K) := by
  intro m hm
  exact (contDiffOn_Nrm K m hm).rpow_const_of_ne (Nrm_pos K hm).ne'

noncomputable def Φ (ε σ : ℝ) (m : ES K) : ℝ :=
  cut ε (S K m + S K (INV K m)) * Nrm K m ^ (-σ / 2)

theorem Φ_nonneg (ε σ : ℝ) (m : ES K) : 0 ≤ Φ K ε σ m :=
  mul_nonneg (cut_nonneg _ _) (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    (Finset.prod_nonneg fun _ _ => by positivity)) _)

theorem Φ_eq_zero_of_le {ε σ : ℝ} (hε : 0 < ε) {m : ES K} (h : ε ≤ S K m) :
    Φ K ε σ m = 0 := by
  unfold Φ
  rw [cut_zero hε (h.trans (le_add_of_nonneg_right (S_nonneg K _))), zero_mul]

theorem contDiff_Φ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 16) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Φ K ε σ) := by
  refine contDiff_of_contDiffOn_of_eventuallyEq_zero (isOpen_U K) ?_ ?_
  · unfold Φ
    refine ContDiffOn.mul ?_ (contDiffOn_Nrm_rpow K _)
    exact (contDiff_cut ε).comp_contDiffOn ((contDiff_S K).contDiffOn.add (contDiffOn_S_INV K))
  · intro m hm
    have hS : 1 / 16 ≤ S K m := S_ge_of_not_mem_U K hm
    have hopen : IsOpen {m' : ES K | ε < S K m'} := isOpen_lt continuous_const (continuous_S K)
    have hmem : m ∈ {m' : ES K | ε < S K m'} := lt_of_lt_of_le hε' hS
    filter_upwards [hopen.mem_nhds hmem] with m' hm'
    exact Φ_eq_zero_of_le K hε (le_of_lt hm')

section Entries

variable (K : Type*) [Field K] [NumberField K]

local notation "Mat" => Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)
local notation "G∞" => GL (Fin 2) (InfiniteAdeleRing K)

noncomputable def Ent (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) : ES K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (g i j)

noncomputable def ρR (v : {w : InfinitePlace K // w.IsReal}) : InfiniteAdeleRing K →+* ℝ :=
  (Completion.extensionEmbeddingOfIsReal v.2).comp (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v.1)

noncomputable def ρC (v : {w : InfinitePlace K // w.IsComplex}) : InfiniteAdeleRing K →+* ℂ :=
  (Completion.extensionEmbedding v.1).comp (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v.1)

omit [NumberField K] in
theorem ρR_apply (v : {w : InfinitePlace K // w.IsReal}) (x : InfiniteAdeleRing K) :
    ρR K v x = Completion.extensionEmbeddingOfIsReal v.2 (x v.1) := rfl

omit [NumberField K] in
theorem ρC_apply (v : {w : InfinitePlace K // w.IsComplex}) (x : InfiniteAdeleRing K) :
    ρC K v x = Completion.extensionEmbedding v.1 (x v.1) := rfl

omit [NumberField K] in
theorem norm_ρR (v : {w : InfinitePlace K // w.IsReal}) (x : InfiniteAdeleRing K) :
    ‖ρR K v x‖ = ‖x v.1‖ :=
  (Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _) _

omit [NumberField K] in
theorem norm_ρC (v : {w : InfinitePlace K // w.IsComplex}) (x : InfiniteAdeleRing K) :
    ‖ρC K v x‖ = ‖x v.1‖ :=
  (Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _) _

omit [NumberField K] in
theorem blkR_Ent (v : {w : InfinitePlace K // w.IsReal})
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    blkR K v (Ent K g) = (ρR K v).mapMatrix g := by
  ext i j
  simp only [blkR, Ent, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, ρR_apply]

omit [NumberField K] in
theorem blkC_Ent (v : {w : InfinitePlace K // w.IsComplex})
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    blkC K v (Ent K g) = (ρC K v).mapMatrix g := by
  ext i j
  simp only [blkC, Ent, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, ρC_apply]

omit [NumberField K] in
theorem ES_ext {m n : ES K} (hR : ∀ v, blkR K v m = blkR K v n)
    (hC : ∀ v, blkC K v m = blkC K v n) : m = n := by
  funext i j
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact congrFun (congrFun (hR v) i) j
  · exact congrFun (congrFun (hC v) i) j

variable (g : GL (Fin 2) (InfiniteAdeleRing K))

omit [NumberField K] in
theorem blkR_Ent_inv (v : {w : InfinitePlace K // w.IsReal}) :
    blkR K v (Ent K ((g⁻¹ : G∞) : Mat)) = (blkR K v (Ent K (g : Mat)))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [blkR_Ent, blkR_Ent, ← map_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, map_one]

omit [NumberField K] in
theorem blkC_Ent_inv (v : {w : InfinitePlace K // w.IsComplex}) :
    blkC K v (Ent K ((g⁻¹ : G∞) : Mat)) = (blkC K v (Ent K (g : Mat)))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [blkC_Ent, blkC_Ent, ← map_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, map_one]

omit [NumberField K] in
theorem Ent_inv : Ent K ((g⁻¹ : G∞) : Mat) = INV K (Ent K (g : Mat)) :=
  ES_ext K (fun v => by rw [blkR_Ent_inv, blkR_INV]) (fun v => by rw [blkC_Ent_inv, blkC_INV])

omit [NumberField K] in
theorem detR_Ent (v : {w : InfinitePlace K // w.IsReal})
    (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (blkR K v (Ent K m)).det = ρR K v m.det := by
  rw [blkR_Ent, ← RingHom.map_det]

omit [NumberField K] in
theorem detC_Ent (v : {w : InfinitePlace K // w.IsComplex})
    (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (blkC K v (Ent K m)).det = ρC K v m.det := by
  rw [blkC_Ent, ← RingHom.map_det]

omit [NumberField K] in
theorem isUnit_det_apply (w : InfinitePlace K) :
    IsUnit (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w ((g : Mat).det)) := by
  have h : IsUnit (g : Mat).det := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
  exact h.map (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w)

omit [NumberField K] in
theorem Ent_mem_U : Ent K (g : Mat) ∈ U K := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [detR_Ent]
    exact ((isUnit_det_apply K g v.1).map (Completion.extensionEmbeddingOfIsReal v.2)).ne_zero
  · rw [detC_Ent]
    exact ((isUnit_det_apply K g v.1).map (Completion.extensionEmbedding v.1)).ne_zero

theorem Nrm_Ent_pos : 0 < Nrm K (Ent K (g : Mat)) := Nrm_pos K (Ent_mem_U K g)

theorem Nrm_Ent (m : Mat) :
    Nrm K (Ent K m) = ∏ w : InfinitePlace K, ‖m.det w‖ ^ w.mult := by
  have hR : (∏ v : {w : InfinitePlace K // w.IsReal}, |(blkR K v (Ent K m)).det|) =
      ∏ v : {w : InfinitePlace K // w.IsReal}, ‖m.det v.1‖ ^ (v.1).mult := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [detR_Ent, ← Real.norm_eq_abs, norm_ρR, InfinitePlace.mult, ite_eq_left v.2, pow_one]
  have hC : (∏ v : {w : InfinitePlace K // w.IsComplex}, ‖(blkC K v (Ent K m)).det‖ ^ 2) =
      ∏ v : {w : InfinitePlace K // ¬ w.IsReal}, ‖m.det v.1‖ ^ (v.1).mult := by
    symm
    refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex) _ _ fun v => ?_
    rw [detC_Ent, norm_ρC, Equiv.subtypeEquivRight_apply_coe, InfinitePlace.mult, ite_eq_right v.2]
  unfold Nrm
  rw [hR, hC, Fintype.prod_subtype_mul_prod_subtype (p := fun w : InfinitePlace K => w.IsReal)
    (f := fun w => ‖m.det w‖ ^ w.mult)]

theorem Nrm_Ent_inv : Nrm K (Ent K ((g⁻¹ : G∞) : Mat)) =
    (Nrm K (Ent K (g : Mat)))⁻¹ := by
  unfold Nrm
  simp only [blkR_Ent_inv, blkC_Ent_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv, norm_inv,
    inv_pow, Finset.prod_inv_distrib, mul_inv]

theorem Φ_Ent_flat (ε σ : ℝ) :
    Φ K ε σ (Ent K (g : Mat)) =
      Φ K ε σ (Ent K ((g⁻¹ : G∞) : Mat)) * Nrm K (Ent K (g : Mat)) ^ (-σ) := by
  have hN := Nrm_Ent_pos K g
  have h1 : INV K (Ent K ((g⁻¹ : G∞) : Mat)) = Ent K (g : Mat) := by
    rw [← Ent_inv, inv_inv]
  unfold Φ
  rw [← Ent_inv K g, h1, Nrm_Ent_inv, add_comm (S K (Ent K ((g⁻¹ : G∞) : Mat))), mul_assoc]
  congr 1
  rw [Real.inv_rpow hN.le, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
  congr 1
  ring

theorem S_Ent_one : S K (Ent K 1) = 0 := by
  unfold S
  simp only [blkR_Ent, blkC_Ent, map_one, sub_self]
  simp [hs]

theorem Nrm_Ent_one : Nrm K (Ent K 1) = 1 := by
  unfold Nrm
  simp only [detR_Ent, detC_Ent, Matrix.det_one, map_one, abs_one, norm_one, one_pow,
    Finset.prod_const_one, mul_one]

theorem Φ_Ent_one (ε σ : ℝ) : Φ K ε σ (Ent K 1) = 1 := by
  unfold Φ
  have h1 : INV K (Ent K 1) = Ent K 1 := by
    have := Ent_inv K 1
    rw [inv_one] at this
    exact this.symm
  rw [h1, S_Ent_one, add_zero, cut_at_zero, Nrm_Ent_one, Real.one_rpow, mul_one]

theorem S_Ent_conj (a : G∞)
    (haR : ∀ v, blkR K v (Ent K (a : Mat)) * (blkR K v (Ent K (a : Mat)))ᴴ = 1)
    (haC : ∀ v, blkC K v (Ent K (a : Mat)) * (blkC K v (Ent K (a : Mat)))ᴴ = 1)
    (x : G∞) :
    S K (Ent K ((a * x * a⁻¹ : G∞) : Mat)) = S K (Ent K (x : Mat)) := by
  unfold S
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    set A := blkR K v (Ent K (a : Mat)) with hA
    have hAinv : blkR K v (Ent K ((a⁻¹ : G∞) : Mat)) = Aᴴ := by
      rw [blkR_Ent_inv]; exact Matrix.inv_eq_right_inv (haR v)
    have hmul : blkR K v (Ent K ((a * x * a⁻¹ : G∞) : Mat)) =
        A * blkR K v (Ent K (x : Mat)) * Aᴴ := by
      rw [← hAinv]
      simp only [blkR_Ent, Matrix.GeneralLinearGroup.coe_mul, map_mul, hA]
    rw [hmul]
    have : A * blkR K v (Ent K (x : Mat)) * Aᴴ - 1 = A * (blkR K v (Ent K (x : Mat)) - 1) * Aᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, haR v]
    rw [this, hs_conj_of_mul_conjTranspose_eq_one _ _ (haR v)]
  · refine Finset.sum_congr rfl fun v _ => ?_
    set A := blkC K v (Ent K (a : Mat)) with hA
    have hAinv : blkC K v (Ent K ((a⁻¹ : G∞) : Mat)) = Aᴴ := by
      rw [blkC_Ent_inv]; exact Matrix.inv_eq_right_inv (haC v)
    have hmul : blkC K v (Ent K ((a * x * a⁻¹ : G∞) : Mat)) =
        A * blkC K v (Ent K (x : Mat)) * Aᴴ := by
      rw [← hAinv]
      simp only [blkC_Ent, Matrix.GeneralLinearGroup.coe_mul, map_mul, hA]
    rw [hmul]
    have : A * blkC K v (Ent K (x : Mat)) * Aᴴ - 1 = A * (blkC K v (Ent K (x : Mat)) - 1) * Aᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, haC v]
    rw [this, hs_conj_of_mul_conjTranspose_eq_one _ _ (haC v)]

theorem Nrm_Ent_conj (a x : G∞) :
    Nrm K (Ent K ((a * x * a⁻¹ : G∞) : Mat)) = Nrm K (Ent K (x : Mat)) := by
  rw [Nrm_Ent, Nrm_Ent]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 2
  have hdet : ((a * x * a⁻¹ : G∞) : Mat).det = (x : Mat).det := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
      Matrix.det_mul, mul_comm ((a : Mat).det), mul_assoc, ← Matrix.det_mul,
      ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.det_one, mul_one]
  rw [hdet]

theorem Φ_Ent_conj (ε σ : ℝ) (a : G∞)
    (haR : ∀ v, blkR K v (Ent K (a : Mat)) * (blkR K v (Ent K (a : Mat)))ᴴ = 1)
    (haC : ∀ v, blkC K v (Ent K (a : Mat)) * (blkC K v (Ent K (a : Mat)))ᴴ = 1)
    (x : G∞) :
    Φ K ε σ (Ent K ((a * x * a⁻¹ : G∞) : Mat)) = Φ K ε σ (Ent K (x : Mat)) := by
  unfold Φ
  rw [S_Ent_conj K a haR haC, Nrm_Ent_conj, ← Ent_inv, ← Ent_inv]
  have : (a * x * a⁻¹)⁻¹ = a * x⁻¹ * a⁻¹ := by group
  rw [this, S_Ent_conj K a haR haC]

end Entries

section Topology

variable (K : Type*) [Field K] [NumberField K]

local notation "Mat" => Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)
local notation "G∞" => GL (Fin 2) (InfiniteAdeleRing K)

omit [NumberField K] in
theorem continuous_ringEquiv_mixedSpace' : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K) = fun x : InfiniteAdeleRing K =>
      ((fun v : {w : InfinitePlace K // w.IsReal} => Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace K // w.IsComplex} => Completion.extensionEmbedding v.1 (x v))) :=
    funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact (Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

omit [NumberField K] in
theorem continuous_Ent : Continuous (Ent K) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace' K).comp (continuous_id.matrix_elem i j)

def Tube (ε : ℝ) : Set Mat := {m | S K (Ent K m) ≤ ε}

theorem mem_Tube {ε : ℝ} {m : Mat} : m ∈ Tube K ε ↔ S K (Ent K m) ≤ ε := Iff.rfl

theorem isClosed_Tube (ε : ℝ) : IsClosed (Tube K ε) :=
  isClosed_le ((continuous_S K).comp (continuous_Ent K)) continuous_const

theorem one_mem_Tube {ε : ℝ} (hε : 0 ≤ ε) : (1 : Mat) ∈ Tube K ε := by
  rw [mem_Tube, S_Ent_one]; exact hε

theorem norm_sub_sq_le_of_mem_Tube {ε : ℝ} {m : Mat} (hm : m ∈ Tube K ε) (i j : Fin 2)
    (w : InfinitePlace K) :
    ‖(m i j - (1 : Mat) i j) w‖ ^ 2 ≤ ε := by
  by_cases hw : w.IsReal
  · have h := (norm_sq_le_hs (blkR K ⟨w, hw⟩ (Ent K m) - 1) i j).trans ((hsR_le_S K _ ⟨w, hw⟩).trans hm)
    have e : (blkR K ⟨w, hw⟩ (Ent K m) - 1) i j = ρR K ⟨w, hw⟩ (m i j - (1 : Mat) i j) := by
      rw [blkR_Ent, ← map_one (ρR K ⟨w, hw⟩).mapMatrix, ← map_sub]
      rfl
    rwa [e, norm_ρR] at h
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have h := (norm_sq_le_hs (blkC K ⟨w, hw'⟩ (Ent K m) - 1) i j).trans ((hsC_le_S K _ ⟨w, hw'⟩).trans hm)
    have e : (blkC K ⟨w, hw'⟩ (Ent K m) - 1) i j = ρC K ⟨w, hw'⟩ (m i j - (1 : Mat) i j) := by
      rw [blkC_Ent, ← map_one (ρC K ⟨w, hw'⟩).mapMatrix, ← map_sub]
      rfl
    rwa [e, norm_ρC] at h

theorem norm_sub_le_sqrt_of_mem_Tube {ε : ℝ} {m : Mat} (hm : m ∈ Tube K ε) (i j : Fin 2)
    (w : InfinitePlace K) :
    ‖(m i j - (1 : Mat) i j) w‖ ≤ Real.sqrt ε := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (norm_sub_sq_le_of_mem_Tube K hm i j w)

theorem isCompact_Tube [∀ w : InfinitePlace K, ProperSpace w.Completion] (ε : ℝ) :
    IsCompact (Tube K ε) := by
  have hbox : IsCompact ((Set.pi Set.univ fun i : Fin 2 => Set.pi Set.univ fun j : Fin 2 =>
      Set.pi Set.univ fun w : InfinitePlace K =>
        Metric.closedBall ((1 : Mat) i j w) (Real.sqrt ε)) : Set Mat) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall _ _
  refine hbox.of_isClosed_subset (isClosed_Tube K ε) fun m hm => ?_
  refine Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => Set.mem_univ_pi.mpr fun w => ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact norm_sub_le_sqrt_of_mem_Tube K hm i j w

theorem det_apply_ne_zero_of_mem_Tube {ε : ℝ} (hε : ε < 1 / 16) {m : Mat} (hm : m ∈ Tube K ε)
    (w : InfinitePlace K) : m.det w ≠ 0 := by
  have hU : Ent K m ∈ U K := mem_U_of_S_lt K (lt_of_le_of_lt hm hε)
  by_cases hw : w.IsReal
  · have h := hU.1 ⟨w, hw⟩
    rw [detR_Ent, ρR_apply] at h
    intro h0
    exact h (by rw [show m.det (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}).1 = 0 from h0, map_zero])
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have h := hU.2 ⟨w, hw'⟩
    rw [detC_Ent, ρC_apply] at h
    intro h0
    exact h (by rw [show m.det (⟨w, hw'⟩ : {w : InfinitePlace K // w.IsComplex}).1 = 0 from h0, map_zero])

noncomputable def piInv (x : InfiniteAdeleRing K) : InfiniteAdeleRing K := fun w => (x w)⁻¹

omit [NumberField K] in
theorem mul_piInv {x : InfiniteAdeleRing K} (hx : ∀ w, x w ≠ 0) : x * piInv K x = 1 :=
  funext fun w => mul_inv_cancel₀ (hx w)

omit [NumberField K] in
theorem piInv_mul {x : InfiniteAdeleRing K} (hx : ∀ w, x w ≠ 0) : piInv K x * x = 1 :=
  funext fun w => inv_mul_cancel₀ (hx w)

omit [NumberField K] in
theorem isUnit_of_forall_ne_zero {x : InfiniteAdeleRing K} (hx : ∀ w, x w ≠ 0) : IsUnit x :=
  ⟨⟨x, piInv K x, mul_piInv K hx, piInv_mul K hx⟩, rfl⟩

omit [NumberField K] in
theorem ringInverse_eq {x : InfiniteAdeleRing K} (hx : ∀ w, x w ≠ 0) : Ring.inverse x = piInv K x :=
  Ring.inverse_unit ⟨x, piInv K x, mul_piInv K hx, piInv_mul K hx⟩

omit [NumberField K] in
theorem continuous_det_apply (w : InfinitePlace K) : Continuous fun m : Mat => m.det w :=
  (continuous_apply w : Continuous fun a : (∀ w : InfinitePlace K, w.Completion) => a w).comp
    (continuous_id.matrix_det : Continuous fun m : Mat => m.det)

noncomputable def toGL {ε : ℝ} (hε : ε < 1 / 16) (m : Tube K ε) : G∞ where
  val := m.1
  inv := m.1⁻¹
  val_inv := Matrix.mul_nonsing_inv _ (isUnit_of_forall_ne_zero K (det_apply_ne_zero_of_mem_Tube K hε m.2))
  inv_val := Matrix.nonsing_inv_mul _ (isUnit_of_forall_ne_zero K (det_apply_ne_zero_of_mem_Tube K hε m.2))

theorem coe_toGL {ε : ℝ} (hε : ε < 1 / 16) (m : Tube K ε) : ((toGL K hε m : G∞) : Mat) = m.1 := rfl

theorem toGL_eq {ε : ℝ} (hε : ε < 1 / 16) (g : G∞) (hg : (g : Mat) ∈ Tube K ε) :
    toGL K hε ⟨(g : Mat), hg⟩ = g :=
  Units.ext (coe_toGL K hε ⟨(g : Mat), hg⟩)

theorem continuous_toGL {ε : ℝ} (hε : ε < 1 / 16) : Continuous (toGL K hε) := by
  have hdet : Continuous fun m : Tube K ε => Ring.inverse (m.1.det) := by
    have heq : (fun m : Tube K ε => Ring.inverse (m.1.det)) = fun m => piInv K m.1.det :=
      funext fun m => ringInverse_eq K (det_apply_ne_zero_of_mem_Tube K hε m.2)
    rw [heq]
    refine continuous_pi fun w => ?_
    exact ((continuous_det_apply K w).comp continuous_subtype_val).inv₀
      fun m => det_apply_ne_zero_of_mem_Tube K hε m.2 w
  refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
  show Continuous fun m : Tube K ε => (m.1)⁻¹
  have heq : (fun m : Tube K ε => (m.1)⁻¹) = fun m => Ring.inverse (m.1.det) • m.1.adjugate :=
    funext fun m => Matrix.inv_def m.1
  rw [heq]
  exact continuous_matrix fun i j => hdet.mul (continuous_subtype_val.matrix_adjugate.matrix_elem i j)

theorem isCompact_range_toGL [∀ w : InfinitePlace K, ProperSpace w.Completion] {ε : ℝ}
    (hε : ε < 1 / 16) : IsCompact (Set.range (toGL K hε)) := by
  have : CompactSpace (Tube K ε) := isCompact_iff_compactSpace.mp (isCompact_Tube K ε)
  exact isCompact_range (continuous_toGL K hε)

theorem mem_range_toGL {ε : ℝ} (hε : ε < 1 / 16) {g : G∞} (hg : (g : Mat) ∈ Tube K ε) :
    g ∈ Set.range (toGL K hε) :=
  ⟨⟨g, hg⟩, toGL_eq K hε g hg⟩

theorem exists_range_toGL_subset {V : Set G∞} (hV : V ∈ nhds (1 : G∞)) :
    ∃ (ε : ℝ) (_ : 0 < ε) (hε : ε < 1 / 16), Set.range (toGL K hε) ⊆ V := by
  have h32 : (1 / 32 : ℝ) < 1 / 16 := by norm_num
  have h1 : (1 : Mat) ∈ Tube K (1 / 32) := one_mem_Tube K (by norm_num)
  have hc := (continuous_toGL K h32).continuousAt (x := ⟨1, h1⟩)
  have h1' : toGL K h32 ⟨1, h1⟩ = 1 := Units.ext (coe_toGL K h32 ⟨1, h1⟩)
  rw [ContinuousAt, h1'] at hc
  obtain ⟨O, hO, hOV⟩ := (mem_nhds_subtype _ _ _).mp (hc hV)
  have hO' : (id O : Set (Fin 2 → Fin 2 → ((w : InfinitePlace K) → w.Completion))) ∈
      @nhds (Fin 2 → Fin 2 → ((w : InfinitePlace K) → w.Completion)) _ (1 : Mat) := hO
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hO'
  refine ⟨min (1 / 32) (δ ^ 2 / 4), by positivity, lt_of_le_of_lt (min_le_left _ _) h32, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hm32 : (m.1 : Mat) ∈ Tube K (1 / 32) := by
    show S K (Ent K m.1) ≤ 1 / 32
    exact le_trans m.2 (min_le_left _ _)
  have key : (⟨m.1, hm32⟩ : Tube K (1 / 32)) ∈ toGL K h32 ⁻¹' V := by
    apply hOV
    show (m.1 : Mat) ∈ O
    apply hball
    have key' : dist (id (m.1 : Mat) : Fin 2 → Fin 2 → ((w : InfinitePlace K) → w.Completion))
        (id (1 : Mat) : Fin 2 → Fin 2 → ((w : InfinitePlace K) → w.Completion)) < δ := by
      refine (dist_pi_lt_iff hδ).mpr fun i => (dist_pi_lt_iff hδ).mpr fun j =>
        (dist_pi_lt_iff hδ).mpr fun w => ?_
      rw [dist_eq_norm]
      have hb : ‖(m.1 i j - (1 : Mat) i j) w‖ ^ 2 ≤ δ ^ 2 / 4 :=
        (norm_sub_sq_le_of_mem_Tube K m.2 i j w).trans (min_le_right _ _)
      have hn : 0 ≤ ‖(m.1 i j - (1 : Mat) i j) w‖ := norm_nonneg _
      have hle : ‖(m.1 i j - (1 : Mat) i j) w‖ ≤ δ / 2 := by nlinarith
      exact lt_of_le_of_lt hle (by linarith)
    exact Metric.mem_ball.mpr key'
  have : toGL K (lt_of_le_of_lt (min_le_left _ _) h32) m = toGL K h32 ⟨m.1, hm32⟩ :=
    Units.ext (by rw [coe_toGL, coe_toGL])
  rw [this]
  exact key

end Topology

section PlatformGlue

variable (F : Type) [Field F] [NumberField F]

local notation "Mat" => Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)
local notation "G∞" => GL (Fin 2) (InfiniteAdeleRing F)

omit [NumberField F] in
theorem archEntries_eq_Ent (g : G∞) : archEntries F g = Ent F (g : Mat) := rfl

theorem mapMatrix_mul_conjTranspose_eq_one {L : Type*} [NormedField L] {𝕜 : Type*} [RCLike 𝕜]
    (φ : L →+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (hsurj : Function.Surjective φ)
    (k : GL (Fin 2) L) (hk : IsRowIsometry k) :
    φ.mapMatrix (k : Matrix (Fin 2) (Fin 2) L) * (φ.mapMatrix (k : Matrix (Fin 2) (Fin 2) L))ᴴ = 1 := by
  apply mul_conjTranspose_eq_one_of_rowIsometry
  intro X Y
  obtain ⟨x, rfl⟩ := hsurj X
  obtain ⟨y, rfl⟩ := hsurj Y
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul, ← map_add, hφ]
  exact hk.2 x y

omit [NumberField F] in
theorem coe_archRowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    ((archRowIsometryInclAt₀ F w k : G∞) : Mat) =
      archMatrixUpdate F w ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
  rfl

omit [NumberField F] in
theorem blkR_Ent_archRow_self (v : {w : InfinitePlace F // w.IsReal})
    (k : rowIsometrySubgroup₀ (v.1).Completion) :
    blkR F v (Ent F ((archRowIsometryInclAt₀ F v.1 k : G∞) : Mat)) =
      (Completion.extensionEmbeddingOfIsReal v.2).mapMatrix
        ((k : GL (Fin 2) (v.1).Completion) : Matrix _ _ _) := by
  ext i j
  simp only [blkR_Ent, RingHom.mapMatrix_apply, Matrix.map_apply, ρR_apply, coe_archRowIsometryInclAt₀,
    archMatrixUpdate_apply_self]

omit [NumberField F] in
theorem blkR_Ent_archRow_of_ne (v : {w : InfinitePlace F // w.IsReal}) {w : InfinitePlace F}
    (h : v.1 ≠ w) (k : rowIsometrySubgroup₀ w.Completion) :
    blkR F v (Ent F ((archRowIsometryInclAt₀ F w k : G∞) : Mat)) = 1 := by
  ext i j
  simp only [blkR_Ent, RingHom.mapMatrix_apply, Matrix.map_apply, ρR_apply, coe_archRowIsometryInclAt₀,
    archMatrixUpdate_apply_of_ne F w _ i j h, Matrix.one_apply]
  split_ifs <;> simp

omit [NumberField F] in
theorem blkC_Ent_archRow_self (v : {w : InfinitePlace F // w.IsComplex})
    (k : rowIsometrySubgroup₀ (v.1).Completion) :
    blkC F v (Ent F ((archRowIsometryInclAt₀ F v.1 k : G∞) : Mat)) =
      (Completion.extensionEmbedding v.1).mapMatrix ((k : GL (Fin 2) (v.1).Completion) : Matrix _ _ _) := by
  ext i j
  simp only [blkC_Ent, RingHom.mapMatrix_apply, Matrix.map_apply, ρC_apply, coe_archRowIsometryInclAt₀,
    archMatrixUpdate_apply_self]

omit [NumberField F] in
theorem blkC_Ent_archRow_of_ne (v : {w : InfinitePlace F // w.IsComplex}) {w : InfinitePlace F}
    (h : v.1 ≠ w) (k : rowIsometrySubgroup₀ w.Completion) :
    blkC F v (Ent F ((archRowIsometryInclAt₀ F w k : G∞) : Mat)) = 1 := by
  ext i j
  simp only [blkC_Ent, RingHom.mapMatrix_apply, Matrix.map_apply, ρC_apply, coe_archRowIsometryInclAt₀,
    archMatrixUpdate_apply_of_ne F w _ i j h, Matrix.one_apply]
  split_ifs <;> simp

omit [NumberField F] in
theorem blocks_unitary (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (∀ v, blkR F v (Ent F ((archRowIsometryInclAt₀ F w k : G∞) : Mat)) *
        (blkR F v (Ent F ((archRowIsometryInclAt₀ F w k : G∞) : Mat)))ᴴ = 1) ∧
    (∀ v, blkC F v (Ent F ((archRowIsometryInclAt₀ F w k : G∞) : Mat)) *
        (blkC F v (Ent F ((archRowIsometryInclAt₀ F w k : G∞) : Mat)))ᴴ = 1) := by
  have hk : IsRowIsometry (k : GL (Fin 2) w.Completion) := ((mem_rowIsometrySubgroup₀_iff _).mp k.2).2
  refine ⟨fun v => ?_, fun v => ?_⟩
  · by_cases h : v.1 = w
    · subst h
      rw [blkR_Ent_archRow_self]
      exact mapMatrix_mul_conjTranspose_eq_one _
        (fun x => (Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _) x)
        (Completion.ringEquivRealOfIsReal v.2).surjective _ hk
    · rw [blkR_Ent_archRow_of_ne F v h, Matrix.conjTranspose_one, Matrix.mul_one]
  · by_cases h : v.1 = w
    · subst h
      rw [blkC_Ent_archRow_self]
      exact mapMatrix_mul_conjTranspose_eq_one _
        (fun x => (Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _) x)
        (Completion.ringEquivComplexOfIsComplex v.2).surjective _ hk
    · rw [blkC_Ent_archRow_of_ne F v h, Matrix.conjTranspose_one, Matrix.mul_one]

theorem ideleNorm_det_adelicArchGLIncl (x : G∞) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) =
      Nrm F (Ent F (x : Mat)) := by
  have h2 : (((Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x) : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F)).2 = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← adeleFin_apply, RingHom.map_det]
    have hval : ((glFin (𝓞 F) F (adelicArchGLIncl F x) :
          GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) =
        (adeleFin (𝓞 F) F).mapMatrix
          ((adelicArchGLIncl F x : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      rfl
    rw [← hval, glFin_adelicArchGLIncl, Matrix.GeneralLinearGroup.coe_one, Matrix.det_one]
  have h1 : (((Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x) : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F)).1 = (x : Mat).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← adeleArch_apply, RingHom.map_det]
    have hval : ((glArch (𝓞 F) F (adelicArchGLIncl F x) : G∞) : Mat) =
        (adeleArch (𝓞 F) F).mapMatrix
          ((adelicArchGLIncl F x : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      rfl
    rw [← hval, glArch_adelicArchGLIncl]
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one F _ h2, h1,
    Nrm_Ent]

end PlatformGlue

end BumpAux

open scoped Classical in
theorem exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (V : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hV : V ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      IsArchTestFactor F h ∧
      (∀ x, (((h x).re : ℝ) : ℂ) = h x ∧ 0 ≤ (h x).re) ∧
      0 < (h 1).re ∧
      tsupport h ⊆ V ∧
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        h (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = h x) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), h x = conj (h x⁻¹) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)
    := by
  have proper : ∀ w : InfinitePlace F, ProperSpace w.Completion := properSpace_completion
  have := proper
  obtain ⟨ε, hε0, hε, hsub⟩ := BumpAux.exists_range_toGL_subset F hV
  set hfun : GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
    fun x => ((BumpAux.Φ F ε σ (BumpAux.Ent F (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) : ℝ) : ℂ)
    with hfun_def
  have hsupp : Function.support hfun ⊆ Set.range (BumpAux.toGL F hε) := by
    intro x hx
    apply BumpAux.mem_range_toGL
    show BumpAux.S F (BumpAux.Ent F (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) ≤ ε
    by_contra hle
    push Not at hle
    apply hx
    simp only [hfun_def, BumpAux.Φ_eq_zero_of_le F hε0 hle.le, Complex.ofReal_zero]
  refine ⟨hfun, ⟨⟨fun m => ((BumpAux.Φ F ε σ m : ℝ) : ℂ), ?_, fun g => rfl⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (BumpAux.contDiff_Φ F hε0 hε σ)
  · exact HasCompactSupport.of_support_subset_isCompact (BumpAux.isCompact_range_toGL F hε) hsupp
  · intro x
    exact ⟨by simp only [hfun_def, Complex.ofReal_re],
      by simpa only [hfun_def, Complex.ofReal_re] using BumpAux.Φ_nonneg F ε σ _⟩
  · simp only [hfun_def, Complex.ofReal_re, Units.val_one]
    rw [BumpAux.Φ_Ent_one]
    exact one_pos
  · exact (closure_minimal hsupp (BumpAux.isCompact_range_toGL F hε).isClosed).trans hsub
  · intro w k x
    obtain ⟨haR, haC⟩ := BumpAux.blocks_unitary F w k
    simp only [hfun_def]
    rw [BumpAux.Φ_Ent_conj F ε σ _ haR haC x]
  · intro x
    simp only [hfun_def]
    rw [BumpAux.ideleNorm_det_adelicArchGLIncl, Complex.conj_ofReal, ← Complex.ofReal_mul,
      BumpAux.Φ_Ent_flat F x ε σ]

open Ws1.Cover AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction NumberField.InfinitePlace NumberField.AdelicVolume in
theorem exists_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧
      ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)),
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) →
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c (max u R) d₁ d₂ κ)
    := by
  classical
  obtain ⟨ρ, hρ0, hbal⟩ := Ws1.Cover.exists_unit_log_balance F
  obtain ⟨R, hR0, hred⟩ := Ws1.Cover.exists_int_translate_le F
  obtain ⟨dd, hdd⟩ : ∃ dd : ℝ, dd = ∑ w : InfinitePlace F, (w.mult : ℝ) := ⟨_, rfl⟩
  have hmult1 : ∀ w : InfinitePlace F, (1 : ℝ) ≤ w.mult := fun w => by exact_mod_cast (mult_pos (w := w))
  have hdd1 : 1 ≤ dd := by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rw [hdd]
    exact le_trans (hmult1 w₀) (Finset.single_le_sum (fun w _ => le_trans zero_le_one (hmult1 w)) (Finset.mem_univ w₀))
  have hdd0 : 0 < dd := lt_of_lt_of_le one_pos hdd1
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.exp (max 2 dd * ρ) := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by rw [hκ]; exact Real.one_le_exp (mul_nonneg (le_trans zero_le_two (le_max_left _ _)) hρ0)
  have hκ0 : 0 < κ := by rw [hκ]; exact Real.exp_pos _
  have hlogκ : Real.log κ = max 2 dd * ρ := by rw [hκ, Real.log_exp]
  have h2ρ : 2 * ρ ≤ Real.log κ := by rw [hlogκ]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0
  have hdρ : dd * ρ ≤ Real.log κ := by rw [hlogκ]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hρ0
  refine ⟨κ, R, hκ1, hR0, fun c u d₁ d₂ T hcov g => ?_⟩

  obtain ⟨γ, z, hγ⟩ := hcov g
  simp only [Set.mem_iUnion, Set.mem_image] at hγ
  obtain ⟨x, hxT, s, hs, hsx⟩ := hγ
  rw [mem_centreCutSiegelSet_iff] at hs
  obtain ⟨hint, hfloor, hwin, hdet⟩ := hs
  obtain ⟨hgt, hhgt⟩ : ∃ hgt : InfinitePlace F → ℝ, hgt = fun w => localHeight (archComponent F w (glArch (𝓞 F) F s)) := ⟨_, rfl⟩
  have hhgtw : ∀ w, hgt w = localHeight (archComponent F w (glArch (𝓞 F) F s)) := fun w => by rw [hhgt]
  have hpos : ∀ w, 0 < hgt w := fun w => by rw [hhgtw]; exact localHeight_pos _

  have hε : ∃ ε : (𝓞 F)ˣ, (∀ w w' : InfinitePlace F, w ((ε : 𝓞 F) : F) * hgt w ≤ κ * (w' ((ε : 𝓞 F) : F) * hgt w')) ∧
      ∀ w : InfinitePlace F, c ≤ w ((ε : 𝓞 F) : F) * hgt w := by
    by_cases hcomp : ∀ w w' : InfinitePlace F, hgt w ≤ κ * hgt w'
    · refine ⟨1, fun w w' => ?_, fun w => ?_⟩
      · simp only [Units.val_one, map_one, one_mul]
        exact hcomp w w'
      · simp only [Units.val_one, map_one, one_mul]
        rw [hhgtw]; exact hfloor w
    · push Not at hcomp
      obtain ⟨w₁, w₂, hlt⟩ := hcomp
      obtain ⟨ε, hεb⟩ := hbal (fun w => Real.log (hgt w))
      obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (hgt w')) /
          (∑ w' : InfinitePlace F, (w'.mult : ℝ)) := ⟨_, rfl⟩
      have hwε : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w =>
        (InfinitePlace.pos_iff).mpr (by exact_mod_cast ε.ne_zero)
      have hlog : ∀ w : InfinitePlace F, Real.log (w ((ε : 𝓞 F) : F) * hgt w) = Real.log (hgt w) + Real.log (w ((ε : 𝓞 F) : F)) := by
        intro w; rw [Real.log_mul (hwε w).ne' (hpos w).ne', add_comm]
      have hup : ∀ w : InfinitePlace F, Real.log (w ((ε : 𝓞 F) : F) * hgt w) ≤ m + ρ := fun w => by
        rw [hlog]; have := hεb w; rw [← hm, abs_le] at this; linarith [this.2]
      have hdown : ∀ w : InfinitePlace F, m - ρ ≤ Real.log (w ((ε : 𝓞 F) : F) * hgt w) := fun w => by
        rw [hlog]; have := hεb w; rw [← hm, abs_le] at this; linarith [this.1]
      refine ⟨ε, fun w w' => ?_, fun w => ?_⟩
      ·
        have hpw : 0 < w ((ε : 𝓞 F) : F) * hgt w := mul_pos (hwε w) (hpos w)
        have hpw' : 0 < w' ((ε : 𝓞 F) : F) * hgt w' := mul_pos (hwε w') (hpos w')
        rw [← Real.log_le_log_iff hpw (mul_pos hκ0 hpw'), Real.log_mul hκ0.ne' hpw'.ne']
        linarith [hup w, hdown w']
      ·
        rcases le_or_gt c 0 with hc | hc
        · exact le_trans hc (mul_pos (hwε w) (hpos w)).le
        ·
          have hlogc : ∀ w' : InfinitePlace F, Real.log c ≤ Real.log (hgt w') := fun w' =>
            Real.log_le_log hc (by rw [hhgtw]; exact hfloor w')
          have hw₁ : Real.log c + Real.log κ ≤ Real.log (hgt w₁) := by
            have h1 : κ * c ≤ κ * hgt w₂ := mul_le_mul_of_nonneg_left (by rw [hhgtw]; exact hfloor w₂) hκ0.le
            have h2 : κ * c < hgt w₁ := lt_of_le_of_lt h1 hlt
            rw [← Real.log_mul hc.ne' hκ0.ne', mul_comm]
            exact (Real.log_le_log (mul_pos hκ0 hc) h2.le)
          have hsum : dd * Real.log c + Real.log κ ≤ ∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (hgt w') := by
            rw [hdd, Finset.sum_mul, Fintype.sum_eq_add_sum_subtype_ne _ w₁,
              Fintype.sum_eq_add_sum_subtype_ne (fun w' : InfinitePlace F => (w'.mult : ℝ) * Real.log (hgt w')) w₁]
            have hA : (w₁.mult : ℝ) * Real.log c + Real.log κ ≤ (w₁.mult : ℝ) * Real.log (hgt w₁) := by
              have := mul_le_mul_of_nonneg_left hw₁ (le_trans zero_le_one (hmult1 w₁))
              have hk : Real.log κ ≤ (w₁.mult : ℝ) * Real.log κ :=
                le_mul_of_one_le_left (by rw [hlogκ]; positivity) (hmult1 w₁)
              linarith
            have hB : ∑ w' : {w' : InfinitePlace F // w' ≠ w₁}, (w'.1.mult : ℝ) * Real.log c ≤
                ∑ w' : {w' : InfinitePlace F // w' ≠ w₁}, (w'.1.mult : ℝ) * Real.log (hgt w'.1) :=
              Finset.sum_le_sum fun w' _ => mul_le_mul_of_nonneg_left (hlogc w'.1) (le_trans zero_le_one (hmult1 w'.1))
            linarith
          have hmlow : Real.log c + ρ ≤ m := by
            rw [hm, ← hdd, le_div_iff₀ hdd0]
            nlinarith [hsum, hdρ, hdd0]
          have := hdown w
          have hpw : 0 < w ((ε : 𝓞 F) : F) * hgt w := mul_pos (hwε w) (hpos w)
          rw [← Real.log_le_log_iff hc hpw]
          linarith
  obtain ⟨ε, hratio, hfloor'⟩ := hε
  have hwε : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w =>
    (InfinitePlace.pos_iff).mpr (by exact_mod_cast ε.ne_zero)

  obtain ⟨y, hydef⟩ : ∃ y : InfinitePlace F → ℂ, y = fun w => InfinitePlace.Completion.extensionEmbedding w ((((ε : 𝓞 F) : F)) : w.Completion) *
    xCoord (((archComponent F w (glArch (𝓞 F) F s) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map
      (InfinitePlace.Completion.extensionEmbedding w)) := ⟨_, rfl⟩
  have hyreal : ∀ w : InfinitePlace F, w.IsReal → (y w).im = 0 := by
    intro w hw
    rw [hydef]; dsimp only
    rw [Complex.mul_im, im_extensionEmbedding_of_isReal F hw, im_xCoord_eq_zero _ (fun i j => ?_), mul_zero, zero_mul,
      add_zero]
    rw [Matrix.map_apply]
    exact im_extensionEmbedding_of_isReal F hw _
  obtain ⟨β, hβ⟩ := hred y hyreal

  obtain ⟨aval, haval⟩ : ∃ aval : ∀ w : InfinitePlace F, w.Completion, aval = fun w => ofRealAt F w (Real.sqrt (w ((ε : 𝓞 F) : F))⁻¹) := ⟨_, rfl⟩
  have ha0 : ∀ w, aval w ≠ 0 := fun w => by
    rw [← norm_pos_iff, haval]; dsimp only
    rw [norm_ofRealAt, abs_of_pos (Real.sqrt_pos.mpr (inv_pos.mpr (hwε w)))]
    exact Real.sqrt_pos.mpr (inv_pos.mpr (hwε w))
  obtain ⟨a, ha⟩ : ∃ a : ∀ w : InfinitePlace F, (w.Completion)ˣ, a = fun w => Units.mk0 (aval w) (ha0 w) := ⟨_, rfl⟩
  have hnorma : ∀ w, ‖(a w : w.Completion)‖ ^ 2 = (w ((ε : 𝓞 F) : F))⁻¹ := fun w => by
    rw [ha]; dsimp only; rw [Units.val_mk0, haval]; dsimp only
    rw [norm_ofRealAt, sq_abs, Real.sq_sqrt (inv_pos.mpr (hwε w)).le]

  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : GL (Fin 2) F, γ₀ = unipotentGL2 ((β : F)) * diagOne (unitF F ε) := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : (AdeleRing (𝓞 F) F)ˣ, z' = archIdele F a := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : AdelicGL2 (𝓞 F) F, s' = centralScalar (𝓞 F) F z' * (globalPoints (𝓞 F) F γ₀ * s) := ⟨_, rfl⟩
  refine ⟨γ₀ * γ, z * z', ?_⟩
  have hnew : globalPoints (𝓞 F) F (γ₀ * γ) * g * centralScalar (𝓞 F) F (z * z') = s' * x := by
    rw [map_mul, map_mul, hs']
    calc globalPoints (𝓞 F) F γ₀ * globalPoints (𝓞 F) F γ * g * (centralScalar (𝓞 F) F z * centralScalar (𝓞 F) F z')
        = globalPoints (𝓞 F) F γ₀ * (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z) * centralScalar (𝓞 F) F z' := by
          simp only [mul_assoc]
      _ = globalPoints (𝓞 F) F γ₀ * (s * x) * centralScalar (𝓞 F) F z' := by rw [hsx]
      _ = globalPoints (𝓞 F) F γ₀ * s * (x * centralScalar (𝓞 F) F z') := by simp only [mul_assoc]
      _ = globalPoints (𝓞 F) F γ₀ * s * (centralScalar (𝓞 F) F z' * x) := by rw [mul_centralScalar_comm]
      _ = (globalPoints (𝓞 F) F γ₀ * s) * centralScalar (𝓞 F) F z' * x := by simp only [mul_assoc]
      _ = centralScalar (𝓞 F) F z' * (globalPoints (𝓞 F) F γ₀ * s) * x := by rw [mul_centralScalar_comm]
  rw [hnew]
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨x, hxT, s', ?_, rfl⟩

  have hγ₀c := redElt_coe F ε β
  have hfacts : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F s')) = w ((ε : 𝓞 F) : F) * hgt w ∧
      archDetNorm w s' = archDetNorm w s ∧
      xWindowSq (archComponent F w (glArch (𝓞 F) F s')) = ‖y w + (w.embedding : F →+* ℂ) (β : F)‖ ^ 2 := by
    intro w
    have hcomp : archComponent F w (glArch (𝓞 F) F s') =
        archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z')) *
          (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ₀)) * archComponent F w (glArch (𝓞 F) F s)) := by
      rw [hs', map_mul, map_mul, map_mul, map_mul]
    obtain ⟨hZ00, hZ01, hZ10, hZ11⟩ := archComponent_centralScalar_archIdele F w a
    rw [← hz'] at hZ00 hZ01 hZ10 hZ11
    have hU : ∀ i j, (((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ₀))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = ((!![((ε : 𝓞 F) : F), (β : F); 0, 1] : Matrix (Fin 2) (Fin 2) F) i j : w.Completion) := by
      intro i j
      rw [archComponent_globalPoints_apply, hγ₀, hγ₀c]
    have hεw : ((((ε : 𝓞 F) : F)) : w.Completion) ≠ 0 := by
      rw [← norm_pos_iff, norm_coe_completion]; exact hwε w
    obtain ⟨h1, h2, h3⟩ := step_place F w (archComponent F w (glArch (𝓞 F) F s))
      (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ₀)))
      (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z')))
      ((((ε : 𝓞 F) : F)) : w.Completion) (((β : F)) : w.Completion) (a w : w.Completion) hεw (a w).ne_zero
      (by rw [hU]; simp) (by rw [hU]; simp)
      (by rw [hU]; simp [NumberField.InfinitePlace.Completion.ext_iff])
      (by rw [hU]; simp [NumberField.InfinitePlace.Completion.ext_iff])
      hZ00 hZ01 hZ10 hZ11
    rw [← hcomp] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, norm_coe_completion, hhgtw]
    · unfold archDetNorm
      rw [h2, hnorma, norm_coe_completion, inv_mul_cancel₀ (hwε w).ne', one_mul]
    · rw [h3, hydef]
      dsimp only
      congr 2
      simp

  rw [mem_centreCutSiegelSetAmple_iff, mem_centreCutSiegelSet_iff]
  refine ⟨⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩, fun w w' => ?_⟩
  ·
    rw [hs', map_mul, map_mul, hz', glFin_centralScalar_archIdele, one_mul, hγ₀, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (glFin_globalPoints_unipotentGL2_mem F β)
      (glFin_globalPoints_diagOne_mem F ε)) hint
  ·
    rw [(hfacts w).1]
    exact hfloor' w
  ·
    rw [(hfacts w).2.2]
    calc ‖y w + (w.embedding : F →+* ℂ) (β : F)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hβ w) 2
      _ ≤ (max u R) ^ 2 := pow_le_pow_left₀ hR0 (le_max_right _ _) 2
  ·
    rw [(hfacts w).2.1]
    exact hdet w
  ·
    rw [(hfacts w).1, (hfacts w').1]
    exact hratio w w'

/-! ## 432 — finite `L²` mass of the union

The pin's `S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le` prelude: translation
invariance of the Haar integral, the archimedean unit idèle, and the central rescalings into the
determinant window. Transcribed at the pin's names and at the pin's visibility (all seventeen are
public in the pin file); statements unchanged. -/

namespace Ws23
namespace V2E

open MeasureTheory
open scoped ENNReal

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

omit [MeasurableSpace G] [MeasurableMul G] in
theorem image_mul_left_eq_preimage (z : G) (A : Set G) :
    (fun x => z * x) '' A = (fun x => z⁻¹ * x) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨z⁻¹ * x, hx, by simp⟩

theorem measurableSet_image_mul_left (z : G) {A : Set G} (hA : MeasurableSet A) :
    MeasurableSet ((fun x => z * x) '' A) := by
  rw [image_mul_left_eq_preimage]
  exact measurable_const_mul _ hA

theorem setLIntegral_image_mul_left (μ : Measure G) [μ.IsMulLeftInvariant]
    (f : G → ℝ≥0∞) (z : G) (r : ℝ≥0∞) (hr : r ≠ ∞) (hf : ∀ x, f (z * x) = r * f x)
    {A : Set G} (hA : MeasurableSet A) :
    ∫⁻ x in (fun x => z * x) '' A, f x ∂μ = r * ∫⁻ x in A, f x ∂μ := by
  have hmeas := measurableSet_image_mul_left z hA
  have hind : ∀ x, ((fun x => z * x) '' A).indicator f (z * x) = r * A.indicator f x := by
    intro x
    by_cases hx : x ∈ A
    · have hx' : z * x ∈ (fun x => z * x) '' A := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hf]
    · have hx' : z * x ∉ (fun x => z * x) '' A := by
        rintro ⟨y, hy, hyx⟩
        exact hx (mul_left_cancel hyx ▸ hy)
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  rw [← lintegral_indicator hmeas, ← lintegral_indicator hA,
    ← lintegral_mul_left_eq_self (fun x => ((fun x => z * x) '' A).indicator f x) z]
  simp only [hind]
  rw [lintegral_const_mul' _ _ hr]

end Generic

section Tsum

theorem tsum_prod_pow_le {ι : Type*} [Fintype ι] (q : ι → ℝ≥0∞) :
    ∑' n : ι → ℕ, ∏ i, q i ^ n i ≤ ∏ i, ∑' k : ℕ, q i ^ k := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set N : ℕ := s.sup fun n => Finset.univ.sup n with hN
  have hs : s ⊆ Fintype.piFinset fun _ : ι => Finset.range (N + 1) := by
    intro n hn
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    calc n i ≤ Finset.univ.sup n := Finset.le_sup (f := n) (Finset.mem_univ i)
      _ ≤ N := Finset.le_sup (f := fun n => Finset.univ.sup n) hn
  calc ∑ n ∈ s, ∏ i, q i ^ n i ≤ ∑ n ∈ Fintype.piFinset fun _ : ι => Finset.range (N + 1), ∏ i, q i ^ n i :=
        Finset.sum_le_sum_of_subset hs
    _ = ∏ i, ∑ k ∈ Finset.range (N + 1), q i ^ k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' k : ℕ, q i ^ k := Finset.prod_le_prod fun i _ => ENNReal.sum_le_tsum _

theorem tsum_prod_pow_lt_top {ι : Type*} [Fintype ι] (q : ι → ℝ≥0∞) (hq : ∀ i, q i < 1) :
    ∑' n : ι → ℕ, ∏ i, q i ^ n i < ⊤ := by
  refine (tsum_prod_pow_le q).trans_lt ?_
  refine ENNReal.prod_lt_top fun i _ => ?_
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 (hq i))

end Tsum

end V2E
end Ws23

noncomputable section

namespace Ws23
namespace V2E

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace
open scoped ENNReal

section Adelic

variable {F : Type} [Field F] [NumberField F]

def archUnitIdele : ((v : InfinitePlace F) → (v.Completion)ˣ) →* (AdeleRing (𝓞 F) F)ˣ where
  toFun b :=
    { val := ((fun v => (b v : v.Completion) : InfiniteAdeleRing F), 1)
      inv := ((fun v => ((b v)⁻¹ : (v.Completion)ˣ) : InfiniteAdeleRing F), 1)
      val_inv := by
        refine Prod.ext (funext fun v => ?_) (one_mul 1)
        show (b v : v.Completion) * ((b v)⁻¹ : (v.Completion)ˣ) = 1
        rw [Units.mul_inv]
      inv_val := by
        refine Prod.ext (funext fun v => ?_) (one_mul 1)
        show ((b v)⁻¹ : (v.Completion)ˣ) * (b v : v.Completion) = 1
        rw [Units.inv_mul] }
  map_one' := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) rfl
    show ((1 : (v.Completion)ˣ) : v.Completion) = 1
    rw [Units.val_one]
  map_mul' b b' := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) (one_mul 1).symm
    show ((b v * b' v : (v.Completion)ˣ) : v.Completion) = (b v : v.Completion) * (b' v : v.Completion)
    rw [Units.val_mul]

theorem archUnitIdele_fst (b : (v : InfinitePlace F) → (v.Completion)ˣ) (v : InfinitePlace F) :
    ((archUnitIdele b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = (b v : v.Completion) := rfl

theorem archUnitIdele_snd (b : (v : InfinitePlace F) → (v.Completion)ˣ) :
    ((archUnitIdele b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

open scoped Classical in
theorem archCentralUnit_eq_archUnitIdele (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archCentralUnit F w a = archUnitIdele (Pi.mulSingle w a) := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) rfl
  show Function.update (1 : (u : InfinitePlace F) → u.Completion) w (a : w.Completion) v
    = ((Pi.mulSingle (M := fun u : InfinitePlace F => (u.Completion)ˣ) w a v : (v.Completion)ˣ) : v.Completion)
  by_cases hv : v = w
  · subst hv
    rw [Function.update_self, Pi.mulSingle_eq_same]
  · rw [Function.update_of_ne hv, Pi.mulSingle_eq_of_ne hv, Units.val_one]
    rfl

theorem archUnitIdele_pow_eq_prod (a : (v : InfinitePlace F) → (v.Completion)ˣ)
    (n : InfinitePlace F → ℕ) :
    archUnitIdele (fun v => a v ^ n v) = ∏ v, (archCentralUnit F v (a v)) ^ n v := by
  classical
  have : (fun v => a v ^ n v) = ∏ v, Pi.mulSingle v (a v ^ n v) := (Finset.univ_prod_mulSingle _).symm
  rw [this, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [archCentralUnit_eq_archUnitIdele, ← map_pow, Pi.mulSingle_pow]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * h = h * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _) _).eq

theorem archDetNorm_centralScalar_mul' (v : InfinitePlace F) (w : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F w * g)
      = (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  set s := archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then (w : AdeleRing (𝓞 F) F).1 v else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, ite_eq_left rfl]
    · rw [centralScalar_apply_ne _ h, ite_eq_right h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

theorem centralScalar_mul_mem_centreCutSiegelSet {c u d₁ d₂ e₁ e₂ : ℝ}
    {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (hdet : ∀ v : InfinitePlace F,
      (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g ∈ Set.Icc e₁ e₂) :
    centralScalar (𝓞 F) F w * g ∈ centreCutSiegelSet F c u e₁ e₂ := by
  obtain ⟨h1, h2, h3, -⟩ := hg
  set s := centralScalar (𝓞 F) F w with hs
  have h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w := centralScalar_apply_eq w 0
  have h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 := centralScalar_apply_ne w (by decide)
  have h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := centralScalar_apply_ne w (by decide)
  have h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w := centralScalar_apply_eq w 1
  have hglFin : glFin (𝓞 F) F s = 1 := glFin_scalar_eq_one F hwf h00 h01 h10 h11
  have hcomp00 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 0 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h00]
  have hcomp01 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 1 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h01]; rfl
  have hcomp10 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h10]; rfl
  have hcomp11 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 1 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h11]
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [map_mul, hglFin, one_mul]
    exact h1
  · rw [map_mul, map_mul, localHeight_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h2 v
  · rw [map_mul, map_mul, xWindowSq_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h3 v
  · rw [hs, archDetNorm_centralScalar_mul']
    exact hdet v

theorem archDetNorm_mul (v : InfinitePlace F) (g x : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (g * x) = archDetNorm v g * archDetNorm v x := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

omit [NumberField F] in

theorem exists_norm_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 ≤ r) :
    ∃ a : v.Completion, ‖a‖ = r := by
  rcases v.isReal_or_isComplex with hv | hv
  · obtain ⟨a, ha⟩ := Completion.surjective_extensionEmbeddingOfIsReal hv r
    refine ⟨a, ?_⟩
    rw [← (Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) a, ha,
      Real.norm_of_nonneg hr]
  · obtain ⟨a, ha⟩ := Completion.surjective_extensionEmbedding_of_isComplex hv (r : ℂ)
    refine ⟨a, ?_⟩
    rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) a, ha,
      Complex.norm_real, Real.norm_of_nonneg hr]

theorem measurableSet_iUnion_centreCutSiegelSet (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

end Adelic

end V2E
end Ws23

end

open NumberField.AdelicVolume in
theorem memLp_iUnion_centreCutSiegelSet_of_detWindow_le
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφm : letI := glBorel (Fin 2) (𝓞 F) F; AEStronglyMeasurable φ (adelicGLHaar (Fin 2) (𝓞 F) F))
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂))) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    := by
  classical
  have hd₁' : d₁ ≤ dp := hd₁
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have : MeasurableMul (AdelicGL2 (𝓞 F) F) :=
    ⟨fun g => (continuous_const_mul g).measurable, fun g => (continuous_mul_const g).measurable⟩
  set Dp : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂ with hDp
  set D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hD
  have hDpm : MeasurableSet Dp := Ws23.V2E.measurableSet_iUnion_centreCutSiegelSet c u dp d₂ T
  set f : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ‖φ g‖ₑ ^ 2 with hf
  have hfz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      f (centralScalar (𝓞 F) F z * g) = ‖((ω z : ℂˣ) : ℂ)‖ₑ ^ 2 * f g := by
    intro z g
    simp only [hf, hω, enorm_mul, mul_pow]

  have hIp : ∫⁻ g in Dp, f g ∂μ < ⊤ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞)) (f := φ)
      (μ := μ.restrict Dp) two_ne_zero ENNReal.ofNat_ne_top hL2.eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h2
    exact h2

  suffices hfin : ∫⁻ g in D, f g ∂μ < ⊤ by
    show eLpNorm φ 2 (μ.restrict D) < ∞
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hφm.restrict]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

  set ρ : ℝ := dp / d₂ with hρ
  have hd₂ : 0 < d₂ := hdp.trans hdp₂
  have hρ0 : 0 < ρ := div_pos hdp hd₂
  have hρ1 : ρ < 1 := (div_lt_one hd₂).mpr hdp₂
  have hunit : ∀ v : InfinitePlace F, ∃ a : (v.Completion)ˣ, ‖(a : v.Completion)‖ = Real.sqrt ρ := by
    intro v
    obtain ⟨a, ha⟩ := Ws23.V2E.exists_norm_eq v (Real.sqrt_nonneg ρ)
    have ha0 : a ≠ 0 := by
      rw [← norm_pos_iff, ha]
      exact Real.sqrt_pos.mpr hρ0
    exact ⟨Units.mk0 a ha0, ha⟩
  choose a ha using hunit
  have ha2 : ∀ v, ‖(a v : v.Completion)‖ * ‖(a v : v.Completion)‖ = ρ := fun v => by
    rw [ha, Real.mul_self_sqrt hρ0.le]
  have ha1 : ∀ v, ‖(a v : v.Completion)‖ < 1 := fun v => by
    rw [ha, Real.sqrt_lt' one_pos, one_pow]
    exact hρ1

  set zι : (InfinitePlace F → ℕ) → (AdeleRing (𝓞 F) F)ˣ := fun n => Ws23.V2E.archUnitIdele fun v => a v ^ n v
    with hzι
  set B : (InfinitePlace F → ℕ) → Set (AdelicGL2 (𝓞 F) F) := fun n =>
    (fun g => centralScalar (𝓞 F) F (zι n) * g) '' Dp with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n => Ws23.V2E.measurableSet_image_mul_left _ hDpm
  have hBmass : ∀ n, ∫⁻ g in B n, f g ∂μ = ‖((ω (zι n) : ℂˣ) : ℂ)‖ₑ ^ 2 * ∫⁻ g in Dp, f g ∂μ := fun n =>
    Ws23.V2E.setLIntegral_image_mul_left μ f (centralScalar (𝓞 F) F (zι n)) _
      (ENNReal.pow_ne_top enorm_ne_top) (hfz (zι n)) hDpm

  set q : InfinitePlace F → ℝ≥0∞ := fun v => ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖ₑ ^ 2 with hq
  have hmult : ∀ n, ‖((ω (zι n) : ℂˣ) : ℂ)‖ₑ ^ 2 = ∏ v, q v ^ n v := by
    intro n
    have hnn : ‖((ω (zι n) : ℂˣ) : ℂ)‖₊ = ∏ v, ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖₊ ^ n v := by
      rw [hzι]
      show ‖((ω (Ws23.V2E.archUnitIdele fun v => a v ^ n v) : ℂˣ) : ℂ)‖₊ = _
      rw [Ws23.V2E.archUnitIdele_pow_eq_prod, map_prod, Units.coe_prod, nnnorm_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_pow, Units.val_pow_eq_pow_val, nnnorm_pow]
    simp only [hq, enorm_eq_nnnorm, hnn, ENNReal.ofNNReal_finsetProd, ENNReal.coe_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm, pow_mul]

  have hcover : ∀ g ∈ D, ∃ n : InfinitePlace F → ℕ, g ∈ B n ∧ ∀ v, d₁ ≤ ρ ^ n v * d₂ := by
    intro g hg
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hg
    have hsdet := fun v => (mem_centreCutSiegelSet_iff.mp hs).2.2.2 v

    have hex : ∀ v, ∃ k : ℕ, ρ ^ (k + 1) < archDetNorm v s / d₂ ∧ archDetNorm v s / d₂ ≤ ρ ^ k := fun v =>
      exists_nat_pow_near_of_lt_one (div_pos (archDetNorm_pos v s) hd₂)
        ((div_le_one hd₂).mpr (hsdet v).2) hρ0 hρ1
    choose n hn using hex
    refine ⟨n, ?_, fun v => ?_⟩
    ·
      have hzinv : (zι n)⁻¹ = Ws23.V2E.archUnitIdele (fun v => (a v ^ n v)⁻¹) := by
        rw [hzι, ← map_inv]
        rfl
      refine ⟨centralScalar (𝓞 F) F (zι n)⁻¹ * (s * x), ?_, ?_⟩
      · refine Set.mem_iUnion₂.mpr ⟨x, hx, centralScalar (𝓞 F) F (zι n)⁻¹ * s, ?_, mul_assoc _ _ _⟩
        rw [hzinv]
        refine Ws23.V2E.centralScalar_mul_mem_centreCutSiegelSet (Ws23.V2E.archUnitIdele_snd _)
          (fun v => ?_) hs (fun v => ?_)
        · rw [Ws23.V2E.archUnitIdele_fst]
          exact Units.ne_zero _
        · rw [Ws23.V2E.archUnitIdele_fst, Units.val_inv_eq_inv_val, norm_inv, Units.val_pow_eq_pow_val, norm_pow,
            ← mul_inv, ← pow_add, ← two_mul, pow_mul, sq, ha2]
          obtain ⟨h1, h2⟩ := hn v
          have hpos := archDetNorm_pos v s
          have hρn : 0 < ρ ^ n v := pow_pos hρ0 _
          constructor
          · rw [le_inv_mul_iff₀ hρn]
            have : ρ ^ (n v + 1) * d₂ < archDetNorm v s := (lt_div_iff₀ hd₂).mp h1
            calc ρ ^ n v * dp = ρ ^ (n v + 1) * d₂ := by rw [hρ, pow_succ]; field_simp
              _ ≤ archDetNorm v s := this.le
          · rw [inv_mul_le_iff₀ hρn]
            rwa [← div_le_iff₀ hd₂]
      · show centralScalar (𝓞 F) F (zι n) * (centralScalar (𝓞 F) F (zι n)⁻¹ * (s * x)) = s * x
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    ·
      obtain ⟨-, h2⟩ := hn v
      calc d₁ ≤ archDetNorm v s := (hsdet v).1
        _ ≤ ρ ^ n v * d₂ := by rwa [← div_le_iff₀ hd₂]

  set S : Set (InfinitePlace F → ℕ) := {n | ∀ v, d₁ ≤ ρ ^ n v * d₂} with hS
  have hDsub : D ⊆ ⋃ n ∈ S, B n := by
    intro g hg
    obtain ⟨n, hgn, hnS⟩ := hcover g hg
    exact Set.mem_iUnion₂.mpr ⟨n, hnS, hgn⟩

  set B' : (InfinitePlace F → ℕ) → Set (AdelicGL2 (𝓞 F) F) := fun n => if n ∈ S then B n else ∅ with hB'
  have hB'sub : (⋃ n ∈ S, B n) ⊆ ⋃ n, B' n := by
    intro g hg
    obtain ⟨n, hn, hgn⟩ := Set.mem_iUnion₂.mp hg
    exact Set.mem_iUnion.mpr ⟨n, by simp only [hB', ite_eq_left hn]; exact hgn⟩
  have hle : ∫⁻ g in D, f g ∂μ ≤ ∑' n, ∫⁻ g in B' n, f g ∂μ :=
    (lintegral_mono_set (hDsub.trans hB'sub)).trans (lintegral_iUnion_le _ _)
  have hterm : ∀ n, ∫⁻ g in B' n, f g ∂μ = if n ∈ S then (∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ else 0 := by
    intro n
    by_cases hn : n ∈ S
    · simp only [hB', ite_eq_left hn, hBmass n, hmult n]
    · simp only [hB', ite_eq_right hn, Measure.restrict_empty, lintegral_zero_measure]
  refine hle.trans_lt ?_
  simp_rw [hterm]
  by_cases hd : 0 < d₁
  ·
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ρ ^ N < d₁ / d₂ := exists_pow_lt_of_lt_one (div_pos hd hd₂) hρ1
    have hSfin : S ⊆ (Fintype.piFinset fun _ : InfinitePlace F => Finset.range N : Finset (InfinitePlace F → ℕ)) := by
      intro n hn
      refine Fintype.mem_piFinset.2 fun v => Finset.mem_range.2 ?_
      by_contra hge
      push Not at hge
      have h1 : ρ ^ n v ≤ ρ ^ N := pow_le_pow_of_le_one hρ0.le hρ1.le hge
      have h2 : d₁ ≤ ρ ^ n v * d₂ := hn v
      have : d₁ < d₁ := by
        calc d₁ ≤ ρ ^ n v * d₂ := h2
          _ ≤ ρ ^ N * d₂ := by gcongr
          _ < d₁ / d₂ * d₂ := by gcongr
          _ = d₁ := div_mul_cancel₀ d₁ hd₂.ne'
      exact lt_irrefl _ this
    rw [tsum_eq_sum (s := Fintype.piFinset fun _ : InfinitePlace F => Finset.range N) (fun n hn => by
      rw [ite_eq_right (fun h => hn (hSfin h))])]
    refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    split_ifs
    · exact ENNReal.mul_lt_top (ENNReal.prod_lt_top fun v _ => ENNReal.pow_lt_top (ENNReal.pow_lt_top enorm_lt_top)) hIp
    · exact ENNReal.zero_lt_top
  ·
    push Not at hd
    have hq1 : ∀ v, q v < 1 := by
      intro v
      have h := hcontr hd v (a v) (ha1 v)
      have h' : ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖ₑ < 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr h
      calc q v = ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖ₑ ^ 2 := rfl
        _ < 1 ^ 2 := by gcongr
        _ = 1 := one_pow 2
    calc ∑' n, (if n ∈ S then (∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ else 0)
        ≤ ∑' n : InfinitePlace F → ℕ, (∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          split_ifs
          · exact le_rfl
          · exact zero_le
      _ = (∑' n : InfinitePlace F → ℕ, ∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ := ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top (Ws23.V2E.tsum_prod_pow_lt_top q hq1) hIp

theorem not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero
    (F : Type) [Field F] [NumberField F] (c d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ¬ CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c 0 d₁ d₂)
    := by
  exact CentreCutEngine.not_coversModCentre_of_u_eq_zero (K := F) T

end AutomorphicForm
