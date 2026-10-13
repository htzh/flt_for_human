/-
  The multiplication sign, the trace-dual bridge, and the bivariate theta kernel.

  This is wave 4 of the `completedDedekindZeta` package, and the largest module so
  far.  It introduces the multiplication sign `multSign` on `index K` and the
  diagonal matrix `Phi` it defines, the trace identity
  `stdBasis_Phi_bilinear_eq_trace` (the `Phi`-bilinear form of the standard basis
  is the trace form of `K`), the basis `idealBasisK` of a fractional ideal in `K`
  together with the bilinear term `biTerm`, the trace-dual ideal `traceDualIdeal`,
  the integer bridge matrix `bridgeMatZ` (absolute determinant `1`), and the bridge
  `bridgeEquiv` between the theta sums of `I` and of its trace dual.  It then lands
  the closed functional equation `heckeKernel_closed_functionalEquation`, the
  `unitPart` factorisation of the cone parameter, the Gaussian domination
  `multiIdealTheta_sub_one_exp_bound`, the continuity of the Hecke kernel, the
  rapid-decay bounds `genericKernel_sub_one_isBigO_exp`,
  `heckeKernel_sub_one_isBigO_rpow` and their `multSq` analogues, and assembles the
  weak functional-equation pair `heckeWeakFEPair` of mathlib's `WeakFEPair ℂ`.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:1965–3148`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.Gapsw80T6TraceDualBridge` and `FLT.Gapsw80T7ClosedFEWeakPair`
  blocks.  The pin's obligation prefixes and per-obligation namespaces are dropped;
  every declaration carries the pin's own name and line in the `-- pin:` comment
  above it (playbook §2.3, §4).

  The pin's file-wide `set_option maxHeartbeats 6400000` and its
  `set_option maxHeartbeats 12800000 in` before `heckeWeakFEPair` are not
  transcribed; the port's global cap is `4000000`.  Proofs are adapted to mathlib
  `v4.34.0`: deprecated lemma names (`if_true`, `continuous_finset_prod`,
  `continuous_finset_sum`, `Set.mem_setOf_eq`), unused `simp` arguments and unused
  binder names are repaired, and `omit [NumberField K] in` silences the
  unused-section-variable linter on the declarations whose statement never
  mentions the `K`-instance.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Places
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Trace.Basic

namespace NumberField.CompletedDedekindZeta

open Matrix
open Module
open WithLp
open MeasureTheory
open Real
open NumberField
open NumberField.InfinitePlace
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open _root_.Complex hiding exp
open scoped Classical
open scoped RealInnerProductSpace
open scoped nonZeroDivisors
open scoped Topology

noncomputable section

/-! ### The multiplication sign and the trace-dual bridge -/

section TraceDualBridge

variable (K : Type) [Field K] [NumberField K]

-- pin: gapsw80_t6_multSign (S_NumberField_exists_completedDedekindZeta_package.lean:2012)
def multSign : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 2 else -2)

omit [NumberField K] in
-- pin: multSign_inl (S_NumberField_exists_completedDedekindZeta_package.lean:2015)
@[scoped simp] theorem multSign_inl (w : {w : InfinitePlace K // IsReal w}) :
    multSign K (Sum.inl w) = 1 := rfl

omit [NumberField K] in
-- pin: multSign_inr_fst (S_NumberField_exists_completedDedekindZeta_package.lean:2018)
@[scoped simp] theorem multSign_inr_fst (w : {w : InfinitePlace K // IsComplex w}) :
    multSign K (Sum.inr (w, 0)) = 2 := rfl

omit [NumberField K] in
-- pin: multSign_inr_snd (S_NumberField_exists_completedDedekindZeta_package.lean:2021)
@[scoped simp] theorem multSign_inr_snd (w : {w : InfinitePlace K // IsComplex w}) :
    multSign K (Sum.inr (w, 1)) = -2 := rfl

omit [NumberField K] in
-- pin: multSign_sq (S_NumberField_exists_completedDedekindZeta_package.lean:2024)
theorem multSign_sq (c : index K) :
    (multSign K c) ^ 2 = ((mult (placeOf K c)) ^ 2 : ℝ) := by
  rcases c with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · simp [mult, hw]
  · rw [placeOf_inr, mult, ite_eq_right (not_isReal_iff_isComplex.mpr hw)]
    fin_cases j <;> simp [multSign]

-- pin: gapsw80_t6_Phi (S_NumberField_exists_completedDedekindZeta_package.lean:2031)
def Phi : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.diagonal fun i => multSign K ((indexEquivFin K).symm i)

-- pin: gapsw80_t6_Phi_Dscale_Phi (S_NumberField_exists_completedDedekindZeta_package.lean:2034)
theorem Phi_Dscale_Phi (y : InfinitePlace K → ℝ) :
    (Phi K)ᵀ * Dscale K y * Phi K
      = Dscale K (fun w => (mult w : ℝ)^2 * y w) := by
  rw [Phi, Matrix.diagonal_transpose, Dscale, Dscale,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  refine Matrix.diagonal_eq_diagonal_iff.mpr fun i => ?_
  rw [show multSign K ((indexEquivFin K).symm i) * y (placeOf K ((indexEquivFin K).symm i))
        * multSign K ((indexEquivFin K).symm i)
      = multSign K ((indexEquivFin K).symm i) ^ 2
        * y (placeOf K ((indexEquivFin K).symm i)) from by ring,
    multSign_sq]

omit [NumberField K] in
-- pin: abs_multSign (S_NumberField_exists_completedDedekindZeta_package.lean:2046)
theorem abs_multSign (c : index K) :
    |multSign K c| = (mult (placeOf K c) : ℝ) := by
  rcases c with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · simp [mult, hw]
  · have hmult : mult (w : InfinitePlace K) = 2 := by
      rw [mult]; exact ite_eq_right (not_isReal_iff_isComplex.mpr hw)
    fin_cases j <;> simp [multSign, placeOf_inr, hmult]

-- pin: gapsw80_t6_abs_det_Phi (S_NumberField_exists_completedDedekindZeta_package.lean:2054)
theorem abs_det_Phi :
    |(Phi K).det| = (4 : ℝ) ^ nrComplexPlaces K := by
  rw [Phi, Matrix.det_diagonal, Finset.abs_prod]
  calc ∏ i, |multSign K ((indexEquivFin K).symm i)|
      = ∏ c : index K, (mult (placeOf K c) : ℝ) := by
        rw [Fintype.prod_equiv (indexEquivFin K).symm _ (fun c => |multSign K c|)
          (fun i => rfl)]
        exact Finset.prod_congr rfl fun c _ => abs_multSign K c
    _ = ∏ w : InfinitePlace K, (mult w : ℝ) ^ mult w := by
        rw [← Finset.prod_fiberwise Finset.univ (placeOf K)
            (fun c => (mult (placeOf K c) : ℝ))]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [Finset.prod_eq_pow_card fun c hc => by
              rw [Finset.mem_filter] at hc; rw [hc.2]]
        congr 1
        rcases isReal_or_isComplex w with hw | hw
        · rw [mult, ite_eq_left hw, fiber_placeOf_isReal K hw, Finset.card_singleton]
        · rw [mult, ite_eq_right (not_isReal_iff_isComplex.mpr hw), fiber_placeOf_isComplex K hw,
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    _ = (4 : ℝ) ^ nrComplexPlaces K := by
        rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => IsReal w)]
        simp only [mult_isReal, Nat.cast_one, pow_one, Finset.prod_const_one, one_mul]
        have hmn : ∀ w : {w : InfinitePlace K // ¬IsReal w},
            mult (w : InfinitePlace K) = 2 :=
          fun w => by rw [mult, ite_eq_right w.2]
        simp only [fun w => hmn w, Nat.cast_ofNat]
        rw [show ((2 : ℝ) ^ 2 : ℝ) = 4 from by norm_num, Finset.prod_const,
          Finset.card_univ]
        congr 1
        exact Fintype.card_congr
          (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex)


variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
-- pin: gapsw80_t6_idealBasisK (S_NumberField_exists_completedDedekindZeta_package.lean:2088)
def idealBasisK (i : Fin (nK K)) : K :=
  basisOfFractionalIdeal K I ((chooseBasisIndexEquivFin K I).symm i)

-- pin: mixedEmbedding_idealBasisK (S_NumberField_exists_completedDedekindZeta_package.lean:2091)
theorem mixedEmbedding_idealBasisK (i : Fin (nK K)) :
    mixedEmbedding K (idealBasisK K I i)
      = (idealLatticeBasisInt K I i : mixedSpace K) := by
  rw [idealBasisK, idealLatticeBasisInt_apply, fractionalIdealLatticeBasis_apply]

-- pin: idealBasisK_mem (S_NumberField_exists_completedDedekindZeta_package.lean:2096)
theorem idealBasisK_mem (i : Fin (nK K)) :
    idealBasisK K I i ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have h : idealBasisK K I i ∈ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
    rw [← mem_span_basisOfFractionalIdeal]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact h

-- pin: gapsw80_t6_biTerm (S_NumberField_exists_completedDedekindZeta_package.lean:2103)
def biTerm (a b : K) (c : index K) : ℝ :=
  (mixedEmbedding.stdBasis K).repr (mixedEmbedding K a) c
    * multSign K c
    * (mixedEmbedding.stdBasis K).repr (mixedEmbedding K b) c

-- pin: biTerm_isReal (S_NumberField_exists_completedDedekindZeta_package.lean:2108)
theorem biTerm_isReal (a b : K) (w : {w : InfinitePlace K // IsReal w}) :
    biTerm K a b (Sum.inl w)
      = embedding_of_isReal w.2 (a * b) := by
  unfold biTerm
  rw [multSign_inl, mul_one, stdBasis_apply_isReal, stdBasis_apply_isReal,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal, ← map_mul]

-- pin: biTerm_isComplex_sum (S_NumberField_exists_completedDedekindZeta_package.lean:2115)
theorem biTerm_isComplex_sum (a b : K) (w : {w : InfinitePlace K // IsComplex w}) :
    biTerm K a b (Sum.inr (w, 0)) + biTerm K a b (Sum.inr (w, 1))
      = 2 * (w.1.embedding (a * b)).re := by
  unfold biTerm
  simp only [multSign_inr_fst, multSign_inr_snd, stdBasis_apply_isComplex_fst,
    stdBasis_apply_isComplex_snd, mixedEmbedding_apply_isComplex, map_mul, Complex.mul_re]
  ring

-- pin: sum_biTerm_eq_sum_embeddings (S_NumberField_exists_completedDedekindZeta_package.lean:2123)
theorem sum_biTerm_eq_sum_embeddings (a b : K) :
    ((∑ c : index K, biTerm K a b c : ℝ) : ℂ)
      = ∑ φ : K →+* ℂ, φ (a * b) := by

  have hRHS : (∑ φ : K →+* ℂ, φ (a * b))
      = ∑ c : index K, (indexEquiv K c) (a * b) :=
    ((indexEquiv K).sum_comp (fun φ => φ (a * b))).symm
  rw [hRHS, Fintype.sum_sum_type, Fintype.sum_sum_type, Complex.ofReal_add,
    Complex.ofReal_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => ?_) ?_
  · rw [biTerm_isReal, indexEquiv_apply_isReal, ← embedding_of_isReal_apply w.2]
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Complex.ofReal_add, ← Complex.ofReal_add,
      biTerm_isComplex_sum, indexEquiv_apply_isComplex_fst, indexEquiv_apply_isComplex_snd,
      ComplexEmbedding.conjugate_coe_eq, Complex.add_conj, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

-- pin: gapsw80_t6_stdBasis_Phi_bilinear_eq_trace (S_NumberField_exists_completedDedekindZeta_package.lean:2141)
theorem stdBasis_Phi_bilinear_eq_trace (a b : K) :
    ∑ i : Fin (nK K),
      (stdBasisFin K).repr (mixedEmbedding K a) i
        * multSign K ((indexEquivFin K).symm i)
        * (stdBasisFin K).repr (mixedEmbedding K b) i
      = ((Algebra.trace ℚ K (a * b) : ℚ) : ℝ) := by

  have hLHS : ∑ i : Fin (nK K),
        (stdBasisFin K).repr (mixedEmbedding K a) i
          * multSign K ((indexEquivFin K).symm i)
          * (stdBasisFin K).repr (mixedEmbedding K b) i
      = ∑ c : index K, biTerm K a b c := by
    rw [Fintype.sum_equiv (indexEquivFin K).symm _ (biTerm K a b) fun i => ?_]
    unfold biTerm
    simp only [stdBasisFin, Basis.repr_reindex_apply]
  rw [hLHS]
  have hRHS : ((Algebra.trace ℚ K (a * b) : ℚ) : ℂ)
      = ∑ φ : K →+* ℂ, φ (a * b) := by
    rw [show ((Algebra.trace ℚ K (a * b) : ℚ) : ℂ)
          = algebraMap ℚ ℂ (Algebra.trace ℚ K (a * b)) from rfl,
      trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ),
      ← (RingHom.equivRatAlgHom (R := K) (S := ℂ)).sum_comp (fun σ => σ (a * b))]
    rfl
  have h := sum_biTerm_eq_sum_embeddings K a b
  rw [← hRHS] at h
  exact_mod_cast h

-- pin: gapsw80_t6_traceDualIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:2168)
def traceDualIdeal : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

-- pin: coe_traceDualIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:2172)
@[scoped simp] theorem coe_traceDualIdeal :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

-- pin: gapsw80_t6_bridgeMatrix (S_NumberField_exists_completedDedekindZeta_package.lean:2176)
def bridgeMatrix : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  (coordMatrix K I)ᵀ * Phi K * coordMatrix K (traceDualIdeal K I)

-- pin: coordMatrix_apply (S_NumberField_exists_completedDedekindZeta_package.lean:2179)
theorem coordMatrix_apply (i j : Fin (nK K)) :
    coordMatrix K I i j
      = (stdBasisFin K).repr (mixedEmbedding K (idealBasisK K I j)) i := by
  rw [coordMatrix_eq_toMatrix, Basis.toMatrix_apply, mixedEmbedding_idealBasisK]

-- pin: gapsw80_t6_bridgeMatrix_entry_eq_trace (S_NumberField_exists_completedDedekindZeta_package.lean:2184)
theorem bridgeMatrix_entry_eq_trace (j k : Fin (nK K)) :
    bridgeMatrix K I j k
      = ((Algebra.trace ℚ K
          (idealBasisK K I j
            * idealBasisK K (traceDualIdeal K I) k) : ℚ) : ℝ) := by
  rw [← stdBasis_Phi_bilinear_eq_trace, bridgeMatrix,
    Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_apply, coordMatrix_apply,
    show (Phi K * coordMatrix K (traceDualIdeal K I)) i k
      = multSign K ((indexEquivFin K).symm i)
          * coordMatrix K (traceDualIdeal K I) i k from by
      rw [Phi, Matrix.diagonal_mul],
    coordMatrix_apply]
  ring

-- pin: gapsw80_t6_bridgeMatrix_entry_isInt (S_NumberField_exists_completedDedekindZeta_package.lean:2200)
theorem bridgeMatrix_entry_isInt (j k : Fin (nK K)) :
    ∃ m : ℤ, bridgeMatrix K I j k = (m : ℝ) := by
  rw [bridgeMatrix_entry_eq_trace]
  have hck : idealBasisK K (traceDualIdeal K I) k
      ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := idealBasisK_mem K (traceDualIdeal K I) k
    rwa [coe_traceDualIdeal] at h
  have hint : Algebra.traceForm ℚ K
        (idealBasisK K (traceDualIdeal K I) k)
        (idealBasisK K I j)
      ∈ (algebraMap ℤ ℚ).range :=
    (FractionalIdeal.mem_dual I.ne_zero).mp hck _ (idealBasisK_mem K I j)
  obtain ⟨m, hm⟩ := hint
  refine ⟨m, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm] at hm
  rw [← hm]
  simp only [eq_intCast, Rat.cast_intCast]

-- pin: gapsw80_t6_bridgeMatZ (S_NumberField_exists_completedDedekindZeta_package.lean:2218)
def bridgeMatZ : Matrix (Fin (nK K)) (Fin (nK K)) ℤ :=
  fun j k => (bridgeMatrix_entry_isInt K I j k).choose

-- pin: bridgeMatZ_cast_eq (S_NumberField_exists_completedDedekindZeta_package.lean:2221)
theorem bridgeMatZ_cast_eq :
    (bridgeMatZ K I).map (Int.cast : ℤ → ℝ) = bridgeMatrix K I := by
  ext j k
  exact (bridgeMatrix_entry_isInt K I j k).choose_spec.symm

-- pin: absNorm_traceDualIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:2226)
theorem absNorm_traceDualIdeal :
    FractionalIdeal.absNorm
        (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
          * ((discr K).natAbs : ℚ))⁻¹ := by
  have hd1 : FractionalIdeal.absNorm
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
        = ((discr K).natAbs : ℚ)⁻¹ := by
    have hcoe : (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹
        = (↑(differentIdeal ℤ (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)).symm
    rw [← inv_inv (FractionalIdeal.absNorm _), ← map_inv₀, hcoe,
      FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal (K := K)]
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, map_mul, map_inv₀, hd1,
    mul_comm, ← mul_inv]

-- pin: gapsw80_t6_abs_det_bridgeMatrix (S_NumberField_exists_completedDedekindZeta_package.lean:2242)
theorem abs_det_bridgeMatrix :
    |(bridgeMatrix K I).det| = 1 := by
  have hdet : |(bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (traceDualIdeal K I)) := by
    rw [bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, abs_det_Phi]
  rw [hdet, mixedEmbedding.covolume_idealLattice, mixedEmbedding.covolume_idealLattice,
    absNorm_traceDualIdeal]
  have hD : (0 : ℝ) < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hNI : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    have hne := (FractionalIdeal.absNorm_eq_zero_iff (K := K)).not.mpr I.ne_zero
    exact_mod_cast hne
  have hsqD : (Real.sqrt |(discr K : ℝ)|) ^ 2 = |(discr K : ℝ)| :=
    Real.sq_sqrt (abs_nonneg _)
  have hnatAbs : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h4 : (4 : ℝ) ^ nrComplexPlaces K * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K) ^ 2 = 1 := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul,
      mul_comm 2 (nrComplexPlaces K), ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]

  push_cast
  rw [hnatAbs, mul_inv]
  have hgoal : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
        * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|
        * (4 : ℝ) ^ nrComplexPlaces K
        * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹
            * |(discr K : ℝ)|⁻¹ * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
            * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹)
          * ((Real.sqrt |(discr K : ℝ)|) ^ 2 * |(discr K : ℝ)|⁻¹)
          * ((4 : ℝ) ^ nrComplexPlaces K * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K) ^ 2) := by
    ring
  rw [hgoal, mul_inv_cancel₀ hNI, hsqD, mul_inv_cancel₀ hD.ne', h4, one_mul, one_mul]

-- pin: cast_det_bridgeMatZ (S_NumberField_exists_completedDedekindZeta_package.lean:2279)
theorem cast_det_bridgeMatZ :
    ((bridgeMatZ K I).det : ℝ) = (bridgeMatrix K I).det := by
  have h : ((bridgeMatZ K I).map (Int.cast : ℤ → ℝ)).det
      = (bridgeMatrix K I).det := by rw [bridgeMatZ_cast_eq]
  rw [← h]
  exact (RingHom.map_det (Int.castRingHom ℝ) (bridgeMatZ K I)).trans
    (congrArg Matrix.det rfl)

-- pin: bridgeMatZ_isUnit (S_NumberField_exists_completedDedekindZeta_package.lean:2287)
theorem bridgeMatZ_isUnit : IsUnit (bridgeMatZ K I) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : |((bridgeMatZ K I).det : ℝ)| = 1 := by
    rw [cast_det_bridgeMatZ, abs_det_bridgeMatrix]
  have hn : (bridgeMatZ K I).det.natAbs = 1 := by
    have h2 : ((bridgeMatZ K I).det.natAbs : ℝ) = 1 := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
    exact_mod_cast h2
  exact Int.isUnit_iff_natAbs_eq.mpr hn

-- pin: gapsw80_t6_bridgeMatZUnit (S_NumberField_exists_completedDedekindZeta_package.lean:2297)
def bridgeMatZUnit : (Matrix (Fin (nK K)) (Fin (nK K)) ℤ)ˣ :=
  (bridgeMatZ_isUnit K I).unit

-- pin: coe_bridgeMatZUnit (S_NumberField_exists_completedDedekindZeta_package.lean:2300)
@[scoped simp] theorem coe_bridgeMatZUnit :
    ((bridgeMatZUnit K I : Matrix (Fin (nK K)) (Fin (nK K)) ℤ))
      = bridgeMatZ K I := rfl

-- pin: gapsw80_t6_bridgeEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:2304)
def bridgeEquiv : (Fin (nK K) → ℤ) ≃ (Fin (nK K) → ℤ) where
  toFun v := ((bridgeMatZUnit K I)⁻¹).val *ᵥ v
  invFun v := (bridgeMatZUnit K I).val *ᵥ v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

-- pin: zcastR_bridgeEquiv_apply (S_NumberField_exists_completedDedekindZeta_package.lean:2314)
theorem intCastVec_bridgeEquiv_apply (v : Fin (nK K) → ℤ) :
    intCastVec (bridgeEquiv K I v)
      = (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
          *ᵥ intCastVec v := by
  ext i
  change ((((bridgeMatZUnit K I)⁻¹).val *ᵥ v) i : ℝ) = _
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, intCastVec]
  push_cast
  rfl

-- pin: bridgeMatrix_mul_cast_inv (S_NumberField_exists_completedDedekindZeta_package.lean:2324)
theorem bridgeMatrix_mul_cast_inv :
    bridgeMatrix K I
        * (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = 1 := by
  have h : (bridgeMatZ K I) * ((bridgeMatZUnit K I)⁻¹).val
      = 1 := by
    conv_lhs => rw [← coe_bridgeMatZUnit, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmap : ((bridgeMatZ K I) * ((bridgeMatZUnit K I)⁻¹).val).map
        (Int.cast : ℤ → ℝ)
      = bridgeMatrix K I
          * (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ)) := by
    have := map_mul (Int.castRingHom ℝ).mapMatrix (bridgeMatZ K I)
      ((bridgeMatZUnit K I)⁻¹).val
    simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
    rw [this, bridgeMatZ_cast_eq]
  rw [← hmap, h]
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply, apply_ite (Int.cast : ℤ → ℝ)]

-- pin: Phi_mul_coordMatrix_mul_cast_inv (S_NumberField_exists_completedDedekindZeta_package.lean:2343)
theorem Phi_mul_coordMatrix_mul_cast_inv :
    Phi K * coordMatrix K (traceDualIdeal K I)
        * (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = ((coordMatrix K I)ᵀ)⁻¹ := by
  have hunit : IsUnit ((coordMatrix K I)ᵀ).det := by
    rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr (det_coordMatrix_ne_zero K I)
  have hcancel : ((coordMatrix K I)ᵀ)⁻¹ * (coordMatrix K I)ᵀ = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  calc Phi K * coordMatrix K (traceDualIdeal K I)
        * (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = (((coordMatrix K I)ᵀ)⁻¹ * (coordMatrix K I)ᵀ)
          * (Phi K * coordMatrix K (traceDualIdeal K I)
              * (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))) := by
        rw [hcancel, one_mul]
    _ = ((coordMatrix K I)ᵀ)⁻¹
          * (bridgeMatrix K I
              * (((bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))) := by
        rw [bridgeMatrix, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = ((coordMatrix K I)ᵀ)⁻¹ := by
        rw [bridgeMatrix_mul_cast_inv, mul_one]

-- pin: gapsw80_t6_dualQuadForm_eq (S_NumberField_exists_completedDedekindZeta_package.lean:2365)
theorem dualQuadForm_eq (y' : InfinitePlace K → ℝ) (v : Fin (nK K) → ℤ) :
    intCastVec v ⬝ᵥ ((coordMatrix K I)⁻¹
        * Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹) *ᵥ intCastVec v
      = intCastVec (bridgeEquiv K I v) ⬝ᵥ
          scaledGram K (traceDualIdeal K I)
            (fun w => (mult w : ℝ)^2 * y' w)
          *ᵥ intCastVec (bridgeEquiv K I v) := by

  have hMv : ((coordMatrix K I)ᵀ)⁻¹ *ᵥ intCastVec v
      = (Phi K * coordMatrix K (traceDualIdeal K I))
          *ᵥ intCastVec (bridgeEquiv K I v) := by
    rw [intCastVec_bridgeEquiv_apply, Matrix.mulVec_mulVec, Phi_mul_coordMatrix_mul_cast_inv]

  have hLHS : intCastVec v ⬝ᵥ ((coordMatrix K I)⁻¹ * Dscale K y'
        * ((coordMatrix K I)ᵀ)⁻¹) *ᵥ intCastVec v
      = (((coordMatrix K I)ᵀ)⁻¹ *ᵥ intCastVec v) ⬝ᵥ
          (Dscale K y') *ᵥ (((coordMatrix K I)ᵀ)⁻¹ *ᵥ intCastVec v) := by
    rw [show (coordMatrix K I)⁻¹ = (((coordMatrix K I)ᵀ)⁻¹)ᵀ from by
          rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose],
      Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (intCastVec v) (((coordMatrix K I)ᵀ)⁻¹)ᵀ, Matrix.vecMul_transpose]

  have hRHS : intCastVec (bridgeEquiv K I v) ⬝ᵥ
        (scaledGram K (traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w))
        *ᵥ intCastVec (bridgeEquiv K I v)
      = ((Phi K * coordMatrix K (traceDualIdeal K I))
            *ᵥ intCastVec (bridgeEquiv K I v))
          ⬝ᵥ (Dscale K y')
          *ᵥ ((Phi K * coordMatrix K (traceDualIdeal K I))
            *ᵥ intCastVec (bridgeEquiv K I v)) := by
    have hG : scaledGram K (traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w)
        = (Phi K * coordMatrix K (traceDualIdeal K I))ᵀ
            * Dscale K y'
            * (Phi K * coordMatrix K (traceDualIdeal K I)) := by
      rw [scaledGram, ← Phi_Dscale_Phi, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hG, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec _
        ((Phi K * coordMatrix K (traceDualIdeal K I))ᵀ),
      Matrix.vecMul_transpose]
  rw [hLHS, hRHS, hMv]

-- pin: gapsw80_t6_dualGramSum_eq_multiIdealTheta_codiff (S_NumberField_exists_completedDedekindZeta_package.lean:2409)
theorem dualGramSum_eq_multiIdealTheta_codiff (y' : InfinitePlace K → ℝ) :
    (∑' v : Fin (nK K) → ℤ,
      cexp ((-(π * (intCastVec v ⬝ᵥ ((coordMatrix K I)⁻¹
          * Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹)
        *ᵥ intCastVec v)) : ℝ) : ℂ))
      = multiIdealTheta K (traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w) := by
  conv_rhs => rw [multiIdealTheta, ← (bridgeEquiv K I).tsum_eq]
  exact tsum_congr fun v => by rw [dualQuadForm_eq]

-- pin: gapsw80_t6_heckeKernel_transformation_bridged (S_NumberField_exists_completedDedekindZeta_package.lean:2419)
theorem heckeKernel_transformation_bridged
    {t : ℝ} (ht : 0 < t) :
    heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          multiIdealTheta K (traceDualIdeal K I)
            (fun w => (mult w : ℝ)^2 * yParam K
              (mkParam K (Real.log t⁻¹ / 2) (-u)) w) ∂MeasureTheory.volume := by
  rw [heckeKernel_transformation_raw' K I ht]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  rw [← dualGramSum_eq_multiIdealTheta_codiff]


end TraceDualBridge

/-! ### The closed functional equation and the weak FE pair -/

section ClosedFEWeakPair

open Asymptotics Filter Set
open scoped Topology

variable (K : Type) [Field K] [NumberField K]
-- pin: gapsw80_t7_multSq (S_NumberField_exists_completedDedekindZeta_package.lean:2461)
def multSq : realSpace K := fun w => ((mult w : ℝ)) ^ 2

omit [NumberField K] in
-- pin: multSq_pos (S_NumberField_exists_completedDedekindZeta_package.lean:2463)
theorem multSq_pos (w : InfinitePlace K) : 0 < multSq K w :=
  pow_pos (Nat.cast_pos.mpr mult_pos) 2

omit [NumberField K] in
-- pin: multSq_unitSqScale_comm (S_NumberField_exists_completedDedekindZeta_package.lean:2466)
theorem multSq_unitSqScale_comm (η : (𝓞 K)ˣ) (y : realSpace K) :
    multSq K * (unitSqScale K η * y)
      = unitSqScale K η * (multSq K * y) := by
  ext w; simp only [Pi.mul_apply]; ring

-- pin: gapsw80_t7_multiIdealTheta_multSq_yParam_periodic (S_NumberField_exists_completedDedekindZeta_package.lean:2471)
theorem multiIdealTheta_multSq_yParam_periodic
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {i : InfinitePlace K} (hi : i ≠ w₀)
    (c : realSpace K) :
    multiIdealTheta K J
        (multSq K * yParam K (c + Pi.single i 1))
      = multiIdealTheta K J
          (multSq K * yParam K c) := by
  rw [yParam_add_single K hi, multSq_unitSqScale_comm,
    multiIdealTheta_unitSq_smul]

-- pin: mkParam_add_single (S_NumberField_exists_completedDedekindZeta_package.lean:2481)
theorem mkParam_add_single (r : ℝ) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    mkParam K r (u + Pi.single i 1)
      = mkParam K r u + Pi.single (i : InfinitePlace K) 1 := by
  ext w
  by_cases hw : w = w₀
  · subst hw
    simp only [mkParam_w₀, Pi.add_apply, Pi.single_eq_of_ne' i.2, add_zero]
  · simp only [mkParam_ne K hw, Pi.add_apply]
    by_cases hwi : w = (i : InfinitePlace K)
    · subst hwi
      simp [Pi.single_eq_same, show (⟨(i:InfinitePlace K), hw⟩ : {w // w ≠ w₀}) = i from
        Subtype.ext rfl]
    · rw [Pi.single_eq_of_ne (fun h => hwi (Subtype.ext_iff.mp h)),
        Pi.single_eq_of_ne hwi, add_zero]

-- pin: gapsw80_t7_integrand (S_NumberField_exists_completedDedekindZeta_package.lean:2497)
abbrev multHeckeIntegrand (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (u : logSpace K) : ℂ :=
  multiIdealTheta K J
    (multSq K * yParam K (mkParam K r u))

-- pin: gapsw80_t7_integrand_single_zperiodic (S_NumberField_exists_completedDedekindZeta_package.lean:2502)
theorem multHeckeIntegrand_single_zperiodic (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (r : ℝ) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ) (u : logSpace K) :
    multHeckeIntegrand K J r (u + k • Pi.single i 1) = multHeckeIntegrand K J r u := by
  have hstep : ∀ v : logSpace K,
      multHeckeIntegrand K J r (v + Pi.single i 1) = multHeckeIntegrand K J r v := fun v => by
    unfold multHeckeIntegrand
    rw [mkParam_add_single, multiIdealTheta_multSq_yParam_periodic K J i.2]
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [add_smul, one_smul, ← add_assoc, hstep]; exact ih
  | pred n ih =>
    have h' := (hstep (u + (-(n : ℤ) - 1) • Pi.single i 1)).symm
    rw [add_assoc, show (-(n:ℤ)-1) • Pi.single i (1:ℝ) + (Pi.single i 1 : logSpace K)
        = (-(n:ℤ)) • Pi.single i 1 from by rw [sub_smul, one_smul, sub_add_cancel]] at h'
    exact h'.trans ih

-- pin: gapsw80_t7_integrand_zlattice_invariant (S_NumberField_exists_completedDedekindZeta_package.lean:2518)
theorem multHeckeIntegrand_zlattice_invariant (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (r : ℝ) (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (u : logSpace K) :
    multHeckeIntegrand K J r ((g : logSpace K) + u) = multHeckeIntegrand K J r u := by
  have hmem := g.2
  rw [Basis.mem_span_iff_repr_mem] at hmem
  simp only [Pi.basisFun_repr] at hmem
  choose k hk using hmem
  have hg : (g : logSpace K) = ∑ i, (k i) • Pi.single i (1:ℝ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      ← hk, eq_intCast]
    simp [zsmul_eq_mul]
  rw [hg]

  induction (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀}) using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj,
      show (k j • Pi.single j (1:ℝ) + ∑ i ∈ s, k i • Pi.single i 1) + u
          = (∑ i ∈ s, k i • Pi.single i 1 + u) + k j • Pi.single j 1 from by abel,
      multHeckeIntegrand_single_zperiodic]
    exact ih

-- pin: gapsw80_t7_unitBox (S_NumberField_exists_completedDedekindZeta_package.lean:2542)
abbrev unitBox : Set (logSpace K) :=
  Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1

-- pin: unitBox_eq_fundamentalDomain (S_NumberField_exists_completedDedekindZeta_package.lean:2545)
theorem unitBox_eq_fundamentalDomain :
    unitBox K
      = ZSpan.fundamentalDomain (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}) :=
  (ZSpan.fundamentalDomain_pi_basisFun).symm

-- pin: gapsw80_t7_unitBox_isAddFundamentalDomain (S_NumberField_exists_completedDedekindZeta_package.lean:2550)
theorem unitBox_isAddFundamentalDomain :
    IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (unitBox K) volume := by
  rw [unitBox_eq_fundamentalDomain]
  exact ZSpan.isAddFundamentalDomain _ volume

local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun _ _ _ => measure_preimage_add _ _ _⟩

local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) := by
  refine Countable.of_equiv ({w : InfinitePlace K // w ≠ w₀} → ℤ)
    (Equiv.ofBijective
      (fun k : {w : InfinitePlace K // w ≠ w₀} → ℤ =>
        (⟨fun i => (k i : ℝ), ?_⟩ :
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))))
      ⟨?_, ?_⟩)
  · rw [Basis.mem_span_iff_repr_mem]; intro i; exact ⟨k i, by simp⟩
  · intro k₁ k₂ h
    exact funext fun i => Int.cast_injective (congr_fun (Subtype.ext_iff.mp h) i)
  · intro ⟨v, hv⟩
    rw [Basis.mem_span_iff_repr_mem] at hv
    simp only [Pi.basisFun_repr] at hv
    choose k hk using hv
    exact ⟨k, Subtype.ext (funext fun i => by simp [← hk i, eq_intCast])⟩

-- pin: gapsw80_t7_neg_unitBox_isAddFundamentalDomain (S_NumberField_exists_completedDedekindZeta_package.lean:2579)
theorem neg_unitBox_isAddFundamentalDomain :
    IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      ((Neg.neg : logSpace K → logSpace K) '' unitBox K) volume := by
  refine (unitBox_isAddFundamentalDomain K).image_of_equiv
    (Equiv.neg (logSpace K))
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    (Equiv.neg _) ?_
  intro g x
  show -((-g : logSpace K) + x) = (g : logSpace K) + -x
  simp only [neg_add, neg_neg]

-- pin: gapsw80_t7_setIntegral_neg_box_eq (S_NumberField_exists_completedDedekindZeta_package.lean:2591)
theorem setIntegral_neg_unitBox_eq (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    ∫ u in unitBox K, multHeckeIntegrand K J r (-u) ∂volume
      = ∫ u in unitBox K, multHeckeIntegrand K J r u ∂volume := by

  calc ∫ u in unitBox K, multHeckeIntegrand K J r (-u) ∂volume
      = ∫ v in (Neg.neg : logSpace K → logSpace K) '' unitBox K,
          multHeckeIntegrand K J r v ∂volume :=
        ((Measure.measurePreserving_neg (volume : Measure (logSpace K))).setIntegral_image_emb
          (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.neg (logSpace K)))
          (multHeckeIntegrand K J r) (unitBox K)).symm
    _ = ∫ u in unitBox K, multHeckeIntegrand K J r u ∂volume :=
        (neg_unitBox_isAddFundamentalDomain K).setIntegral_eq
          (unitBox_isAddFundamentalDomain K)
          (fun g u => multHeckeIntegrand_zlattice_invariant K J r g u)

-- pin: gapsw80_t7_multHeckeKernel (S_NumberField_exists_completedDedekindZeta_package.lean:2606)
def multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in unitBox K, multHeckeIntegrand K J (Real.log t / 2) u ∂volume

-- pin: gapsw80_t7_heckeKernel_closed_FE (S_NumberField_exists_completedDedekindZeta_package.lean:2609)
theorem heckeKernel_closed_functionalEquation (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ)
        * multHeckeKernel K (traceDualIdeal K I) t⁻¹ := by
  rw [heckeKernel_transformation_bridged K I ht, multHeckeKernel]
  congr 1

  rw [← setIntegral_neg_unitBox_eq K (traceDualIdeal K I) (Real.log t⁻¹ / 2)]
  rfl

-- pin: gapsw80_t7_covol_pos (S_NumberField_exists_completedDedekindZeta_package.lean:2621)
theorem covolume_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < ZLattice.covolume (mixedEmbedding.idealLattice K I) :=
  ZLattice.covolume_pos _ volume

-- pin: rpow_factor_h_feq (S_NumberField_exists_completedDedekindZeta_package.lean:2625)
theorem rpow_inv_pow_mul_sq {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    (x⁻¹ ^ n * c ^ 2) ^ (-(1/2) : ℝ) = x ^ ((n : ℝ)/2) * c⁻¹ := by
  have h1 : (x⁻¹ ^ n : ℝ) ^ (-(1/2) : ℝ) = x ^ ((n : ℝ)/2) := by
    rw [← Real.rpow_natCast x⁻¹, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
      ← Real.rpow_mul hx.le]
    ring_nf
  have h2 : (c ^ 2 : ℝ) ^ (-(1/2) : ℝ) = c⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc.le]
    norm_num
    exact Real.rpow_neg_one c
  rw [Real.mul_rpow (by positivity) (by positivity), h1, h2]

-- pin: gapsw80_t7_h_feq (S_NumberField_exists_completedDedekindZeta_package.lean:2637)
theorem heckeKernel_one_div_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      heckeKernel K I (1 / x)
        = (((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹
            * ((x ^ ((nK K : ℝ)/2) : ℝ) : ℂ))
          • multHeckeKernel K (traceDualIdeal K I) x := by
  intro x hx
  have hx' : (0:ℝ) < x := hx
  have h1x : (0:ℝ) < 1/x := by positivity
  rw [heckeKernel_closed_functionalEquation K I h1x, one_div, inv_inv, smul_eq_mul]
  congr 1
  rw [rpow_inv_pow_mul_sq hx' (covolume_pos K I)]
  push_cast
  ring

-- pin: gapsw80_t7_unitPart (S_NumberField_exists_completedDedekindZeta_package.lean:2652)
def unitPart (u : logSpace K) : realSpace K := fun w =>
  (∏ i : {w : InfinitePlace K // w ≠ w₀},
    (w (fundSystem K (equivFinRank.symm i) : K)) ^ (u i)) ^ 2

-- pin: unitPart_pos (S_NumberField_exists_completedDedekindZeta_package.lean:2656)
theorem unitPart_pos (u : logSpace K) (w : InfinitePlace K) :
    0 < unitPart K u w := by
  refine pow_pos (Finset.prod_pos fun i _ => ?_) 2
  exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _

-- pin: gapsw80_t7_yParam_mkParam_factor (S_NumberField_exists_completedDedekindZeta_package.lean:2661)
theorem yParam_mkParam_factor {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (w : InfinitePlace K) :
    yParam K (mkParam K (Real.log t / 2) u) w
      = t * unitPart K u w := by
  unfold yParam unitPart
  rw [expMapBasis_apply']
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mkParam_w₀,
    ← Real.exp_nat_mul, show (2:ℕ) * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by rw [mkParam_ne K i.2]

-- pin: continuous_unitPart (S_NumberField_exists_completedDedekindZeta_package.lean:2672)
theorem continuous_unitPart (w : InfinitePlace K) :
    Continuous fun u : logSpace K => unitPart K u w := by
  unfold unitPart
  refine (continuous_finsetProd _ fun i _ => ?_).pow 2
  exact (Real.continuous_const_rpow
    (pos_iff.mpr (by simp [fundSystem])).ne').comp (continuous_apply i)

-- pin: gapsw80_t7_unitPart_lower_bound (S_NumberField_exists_completedDedekindZeta_package.lean:2679)
theorem unitPart_lower_bound :
    ∃ c > 0, ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1),
      ∀ w, c ≤ unitPart K u w := by
  have hcpct : IsCompact (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hne : (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1).Nonempty :=
    ⟨0, fun i _ => by simp⟩

  have hw : ∀ w : InfinitePlace K, ∃ c > 0,
      ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1),
        c ≤ unitPart K u w := fun w => by
    obtain ⟨u₀, hu₀, hmin⟩ := hcpct.exists_isMinOn hne (continuous_unitPart K w).continuousOn
    exact ⟨unitPart K u₀ w, unitPart_pos K u₀ w, fun u hu => hmin hu⟩
  choose c hcpos hc using hw
  refine ⟨Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ c, ?_, fun u hu w => ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun w _ => hcpos w
  · exact (Finset.inf'_le c (Finset.mem_univ w)).trans (hc w u hu)

-- pin: isCompact_sum_sq_eq_one (S_NumberField_exists_completedDedekindZeta_package.lean:2697)
theorem isCompact_sum_sq_eq_one :
    IsCompact {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
  have hclosed : IsClosed {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbdd : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hle : w i ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)).trans_eq hw
    calc ‖w i‖ = |w i| := Real.norm_eq_abs _
      _ = √(w i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  exact (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, Metric.isBounded_closedBall.subset hbdd⟩)

-- pin: gapsw80_t7_idealGram_lower_bound (S_NumberField_exists_completedDedekindZeta_package.lean:2714)
theorem idealGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ lam > 0, ∀ v : Fin (nK K) → ℤ,
      lam * ∑ i, (v i : ℝ)^2 ≤ intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v := by
  set F : (Fin (nK K) → ℝ) → ℝ := fun w => w ⬝ᵥ (idealGram K I) *ᵥ w with hF
  have hFcont : Continuous F := by unfold F; fun_prop
  have hFscale : ∀ (c : ℝ) (w : Fin (nK K) → ℝ), F (c • w) = c^2 * F w := fun c w => by
    simp only [hF, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, sq, mul_assoc]
  have hSne : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1}.Nonempty := by
    refine ⟨Pi.single (⟨0, Module.finrank_pos⟩ : Fin (nK K)) 1, ?_⟩
    simp only [Set.mem_ofPred_eq, Pi.single_apply, ite_pow, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  obtain ⟨ww, hww, hmin⟩ := (isCompact_sum_sq_eq_one K).exists_isMinOn hSne hFcont.continuousOn
  have hne : ww ≠ 0 := fun habs => by rw [habs] at hww; simp at hww
  have hlam : 0 < F ww := by
    have h := (idealGram_posDef K I).dotProduct_mulVec_pos hne
    simpa [hF] using h
  refine ⟨F ww, hlam, fun v => ?_⟩
  by_cases hv : intCastVec v = 0
  · have hsum0 : ∑ i, (v i : ℝ)^2 = 0 := Finset.sum_eq_zero fun i _ => by
      have h0 : (v i : ℝ) = 0 := congr_fun hv i; rw [h0]; ring
    simp only [hsum0, mul_zero, hv, hF, Matrix.mulVec_zero, dotProduct_zero, le_refl]
  ·
    set s : ℝ := Real.sqrt (∑ i, (v i : ℝ)^2) with hs_def
    have hsumpos : 0 < ∑ i, (v i : ℝ)^2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ?_
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact ⟨i, Finset.mem_univ i, by
        simp only [intCastVec, Pi.zero_apply] at hi; positivity⟩
    have hspos : 0 < s := Real.sqrt_pos.mpr hsumpos
    have hs_sq : s^2 = ∑ i, (v i : ℝ)^2 := Real.sq_sqrt hsumpos.le
    have hmem : s⁻¹ • intCastVec v ∈ {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
      simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
        ← hs_sq, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hspos.ne')
    calc F ww * ∑ i, (v i : ℝ)^2
        = s^2 * F ww := by rw [hs_sq, mul_comm]
      _ ≤ s^2 * F (s⁻¹ • intCastVec v) :=
          mul_le_mul_of_nonneg_left (hmin hmem) (sq_nonneg s)
      _ = F (s • (s⁻¹ • intCastVec v)) := (hFscale s _).symm
      _ = intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v := by
          rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]

-- pin: multiIdealTheta_zero_term (S_NumberField_exists_completedDedekindZeta_package.lean:2757)
theorem multiIdealTheta_zero_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : InfinitePlace K → ℝ) :
    cexp ((-(π * (intCastVec (0 : Fin (nK K) → ℤ) ⬝ᵥ (scaledGram K I y)
      *ᵥ intCastVec 0)) : ℝ) : ℂ) = 1 := by
  simp [intCastVec, dotProduct]

-- pin: scaledGram_lower_bound (S_NumberField_exists_completedDedekindZeta_package.lean:2763)
theorem scaledGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℝ}
    {y : InfinitePlace K → ℝ} (hy : ∀ w, c ≤ y w) (v : Fin (nK K) → ℤ) :
    c * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)
      ≤ intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v := by
  have hGram1 : idealGram K I = scaledGram K I (fun _ => (1:ℝ)) := by
    rw [scaledGram_const_eq, one_smul]
  rw [hGram1, quadForm_scaledGram, quadForm_scaledGram, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => by
    rw [one_mul]; exact mul_le_mul_of_nonneg_right (hy w) (sq_nonneg _)

-- pin: one_le_sum_sq_of_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:2773)
theorem one_le_sum_sq_of_ne_zero {v : Fin (nK K) → ℤ} (hv : v ≠ 0) :
    (1 : ℝ) ≤ ∑ i, (v i : ℝ)^2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h1 : (1:ℝ) ≤ (v i : ℝ)^2 := by
    have : (1:ℤ) ≤ |v i| := Int.one_le_abs (by simpa using hi)
    have habs : (1:ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast this
    calc (1:ℝ) = (1:ℝ)^2 := (one_pow 2).symm
      _ ≤ |(v i:ℝ)|^2 := pow_le_pow_left₀ zero_le_one habs 2
      _ = (v i:ℝ)^2 := sq_abs _
  have h2 : (v i : ℝ)^2 ≤ ∑ j, (v j : ℝ)^2 :=
    Finset.single_le_sum (f := fun j => (v j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

-- pin: gapsw80_t7_summable_dom_gaussian (S_NumberField_exists_completedDedekindZeta_package.lean:2786)
theorem summable_dom_gaussian {lam : ℝ} (hlam : 0 < lam) :
    Summable fun v : Fin (nK K) → ℤ => rexp (-(π * lam * ∑ i, (v i : ℝ)^2)) := by
  have h := summable_exp_neg_mul_sum_sq_int (n := nK K) (c := π * lam) (by positivity)
  exact h.congr fun v => by ring_nf

-- pin: gapsw80_t7_theta_sub_one_exp_bound (S_NumberField_exists_completedDedekindZeta_package.lean:2791)
theorem multiIdealTheta_sub_one_exp_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C p, 0 < p ∧ ∀ {c : ℝ}, 1 ≤ c →
      ∀ {y : InfinitePlace K → ℝ}, (∀ w, c ≤ y w) →
        ‖multiIdealTheta K I y - 1‖ ≤ C * Real.exp (-(p * c)) := by
  obtain ⟨lam, hlam, hGram⟩ := idealGram_lower_bound K I
  set p := π * lam with hp_def
  have hp : 0 < p := by positivity
  have hsum : Summable fun v : Fin (nK K) → ℤ => rexp (-(p * ∑ i, (v i:ℝ)^2)) :=
    summable_dom_gaussian K hlam
  set C := rexp p * ∑' v : Fin (nK K) → ℤ, rexp (-(p * ∑ i, (v i:ℝ)^2)) with hC_def
  refine ⟨C, p, hp, fun {c} hc {y} hy => ?_⟩

  let f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v)) : ℝ) : ℂ)
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hterm : ∀ v, ‖f v‖ ≤ rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := fun v => by
    show ‖cexp _‖ ≤ _
    rw [Complex.norm_exp, Complex.ofReal_re]
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    calc p * c * ∑ i, (v i:ℝ)^2
        = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
      _ ≤ π * (c * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hGram v) (by linarith)) Real.pi_nonneg
      _ ≤ π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v) :=
          mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

  have hdom : ∀ v : Fin (nK K) → ℤ,
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p * ∑ i, (v i:ℝ)^2)) := fun v => by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hs : (0:ℝ) ≤ ∑ i, (v i : ℝ)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) hs]
  have hsplit : ∀ {v : Fin (nK K) → ℤ}, v ≠ 0 →
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
    intro v hv
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := one_le_sum_sq_of_ne_zero K hv
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) (sub_nonneg.mpr h1)]

  have hfullnorm : Summable fun v => ‖f v‖ :=
    hsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => (hterm v).trans (hdom v))
  have hfullsum : Summable f := hfullnorm.of_norm
  have htail_summable : Summable fun v : Fin (nK K) → ℤ =>
      if v = 0 then (0:ℝ) else rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := by
    refine hsum.of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · split_ifs <;> positivity
    · split_ifs with h
      · positivity
      · exact hdom v
  have hite_norm_summable : Summable fun v : Fin (nK K) → ℤ =>
      ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ := by
    refine hfullnorm.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    split_ifs <;> simp

  have hTheta : multiIdealTheta K I y - 1
      = ∑' v, if v = 0 then 0 else f v := by
    have heq : multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfullsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
  rw [hTheta]
  calc ‖∑' v, if v = 0 then 0 else f v‖
      ≤ ∑' v, ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ :=
        norm_tsum_le_tsum_norm hite_norm_summable
    _ ≤ ∑' v, if v = (0 : Fin (nK K) → ℤ) then (0:ℝ) else rexp (-(p*c*∑ i, (v i:ℝ)^2)) := by
        refine hite_norm_summable.tsum_le_tsum (fun v => ?_) htail_summable
        split_ifs with h
        · simp
        · exact hterm v
    _ ≤ ∑' v : Fin (nK K) → ℤ, rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
        refine htail_summable.tsum_le_tsum (fun v => ?_) (hsum.mul_left _)
        split_ifs with h
        · positivity
        · exact hsplit h
    _ = C * rexp (-(p * c)) := by
        rw [tsum_mul_left, hC_def,
          show -(p*(c-1)) = p + (-(p*c)) from by ring, Real.exp_add]
        ring

-- pin: continuous_theta_term (S_NumberField_exists_completedDedekindZeta_package.lean:2870)
theorem continuous_theta_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : Fin (nK K) → ℤ) :
    Continuous fun y : InfinitePlace K → ℝ =>
      cexp ((-(π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v)) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (Continuous.neg ?_))
  refine continuous_const.mul ?_
  simp only [quadForm_scaledGram]
  exact continuous_finsetSum _ fun w _ => (continuous_apply w).mul continuous_const

-- pin: gapsw80_t7_continuousOn_multiIdealTheta_ge (S_NumberField_exists_completedDedekindZeta_package.lean:2878)
theorem continuousOn_multiIdealTheta_ge (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : ℝ} (hc : 0 < c) :
    ContinuousOn (multiIdealTheta K I) {y | ∀ w, c ≤ y w} := by
  obtain ⟨lam, hlam, hGram⟩ := idealGram_lower_bound K I
  refine continuousOn_tsum (fun v => (continuous_theta_term K I v).continuousOn)
    (summable_dom_gaussian K (mul_pos hc hlam)) (fun v y hy => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

-- pin: gapsw80_t7_continuousOn_multiIdealTheta (S_NumberField_exists_completedDedekindZeta_package.lean:2893)
theorem continuousOn_multiIdealTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (multiIdealTheta K I) {y | ∀ w, 0 < y w} := by
  intro y hy
  set c := Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ (fun w => y w / 2) with hc_def
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr fun w _ => half_pos (hy w)
  have hy' : y ∈ {z | ∀ w, c ≤ z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans (half_le_self (hy w).le)
  have hopen : IsOpen {z : InfinitePlace K → ℝ | ∀ w, c < z w} := by
    have : {z : InfinitePlace K → ℝ | ∀ w, c < z w} = ⋂ w, {z | c < z w} := by
      ext z; simp [Set.mem_iInter]
    rw [this]; exact isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have hy'' : y ∈ {z | ∀ w, c < z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans_lt (by linarith [half_lt_self (hy w)])

  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_
    (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hy''))
  exact ((continuousOn_multiIdealTheta_ge K I hc) y hy').mono
    (fun z hz w => (hz w).le)

-- pin: continuous_mkParam (S_NumberField_exists_completedDedekindZeta_package.lean:2912)
theorem continuous_mkParam (r : ℝ) :
    Continuous fun u : logSpace K => mkParam K r u := by
  refine continuous_pi fun w => ?_
  unfold mkParam
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

-- pin: continuous_genericKernel_integrand (S_NumberField_exists_completedDedekindZeta_package.lean:2920)
theorem continuous_genericKernel_integrand (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (scale : realSpace K) (hscale : ∀ w, 0 < scale w) :
    Continuous fun u : logSpace K =>
      multiIdealTheta K I
        (scale * yParam K (mkParam K r u)) := by
  have hyP : Continuous fun u : logSpace K =>
      scale * yParam K (mkParam K r u) := by
    refine continuous_pi fun w => ?_
    exact continuous_const.mul
      (((continuous_apply w).comp ((continuous_expMapBasis K).comp (continuous_mkParam K r))).pow 2)
  refine ContinuousOn.comp_continuous (continuousOn_multiIdealTheta K I) hyP ?_
  exact fun u w => mul_pos (hscale w) (yParam_pos K _ w)

-- pin: volume_unitBox_eq_one (S_NumberField_exists_completedDedekindZeta_package.lean:2933)
theorem volume_unitBox_eq_one : volume (unitBox K) = 1 := by
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

-- pin: volume_unitBox_lt_top (S_NumberField_exists_completedDedekindZeta_package.lean:2937)
theorem volume_unitBox_lt_top : volume (unitBox K) < ⊤ := by
  rw [volume_unitBox_eq_one]; exact ENNReal.one_lt_top

-- pin: gapsw80_t7_continuousOn_genericKernel (S_NumberField_exists_completedDedekindZeta_package.lean:2940)
theorem continuousOn_genericKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ContinuousOn (fun t : ℝ => ∫ u in unitBox K,
      multiIdealTheta K I
        (scale * yParam K (mkParam K (Real.log t / 2) u)) ∂volume)
      (Set.Ioi 0) := by
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  obtain ⟨cK, hcK, hLB⟩ := unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := multiIdealTheta_sub_one_exp_bound K I
  have hfin : IsFiniteMeasure (volume.restrict (unitBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitBox_lt_top K⟩

  intro t₀ ht₀
  have ht₀' : (0:ℝ) < t₀ := ht₀
  set s := Set.Icc (t₀/2) (t₀+1) with hs_def
  have hsnhds : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hssub : s ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le (by linarith) ht.1
  set c₀ : ℝ := cK * (t₀/2)
  have hc₀ : 0 < c₀ := mul_pos hcK (by linarith)
  obtain ⟨lam, hlam, hGram⟩ := idealGram_lower_bound K I
  set M : ℝ := ∑' v : Fin (nK K) → ℤ, rexp (-(π * (c₀ * lam) * ∑ i, (v i:ℝ)^2)) with hM_def
  have hMsum := summable_dom_gaussian K (mul_pos hc₀ hlam)

  have hy_lb : ∀ t ∈ s, ∀ u ∈ unitBox K, ∀ w,
      c₀ ≤ (scale * yParam K (mkParam K (Real.log t / 2) u)) w := by
    intro t ht u hu w
    have ht' : (0:ℝ) < t := hssub ht
    rw [Pi.mul_apply, yParam_mkParam_factor K ht']
    have huIcc : u ∈ (Set.univ.pi fun _ : {w // w ≠ w₀} => Icc (0:ℝ) 1) :=
      fun i hi => Ico_subset_Icc_self (hu i hi)
    have huP : 0 < unitPart K u w := unitPart_pos K u w
    calc c₀ = cK * (t₀/2) := rfl
      _ ≤ unitPart K u w * t :=
          mul_le_mul (hLB u huIcc w) ht.1 (by linarith) huP.le
      _ = 1 * (t * unitPart K u w) := by ring
      _ ≤ scale w * (t * unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hTheta_bound : ∀ t ∈ s, ∀ u ∈ unitBox K,
      ‖multiIdealTheta K I
        (scale * yParam K (mkParam K (Real.log t / 2) u))‖ ≤ M := by
    intro t ht u hu
    unfold multiIdealTheta
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact hMsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => by
        rw [Complex.norm_exp, Complex.ofReal_re]
        exact Real.exp_le_exp.mpr (neg_le_neg (by
          calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
              = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
            _ ≤ π * (c₀ * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
            _ ≤ π * (intCastVec v ⬝ᵥ (scaledGram K I _) *ᵥ intCastVec v) :=
                mul_le_mul_of_nonneg_left
                  (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg)))
    · refine (Summable.tsum_le_tsum (fun v => ?_) ?_ hMsum)
      · rw [Complex.norm_exp, Complex.ofReal_re]
        exact Real.exp_le_exp.mpr (neg_le_neg (by
          calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
              = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
            _ ≤ π * (c₀ * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
            _ ≤ π * (intCastVec v ⬝ᵥ (scaledGram K I _) *ᵥ intCastVec v) :=
                mul_le_mul_of_nonneg_left
                  (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg))
      · exact hMsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => by
          rw [Complex.norm_exp, Complex.ofReal_re]
          exact Real.exp_le_exp.mpr (neg_le_neg (by
            calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
                = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
              _ ≤ π * (c₀ * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
              _ ≤ π * (intCastVec v ⬝ᵥ (scaledGram K I _) *ᵥ intCastVec v) :=
                  mul_le_mul_of_nonneg_left
                    (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg)))

  have hcontOn_s : ContinuousOn
      (fun t => ∫ u in unitBox K,
        multiIdealTheta K I
          (scale * yParam K (mkParam K (Real.log t / 2) u)) ∂volume) s := by
    refine continuousOn_of_dominated (bound := fun _ => M)
      (μ := volume.restrict (unitBox K)) ?_ ?_ ?_ ?_
    · intro t _
      exact (continuous_genericKernel_integrand K I _ scale hscale').aestronglyMeasurable.restrict
    · intro t ht
      exact ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hTheta_bound t ht u hu)
    · exact integrable_const M
    · refine ae_of_all _ fun u => ?_

      have hmk : ContinuousOn (fun t : ℝ => mkParam K (Real.log t / 2) u) s := by
        refine continuousOn_pi.mpr fun w' => ?_
        unfold mkParam
        split_ifs
        · exact (Real.continuousOn_log.mono (hssub.trans fun x hx => ne_of_gt hx)).div_const 2
        · exact continuousOn_const
      have hyP : ContinuousOn
          (fun t : ℝ => scale * yParam K (mkParam K (Real.log t / 2) u)) s := by
        refine ContinuousOn.mul continuousOn_const ?_
        refine continuousOn_pi.mpr fun w => ?_
        unfold yParam
        exact (((continuous_apply w).comp (continuous_expMapBasis K)).continuousOn.comp hmk
          (Set.mapsTo_univ _ _)).pow 2
      exact (continuousOn_multiIdealTheta K I).comp hyP
        (fun t ht w => mul_pos (hscale' w) (yParam_pos K _ w))
  exact (hcontOn_s t₀ ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds hsnhds)

-- pin: gapsw80_t7_continuousOn_heckeKernel (S_NumberField_exists_completedDedekindZeta_package.lean:3050)
theorem continuousOn_heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (heckeKernel K I) (Set.Ioi 0) := by
  have h := continuousOn_genericKernel K I 1 (fun _ => le_refl 1)
  simp only [one_mul] at h
  exact h

-- pin: gapsw80_t7_continuousOn_multHeckeKernel (S_NumberField_exists_completedDedekindZeta_package.lean:3056)
theorem continuousOn_multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (multHeckeKernel K J) (Set.Ioi 0) := by
  have h := continuousOn_genericKernel K J (multSq K)
    (fun _ => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))
  exact h

-- pin: gapsw80_t7_genericKernel_sub_one_isBigO_exp (S_NumberField_exists_completedDedekindZeta_package.lean:3062)
theorem genericKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ∃ p > 0, (fun t => (∫ u in unitBox K,
        multiIdealTheta K I
          (scale * yParam K (mkParam K (Real.log t / 2) u)) ∂volume) - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨cK, hcK, hLB⟩ := unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := multiIdealTheta_sub_one_exp_bound K I
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  refine ⟨p * cK, by positivity, IsBigO.of_bound (max C 0) ?_⟩
  filter_upwards [eventually_ge_atTop cK⁻¹] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hcK) ht
  have hcKt : 1 ≤ cK * t := by rw [mul_comm]; exact (inv_le_iff_one_le_mul₀ hcK).mp ht
  set G : logSpace K → ℂ := fun u => multiIdealTheta K I
      (scale * yParam K (mkParam K (Real.log t / 2) u)) with hG_def

  have hptw : ∀ u ∈ unitBox K, ‖G u - 1‖ ≤ C * Real.exp (-(p * (cK * t))) := by
    intro u hu
    refine hbound hcKt (fun w => ?_)
    rw [Pi.mul_apply, yParam_mkParam_factor K ht0]
    have huIcc : u ∈ (Set.univ.pi fun _ : {w // w ≠ w₀} => Icc (0:ℝ) 1) :=
      fun i hi => Ico_subset_Icc_self (hu i hi)
    have huP : 0 < unitPart K u w := unitPart_pos K u w
    calc cK * t ≤ unitPart K u w * t :=
          mul_le_mul_of_nonneg_right (hLB u huIcc w) ht0.le
      _ = 1 * (t * unitPart K u w) := by ring
      _ ≤ scale w * (t * unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hGcont : Continuous G := continuous_genericKernel_integrand K I _ scale hscale'
  have hfin : IsFiniteMeasure (volume.restrict (unitBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitBox_lt_top K⟩
  have hintconst : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (unitBox K) volume := by
    simp only [IntegrableOn, integrable_const_iff]; exact Or.inr hfin
  have hint : IntegrableOn (fun u => G u - 1) (unitBox K) volume := by
    refine ⟨(hGcont.sub continuous_const).aestronglyMeasurable.restrict, ?_⟩
    refine HasFiniteIntegral.mono' ?_
      (ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hptw u hu))
    exact (integrable_const (C * Real.exp (-(p * (cK * t))))).hasFiniteIntegral

  have heq : (∫ u in unitBox K, G u ∂volume) - 1
      = ∫ u in unitBox K, (G u - 1) ∂volume := by
    have hintG : IntegrableOn G (unitBox K) volume :=
      (hint.add hintconst).congr_fun
        (fun u _ => by simp only [Pi.add_apply]; ring)
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    rw [integral_sub hintG hintconst, setIntegral_const]
    simp [measureReal_def, volume_unitBox_eq_one]

  rw [Real.norm_of_nonneg (Real.exp_pos _).le,
    show -(p * cK) * t = -(p * (cK * t)) from by ring]
  calc ‖(∫ u in unitBox K, G u ∂volume) - 1‖
      = ‖∫ u in unitBox K, (G u - 1) ∂volume‖ := by rw [heq]
    _ ≤ (C * Real.exp (-(p * (cK * t)))) * (volume (unitBox K)).toReal :=
        norm_setIntegral_le_of_norm_le_const (volume_unitBox_lt_top K) hptw
    _ = C * Real.exp (-(p * (cK * t))) := by
        rw [volume_unitBox_eq_one, ENNReal.toReal_one, mul_one]
    _ ≤ max C 0 * Real.exp (-(p * (cK * t))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

-- pin: gapsw80_t7_heckeKernel_sub_one_isBigO_exp (S_NumberField_exists_completedDedekindZeta_package.lean:3123)
theorem heckeKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => heckeKernel K I t - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := genericKernel_sub_one_isBigO_exp K I 1 (fun _ => le_refl 1)
  refine ⟨p, hp, hO.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl⟩
  simp only [one_mul, heckeKernel]

-- pin: gapsw80_t7_hf_top (S_NumberField_exists_completedDedekindZeta_package.lean:3130)
theorem heckeKernel_sub_one_isBigO_rpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => heckeKernel K I t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := heckeKernel_sub_one_isBigO_exp K I
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

-- pin: gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp (S_NumberField_exists_completedDedekindZeta_package.lean:3135)
theorem multHeckeKernel_sub_one_isBigO_exp (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => multHeckeKernel K J t - 1)
      =O[atTop] fun t => Real.exp (-p * t) :=
  genericKernel_sub_one_isBigO_exp K J (multSq K)
    (fun _ => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))

-- pin: gapsw80_t7_hg_top (S_NumberField_exists_completedDedekindZeta_package.lean:3141)
theorem multHeckeKernel_sub_one_isBigO_rpow (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => multHeckeKernel K J t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := multHeckeKernel_sub_one_isBigO_exp K J
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

-- pin: gapsw80_t7_heckeWeakFEPair (S_NumberField_exists_completedDedekindZeta_package.lean:3148)
def heckeWeakFEPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : WeakFEPair ℂ where
  f := heckeKernel K I
  g := multHeckeKernel K (traceDualIdeal K I)
  k := (nK K : ℝ) / 2
  ε := ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹
  f₀ := 1
  g₀ := 1
  hk := div_pos (by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ K)) two_pos
  hε := by
    refine inv_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
    exact (covolume_pos K I).ne'
  hf_int := (continuousOn_heckeKernel K I).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_multHeckeKernel K _).locallyIntegrableOn measurableSet_Ioi
  h_feq := by
    intro x hx
    have h := heckeKernel_one_div_eq K I x hx
    simp only [smul_eq_mul] at h ⊢
    convert h using 2
  hf_top := heckeKernel_sub_one_isBigO_rpow K I
  hg_top := multHeckeKernel_sub_one_isBigO_rpow K _

end ClosedFEWeakPair

end

end NumberField.CompletedDedekindZeta
