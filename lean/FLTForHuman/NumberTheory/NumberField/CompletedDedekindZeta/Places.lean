/-
  Archimedean places, the scaling matrix, the scaled Gram matrix, and the Hecke
  theta kernel.

  This is wave 3 of the `completedDedekindZeta` package.  It introduces the place
  index `placeOf` of

    index K = {real places} ⊕ ({complex places} × Fin 2),

  the diagonal scaling matrix `Dscale`, the scaled Gram matrix
  `scaledGram K I y = (coordMatrix K I)ᵀ * Dscale K y * coordMatrix K I` of a
  fractional ideal `I`, its determinant `det_scaledGram` (the product of the
  `y w ^ mult w` and the square of the covolume) and its positive definiteness, and
  the norm-at-place identity `sum_sq_repr_fiber_eq_normAtPlace_sq` that turns the
  quadratic form of `scaledGram` into `∑ w, y w * normAtPlace w x ^ 2`.  It then
  defines the multi-variable theta series `multiIdealTheta`, its Poisson
  transformation law `multiIdealTheta_transformation`, the unit scaling
  `unitSqScale`/`unitSMulLatticeEquiv`, the `yParam`/`mkParam` coordinates on the
  cone, and the Hecke theta kernel `heckeKernel` with its raw transformation law.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:1543–1964`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.Gapsw80T4MultiVarIdealThetaTransformation` and
  `FLT.Gapsw80T5HeckeThetaKernel` blocks.  The pin's obligation prefixes and
  per-obligation namespaces are dropped; every declaration carries the pin's own
  name and line in the `-- pin:` comment above it (playbook §2.3, §4).

  The pin's file-wide `set_option maxHeartbeats 6400000` is not transcribed; the
  port's global cap is `4000000`.  Proofs are adapted to mathlib `v4.34.0`: the
  `v4.34.0` deprecations `if_pos`/`if_neg`/`dif_pos`/`dif_neg` become
  `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`, unused `simp`
  arguments are dropped, and `omit [NumberField K] in` silences the
  unused-section-variable linter on the four declarations whose statement never
  mentions the `K`-instance.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Poisson
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

namespace NumberField.CompletedDedekindZeta

open Matrix
open Module
open WithLp
open MeasureTheory
open Real
open NumberField.InfinitePlace
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open _root_.Complex hiding exp
open scoped Classical
open scoped RealInnerProductSpace
open scoped nonZeroDivisors

noncomputable section

/-! ### Archimedean places, the scaling matrix and the scaled Gram matrix -/

section PlacesAndScaling

variable (K : Type) [Field K] [NumberField K]


-- pin: gapsw80_t4_placeOf (S_NumberField_exists_completedDedekindZeta_package.lean:1600)
def placeOf : index K → InfinitePlace K :=
  Sum.elim (fun w => (w : InfinitePlace K)) (fun p => (p.1 : InfinitePlace K))

omit [NumberField K] in
-- pin: placeOf_inl (S_NumberField_exists_completedDedekindZeta_package.lean:1603)
@[scoped simp] theorem placeOf_inl (w : {w : InfinitePlace K // IsReal w}) :
    placeOf K (Sum.inl w) = (w : InfinitePlace K) := rfl

omit [NumberField K] in
-- pin: placeOf_inr (S_NumberField_exists_completedDedekindZeta_package.lean:1606)
@[scoped simp] theorem placeOf_inr (p : {w : InfinitePlace K // IsComplex w} × Fin 2) :
    placeOf K (Sum.inr p) = (p.1 : InfinitePlace K) := rfl

-- pin: gapsw80_t4_Dscale (S_NumberField_exists_completedDedekindZeta_package.lean:1609)
def Dscale (y : InfinitePlace K → ℝ) : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.diagonal fun i => y (placeOf K ((indexEquivFin K).symm i))

-- pin: Dscale_posDef (S_NumberField_exists_completedDedekindZeta_package.lean:1612)
theorem Dscale_posDef {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (Dscale K y).PosDef :=
  Matrix.PosDef.diagonal fun _ => hy _

-- pin: fiber_placeOf_isReal (S_NumberField_exists_completedDedekindZeta_package.lean:1616)
theorem fiber_placeOf_isReal {w : InfinitePlace K} (hw : IsReal w) :
    (Finset.univ.filter fun j => placeOf K j = w)
      = {Sum.inl ⟨w, hw⟩} := by
  ext j
  rcases j with ⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inl,
      Finset.mem_singleton, Sum.inl.injEq, Subtype.mk.injEq]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inr,
      Finset.mem_singleton]
    exact iff_of_false (fun h => (not_isReal_iff_isComplex.mpr hv) (h ▸ hw)) (by simp)

-- pin: fiber_placeOf_isComplex (S_NumberField_exists_completedDedekindZeta_package.lean:1627)
theorem fiber_placeOf_isComplex {w : InfinitePlace K} (hw : IsComplex w) :
    (Finset.univ.filter fun j => placeOf K j = w)
      = {Sum.inr (⟨w, hw⟩, 0), Sum.inr (⟨w, hw⟩, 1)} := by
  ext j
  rcases j with ⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inl,
      Finset.mem_insert, Finset.mem_singleton]
    exact iff_of_false (fun h => (not_isComplex_iff_isReal.mpr hv) (h ▸ hw)) (by simp)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inr,
      Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, Prod.mk.injEq,
      Subtype.mk.injEq]
    constructor
    · rintro rfl; fin_cases k <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

-- pin: gapsw80_t4_det_Dscale (S_NumberField_exists_completedDedekindZeta_package.lean:1642)
theorem det_Dscale (y : InfinitePlace K → ℝ) :
    (Dscale K y).det = ∏ w : InfinitePlace K, y w ^ mult w := by
  rw [Dscale, Matrix.det_diagonal,
    Fintype.prod_equiv (indexEquivFin K).symm _ (fun j => y (placeOf K j))
      (fun i => by simp),
    ← Finset.prod_fiberwise Finset.univ (fun j => placeOf K j)
      (fun j => y (placeOf K j))]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_pow_card fun j hj => by
      rw [Finset.mem_filter] at hj; rw [hj.2]]
  congr 1
  rcases isReal_or_isComplex w with hw | hw
  · rw [mult, ite_eq_left hw, fiber_placeOf_isReal K hw, Finset.card_singleton]
  · rw [mult, ite_eq_right (not_isReal_iff_isComplex.mpr hw), fiber_placeOf_isComplex K hw,
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]


variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
-- pin: gapsw80_t4_scaledGram (S_NumberField_exists_completedDedekindZeta_package.lean:1660)
def scaledGram (y : InfinitePlace K → ℝ) :
    Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  (coordMatrix K I)ᵀ * Dscale K y * coordMatrix K I

-- pin: det_coordMatrix_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:1664)
theorem det_coordMatrix_ne_zero : (coordMatrix K I).det ≠ 0 := fun h =>
  (ZLattice.covolume_pos (mixedEmbedding.idealLattice K I) MeasureTheory.volume).ne'
    ((abs_det_coordMatrix K I).symm.trans (by rw [h, abs_zero]))

-- pin: isUnit_coordMatrix (S_NumberField_exists_completedDedekindZeta_package.lean:1668)
theorem isUnit_coordMatrix : IsUnit (coordMatrix K I) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_coordMatrix_ne_zero K I))

-- pin: gapsw80_t4_scaledGram_posDef (S_NumberField_exists_completedDedekindZeta_package.lean:1671)
theorem scaledGram_posDef {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (scaledGram K I y).PosDef := by
  have h := (Dscale_posDef K hy).conjTranspose_mul_mul_same (B := coordMatrix K I)
    (Matrix.mulVec_injective_of_isUnit (isUnit_coordMatrix K I))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

-- pin: gapsw80_t4_det_scaledGram (S_NumberField_exists_completedDedekindZeta_package.lean:1677)
theorem det_scaledGram (y : InfinitePlace K → ℝ) :
    (scaledGram K I y).det
      = (∏ w : InfinitePlace K, y w ^ mult w)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2 := by
  rw [scaledGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_Dscale, mul_comm (coordMatrix K I).det, mul_assoc, ← sq, ← sq_abs,
    abs_det_coordMatrix]

-- pin: sum_sq_repr_fiber_eq_normAtPlace_sq (S_NumberField_exists_completedDedekindZeta_package.lean:1685)
theorem sum_sq_repr_fiber_eq_normAtPlace_sq (x : mixedSpace K) (w : InfinitePlace K) :
    ∑ j ∈ Finset.univ.filter (fun j => placeOf K j = w),
        ((mixedEmbedding.stdBasis K).repr x j) ^ 2
      = normAtPlace w x ^ 2 := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, fiber_placeOf_isReal K hw, Finset.sum_singleton,
      stdBasis_apply_isReal, Real.norm_eq_abs, sq_abs]
  · rw [normAtPlace_apply_of_isComplex hw, fiber_placeOf_isComplex K hw,
      Finset.sum_insert (by simp), Finset.sum_singleton,
      stdBasis_apply_isComplex_fst, stdBasis_apply_isComplex_snd,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

-- pin: coordMatrix_mulVec_eq_repr (S_NumberField_exists_completedDedekindZeta_package.lean:1698)
theorem coordMatrix_mulVec_eq_repr (v : Fin (nK K) → ℤ) (i : Fin (nK K)) :
    ((coordMatrix K I) *ᵥ intCastVec v) i
      = (mixedEmbedding.stdBasis K).repr (idealLatticeEquiv K I v : mixedSpace K) ((indexEquivFin K).symm i) := by

  have hRHS : (mixedEmbedding.stdBasis K).repr (idealLatticeEquiv K I v : mixedSpace K) ((indexEquivFin K).symm i)
      = ∑ j, (v j : ℝ) * (stdBasisFin K).repr
          (fractionalIdealLatticeBasis K I ((chooseBasisIndexEquivFin K I).symm j)) i := by
    rw [show (mixedEmbedding.stdBasis K).repr (idealLatticeEquiv K I v : mixedSpace K) ((indexEquivFin K).symm i)
          = (stdBasisFin K).repr (idealLatticeEquiv K I v : mixedSpace K) i by
        simp only [stdBasisFin, Basis.repr_reindex_apply],
      idealLatticeEquiv_apply, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hRHS, coordMatrix_eq_toMatrix, Matrix.mulVec]
  simp only [dotProduct, Basis.toMatrix_apply, idealLatticeBasisInt_apply, intCastVec]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

-- pin: gapsw80_t4_quadForm_scaledGram (S_NumberField_exists_completedDedekindZeta_package.lean:1715)
theorem quadForm_scaledGram (y : InfinitePlace K → ℝ) (v : Fin (nK K) → ℤ) :
    intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v
      = ∑ w : InfinitePlace K, y w * normAtPlace w (idealLatticeEquiv K I v : mixedSpace K) ^ 2 := by

  have hstep1 : intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v
      = ((coordMatrix K I) *ᵥ intCastVec v) ⬝ᵥ
          (Dscale K y) *ᵥ ((coordMatrix K I) *ᵥ intCastVec v) := by
    rw [scaledGram, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (intCastVec v) (coordMatrix K I)ᵀ,
      Matrix.vecMul_transpose]

  rw [hstep1]
  have hstep2 : ∀ u : Fin (nK K) → ℝ, u ⬝ᵥ (Dscale K y) *ᵥ u
      = ∑ i, y (placeOf K ((indexEquivFin K).symm i)) * u i ^ 2 := fun u => by
    simp only [dotProduct, Dscale, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hstep2,
    Fintype.sum_equiv (indexEquivFin K).symm _
      (fun j => y (placeOf K j)
        * ((mixedEmbedding.stdBasis K).repr (idealLatticeEquiv K I v : mixedSpace K) j) ^ 2)
      (fun i => by rw [coordMatrix_mulVec_eq_repr K I v i]),
    ← Finset.sum_fiberwise Finset.univ (fun j => placeOf K j)
      (fun j => y (placeOf K j)
        * ((mixedEmbedding.stdBasis K).repr (idealLatticeEquiv K I v : mixedSpace K) j) ^ 2)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_sq_repr_fiber_eq_normAtPlace_sq K (idealLatticeEquiv K I v : mixedSpace K) w,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => by
    rw [Finset.mem_filter] at hj; rw [hj.2]

-- pin: gapsw80_t4_multiIdealTheta (S_NumberField_exists_completedDedekindZeta_package.lean:1745)
def multiIdealTheta (y : InfinitePlace K → ℝ) : ℂ :=
  ∑' v : Fin (nK K) → ℤ, cexp ((-(π *
    (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v)) : ℝ) : ℂ)

-- pin: gapsw80_t4_multiIdealTheta_eq_latticeSum (S_NumberField_exists_completedDedekindZeta_package.lean:1749)
theorem multiIdealTheta_eq_latticeSum (y : InfinitePlace K → ℝ) :
    multiIdealTheta K I y
      = ∑' x : mixedEmbedding.idealLattice K I,
          cexp ((-(π *
            ∑ w : InfinitePlace K, y w * normAtPlace w (x : mixedSpace K) ^ 2) : ℝ) : ℂ) := by
  unfold multiIdealTheta
  rw [← (idealLatticeEquiv K I).toEquiv.tsum_eq]
  exact tsum_congr fun v => by rw [quadForm_scaledGram]; rfl

-- pin: gapsw80_t4_scaledGram_const_eq (S_NumberField_exists_completedDedekindZeta_package.lean:1758)
theorem scaledGram_const_eq (t : ℝ) :
    scaledGram K I (fun _ => t) = t • idealGram K I := by
  have hD : Dscale K (fun _ => t) = Matrix.diagonal (fun _ => t) := rfl
  rw [scaledGram, idealGram_eq_transpose_mul, hD,
    show (Matrix.diagonal (fun _ : Fin (nK K) => t) : Matrix _ _ ℝ) = t • 1 by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h],
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

-- pin: gapsw80_t4_multiIdealTheta_transformation (S_NumberField_exists_completedDedekindZeta_package.lean:1766)
theorem multiIdealTheta_transformation {y : InfinitePlace K → ℝ}
    (hy : ∀ w, 0 < y w) :
    multiIdealTheta K I y
      = ((((∏ w : InfinitePlace K, y w ^ mult w)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin (nK K) → ℤ,
          cexp ((-(π *
            (intCastVec w ⬝ᵥ (scaledGram K I y)⁻¹ *ᵥ intCastVec w)) : ℝ) : ℂ) := by
  have h := poissonSummation_posDef (scaledGram K I y)
    (scaledGram_posDef K I hy) one_pos
  rw [det_scaledGram, one_pow, one_mul] at h
  simp only [mul_one, div_one] at h
  exact h

-- pin: gapsw80_t4_scaledGram_inv_eq (S_NumberField_exists_completedDedekindZeta_package.lean:1780)
theorem scaledGram_inv_eq {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (scaledGram K I y)⁻¹
      = (coordMatrix K I)⁻¹ * Dscale K (fun w => (y w)⁻¹)
          * ((coordMatrix K I)ᵀ)⁻¹ := by
  have hD : Dscale K (fun w => (y w)⁻¹) = (Dscale K y)⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [show Dscale K y
          = Matrix.diagonal fun i => y (placeOf K ((indexEquivFin K).symm i)) from rfl,
      show Dscale K (fun w => (y w)⁻¹)
          = Matrix.diagonal fun i => (y (placeOf K ((indexEquivFin K).symm i)))⁻¹ from rfl,
      Matrix.diagonal_mul_diagonal, show (1 : Matrix (Fin (nK K)) (Fin (nK K)) ℝ)
          = Matrix.diagonal 1 from (Matrix.diagonal_one).symm]
    exact Matrix.diagonal_eq_diagonal_iff.mpr fun i => mul_inv_cancel₀ (hy _).ne'
  rw [hD, scaledGram, Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.mul_inv_rev]


end PlacesAndScaling

/-! ### The Hecke theta kernel -/

section HeckeThetaKernel

variable (K : Type) [Field K] [NumberField K]
-- pin: gapsw80_t5_unitSqScale (S_NumberField_exists_completedDedekindZeta_package.lean:1821)
def unitSqScale (η : (𝓞 K)ˣ) : realSpace K := fun w => (w (η : K)) ^ 2

omit [NumberField K] in
-- pin: normAtPlace_unitSMul (S_NumberField_exists_completedDedekindZeta_package.lean:1823)
theorem normAtPlace_unitSMul (η : (𝓞 K)ˣ) (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (η • x) = w (η : K) * normAtPlace w x := by
  rw [unitSMul_smul, map_mul, normAtPlace_apply]

omit [NumberField K] in
-- pin: unitSMul_mem_idealLattice (S_NumberField_exists_completedDedekindZeta_package.lean:1827)
theorem unitSMul_mem_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (η : (𝓞 K)ˣ)
    {x : mixedSpace K} (hx : x ∈ mixedEmbedding.idealLattice K I) :
    η • x ∈ mixedEmbedding.idealLattice K I := by
  obtain ⟨a, ha, rfl⟩ := (mem_idealLattice K I).mp hx
  refine (mem_idealLattice K I).mpr ⟨(η : 𝓞 K) • a, Submodule.smul_mem _ _ ha, ?_⟩
  rw [unitSMul_smul, Algebra.smul_def, map_mul]

-- pin: gapsw80_t5_unitSMulLatticeEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:1834)
def unitSMulLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (η : (𝓞 K)ˣ) :
    mixedEmbedding.idealLattice K I ≃ mixedEmbedding.idealLattice K I where
  toFun x := ⟨η • (x : mixedSpace K), unitSMul_mem_idealLattice K I η x.2⟩
  invFun x := ⟨η⁻¹ • (x : mixedSpace K), unitSMul_mem_idealLattice K I η⁻¹ x.2⟩
  left_inv x := by
    simp only [inv_smul_smul]
  right_inv x := by
    simp only [smul_inv_smul]

-- pin: gapsw80_t5_multiIdealTheta_unitSq_smul (S_NumberField_exists_completedDedekindZeta_package.lean:1843)
theorem multiIdealTheta_unitSq_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (η : (𝓞 K)ˣ) (y : InfinitePlace K → ℝ) :
    multiIdealTheta K I (unitSqScale K η * y)
      = multiIdealTheta K I y := by
  rw [multiIdealTheta_eq_latticeSum, multiIdealTheta_eq_latticeSum]
  conv_rhs => rw [← (unitSMulLatticeEquiv K I η).tsum_eq]
  refine tsum_congr fun x => ?_
  have hsum : ∑ w : InfinitePlace K,
        (unitSqScale K η * y) w * normAtPlace w (x : mixedSpace K) ^ 2
      = ∑ w : InfinitePlace K,
        y w * normAtPlace w ((unitSMulLatticeEquiv K I η x : mixedSpace K)) ^ 2 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    show unitSqScale K η w * y w * normAtPlace w (x : mixedSpace K) ^ 2
      = y w * normAtPlace w (η • (x : mixedSpace K)) ^ 2
    rw [normAtPlace_unitSMul, mul_pow, unitSqScale]
    ring
  rw [hsum]

-- pin: gapsw80_t5_yParam (S_NumberField_exists_completedDedekindZeta_package.lean:1861)
def yParam (c : realSpace K) : realSpace K := fun w => (expMapBasis c w) ^ 2

-- pin: yParam_pos (S_NumberField_exists_completedDedekindZeta_package.lean:1863)
theorem yParam_pos (c : realSpace K) (w : InfinitePlace K) :
    0 < yParam K c w := pow_pos (expMapBasis_pos c w) 2

-- pin: gapsw80_t5_prod_yParam_mult (S_NumberField_exists_completedDedekindZeta_package.lean:1866)
theorem prod_yParam_mult (c : realSpace K) :
    ∏ w : InfinitePlace K, (yParam K c w) ^ mult w
      = Real.exp (c w₀) ^ (2 * nK K) := by
  unfold yParam
  simp_rw [← pow_mul, mul_comm 2, pow_mul]
  rw [Finset.prod_pow, prod_expMapBasis_pow, ← pow_mul, mul_comm]

-- pin: expMapBasis_neg (S_NumberField_exists_completedDedekindZeta_package.lean:1873)
theorem expMapBasis_neg (c : realSpace K) (w : InfinitePlace K) :
    expMapBasis (-c) w = (expMapBasis c w)⁻¹ := by
  rw [expMapBasis_apply, expMapBasis_apply, _root_.map_neg, expMap_apply, expMap_apply,
    Pi.neg_apply, mul_neg, Real.exp_neg]

-- pin: gapsw80_t5_yParam_neg (S_NumberField_exists_completedDedekindZeta_package.lean:1878)
theorem yParam_neg (c : realSpace K) (w : InfinitePlace K) :
    yParam K (-c) w = (yParam K c w)⁻¹ := by
  unfold yParam
  rw [expMapBasis_neg, inv_pow]

-- pin: expMapBasis_add_single (S_NumberField_exists_completedDedekindZeta_package.lean:1883)
theorem expMapBasis_add_single {i : InfinitePlace K} (hi : i ≠ w₀) (c : realSpace K)
    (w : InfinitePlace K) :
    expMapBasis (c + Pi.single i 1) w
      = expMapBasis c w * w (fundSystem K (equivFinRank.symm ⟨i, hi⟩) : K) := by

  rw [expMapBasis_apply, expMapBasis_apply, map_add, expMap_add, Pi.mul_apply,
    show ((completeBasis K).equivFun.symm) (Pi.single i 1) = completeBasis K i by
      simp [Basis.equivFun_symm_apply, Pi.single_apply],
    completeBasis_apply_of_ne K ⟨i, hi⟩,
    show expMap (expMap.symm
        (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))))) w
      = normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) w from
      congrFun (expMap.right_inv (by simp [expMap_target, pos_at_place])) w,
    normAtAllPlaces_apply, normAtPlace_apply]

-- pin: gapsw80_t5_yParam_add_single (S_NumberField_exists_completedDedekindZeta_package.lean:1898)
theorem yParam_add_single {i : InfinitePlace K} (hi : i ≠ w₀) (c : realSpace K) :
    yParam K (c + Pi.single i 1)
      = unitSqScale K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))
          * yParam K c := by
  ext w
  unfold yParam unitSqScale
  rw [expMapBasis_add_single K hi, mul_pow, Pi.mul_apply, mul_comm]

-- pin: gapsw80_t5_mkParam (S_NumberField_exists_completedDedekindZeta_package.lean:1906)
def mkParam (r : ℝ) (u : logSpace K) : realSpace K :=
  fun w => if h : w = w₀ then r else u ⟨w, h⟩

-- pin: mkParam_w₀ (S_NumberField_exists_completedDedekindZeta_package.lean:1909)
@[scoped simp] theorem mkParam_w₀ (r : ℝ) (u : logSpace K) : mkParam K r u w₀ = r := by
  unfold mkParam; rw [dite_eq_left rfl]

-- pin: mkParam_ne (S_NumberField_exists_completedDedekindZeta_package.lean:1912)
@[scoped simp] theorem mkParam_ne {w : InfinitePlace K} (hw : w ≠ w₀) (r : ℝ) (u : logSpace K) :
    mkParam K r u w = u ⟨w, hw⟩ := by
  unfold mkParam; rw [dite_eq_right hw]

-- pin: mkParam_neg (S_NumberField_exists_completedDedekindZeta_package.lean:1916)
theorem mkParam_neg (r : ℝ) (u : logSpace K) :
    mkParam K (-r) (-u) = -(mkParam K r u) := by
  ext w
  by_cases hw : w = w₀
  · simp [hw, mkParam_w₀]
  · simp [mkParam_ne K hw]

-- pin: gapsw80_t5_prod_yParam_mkParam (S_NumberField_exists_completedDedekindZeta_package.lean:1923)
theorem prod_yParam_mkParam (r : ℝ) (u : logSpace K) :
    ∏ w : InfinitePlace K, (yParam K (mkParam K r u) w) ^ mult w
      = Real.exp r ^ (2 * nK K) := by
  rw [prod_yParam_mult, mkParam_w₀]

-- pin: exp_half_log_pow_two_n (S_NumberField_exists_completedDedekindZeta_package.lean:1928)
theorem exp_half_log_pow_two_n {t : ℝ} (ht : 0 < t) :
    Real.exp (Real.log t / 2) ^ (2 * nK K) = t ^ (nK K) := by
  rw [pow_mul, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero,
    Real.exp_log ht]

-- pin: gapsw80_t5_heckeKernel (S_NumberField_exists_completedDedekindZeta_package.lean:1933)
def heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
    multiIdealTheta K I
      (yParam K (mkParam K (Real.log t / 2) u)) ∂volume

-- pin: gapsw80_t5_heckeKernel_transformation_raw (S_NumberField_exists_completedDedekindZeta_package.lean:1938)
theorem heckeKernel_transformation_raw (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          (∑' v : Fin (nK K) → ℤ,
            cexp ((-(π *
              (intCastVec v ⬝ᵥ (scaledGram K I
                  (yParam K (mkParam K (Real.log t / 2) u)))⁻¹
                *ᵥ intCastVec v)) : ℝ) : ℂ)) ∂volume := by
  unfold heckeKernel
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  rw [multiIdealTheta_transformation K I (fun w => yParam_pos K _ w),
    prod_yParam_mkParam, exp_half_log_pow_two_n K ht]

-- pin: gapsw80_t5_scaledGram_yParam_inv (S_NumberField_exists_completedDedekindZeta_package.lean:1955)
theorem scaledGram_yParam_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) :
    (scaledGram K I (yParam K c))⁻¹
      = (coordMatrix K I)⁻¹ * Dscale K (yParam K (-c))
          * ((coordMatrix K I)ᵀ)⁻¹ := by
  rw [scaledGram_inv_eq K I (fun w => yParam_pos K c w),
    show (fun w => (yParam K c w)⁻¹) = yParam K (-c) from
      funext fun w => (yParam_neg K c w).symm]

-- pin: gapsw80_t5_heckeKernel_transformation_raw' (S_NumberField_exists_completedDedekindZeta_package.lean:1964)
theorem heckeKernel_transformation_raw' (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          (∑' v : Fin (nK K) → ℤ,
            cexp ((-(π *
              (intCastVec v ⬝ᵥ ((coordMatrix K I)⁻¹
                  * Dscale K
                      (yParam K (mkParam K (Real.log t⁻¹ / 2) (-u)))
                  * ((coordMatrix K I)ᵀ)⁻¹)
                *ᵥ intCastVec v)) : ℝ) : ℂ)) ∂volume := by
  rw [heckeKernel_transformation_raw K I ht]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1
  ext v
  rw [scaledGram_yParam_inv,
    show mkParam K (Real.log t⁻¹ / 2) (-u)
        = -(mkParam K (Real.log t / 2) u) by
      rw [Real.log_inv, neg_div, ← mkParam_neg]]

end HeckeThetaKernel

end

end NumberField.CompletedDedekindZeta
