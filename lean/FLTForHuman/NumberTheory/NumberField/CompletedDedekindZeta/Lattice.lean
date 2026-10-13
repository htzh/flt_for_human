/-
  The ideal lattice in the mixed space, its Gram matrix, and the theta kernel.

  This is wave 1 of the `completedDedekindZeta` package: the Euclidean structure of
  the mixed space (`NumberField.mixedEmbedding.euclidean`), the `ℤ`-basis
  `idealLatticeBasisInt` of the image of a fractional ideal, the coordinate matrix
  `coordMatrix` of that basis against the standard orthonormal basis, its Gram matrix
  `idealGram`, and the covolume `|det coordMatrix|` of the ideal lattice. It closes
  with the theta kernel `thetaTerm`, its dual `dualTerm` and the Poisson law
  `PoissonLaw` those two are meant to satisfy, together with the two headline
  `Prop` obligations of the package, `completedDedekindZeta` and
  `exists_completedDedekindZeta_functionalEquation`.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:233–540`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.GaussianFourierPosDef`, `FLT.Gapsw80T15XiOrderOneB1Decomp`,
  `FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition`,
  `FLT.Gapsw80T3IdealLatticeThetaTransformation` and
  `FLT.Gapsw80T2RankNGaussianPoisson` blocks. The pin's obligation prefixes and
  per-obligation namespaces are dropped; every declaration carries the pin's own
  name and line in the `-- pin:` comment above it (playbook §2.3, §4).

  The pin's two `set_option maxHeartbeats 3200000 in` overrides on the `t15` pair
  are dropped: they sit below the port's global `maxHeartbeats` cap.
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

namespace NumberField.CompletedDedekindZeta

open Matrix
open Module
open WithLp
open Real
open NumberField.InfinitePlace
open NumberField.mixedEmbedding
open _root_.Complex hiding exp
open scoped Classical
open scoped RealInnerProductSpace
open scoped nonZeroDivisors

noncomputable section

/-! ### Inner products and quadratic forms on `ℤⁿ` -/

section GaussianQuadraticForm

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

-- pin: dotProduct_ofLp_eq_inner (S_NumberField_exists_completedDedekindZeta_package.lean:233)
lemma dotProduct_ofLp_eq_inner (x y : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ ofLp y = ⟪x, y⟫ := by
  simp [dotProduct, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

-- pin: dotProduct_mulVec_eigen (S_NumberField_exists_completedDedekindZeta_package.lean:237)
lemma dotProduct_mulVec_eigen (hA : A.PosDef)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) {μ : Fin n → ℝ}
    (hMb : ∀ j, M *ᵥ ofLp (hA.1.eigenvectorBasis j) = μ j • ofLp (hA.1.eigenvectorBasis j))
    (x : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ M *ᵥ ofLp x = ∑ i, μ i * (ofLp (hA.1.eigenvectorBasis.repr x) i) ^ 2 := by
  classical
  set bs := hA.1.eigenvectorBasis with hbs
  set w : EuclideanSpace ℝ (Fin n) := toLp 2 (M *ᵥ ofLp x) with hw
  have hcoe : ofLp w = M *ᵥ ofLp x := rfl
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM
  have h1 : ofLp x ⬝ᵥ M *ᵥ ofLp x = ⟪w, x⟫ := by
    rw [← dotProduct_ofLp_eq_inner, hcoe, dotProduct_comm]
  have h2 : ⟪w, x⟫ = ∑ i, ofLp (bs.repr w) i * ofLp (bs.repr x) i := by
    rw [← LinearIsometryEquiv.inner_map_map bs.repr w x, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 : ∀ i, ofLp (bs.repr w) i = μ i * ofLp (bs.repr x) i := by
    intro i
    have hr : ofLp (bs.repr w) i = ⟪bs i, w⟫ := bs.repr_apply_apply w i
    have hr' : ofLp (bs.repr x) i = ⟪bs i, x⟫ := bs.repr_apply_apply x i
    rw [hr, hr', ← dotProduct_ofLp_eq_inner, ← dotProduct_ofLp_eq_inner, hcoe,
      dotProduct_mulVec, ← Matrix.mulVec_transpose, hMT, hMb i, smul_dotProduct]
    rfl
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => by rw [h3 i]; ring

-- pin: quadForm_eq_sum_eigen (S_NumberField_exists_completedDedekindZeta_package.lean:264)
lemma quadForm_eq_sum_eigen (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ A *ᵥ ofLp x
      = ∑ i, hA.1.eigenvalues i * (ofLp (hA.1.eigenvectorBasis.repr x) i) ^ 2 :=
  dotProduct_mulVec_eigen hA hA.1 (hA.1.mulVec_eigenvectorBasis) x

end GaussianQuadraticForm

/-! ### The order bound on `s(s - 1)` outside the unit disc -/

section XiOrderBound

-- pin: gapsw80_t15_norm_ge_two_ne_zero_one (S_NumberField_exists_completedDedekindZeta_package.lean:299)
theorem ne_zero_and_ne_one_of_two_le_norm {s : ℂ} (hs : 2 ≤ ‖s‖) :
    s ≠ 0 ∧ s ≠ 1 := by
  have _em := Classical.em
  constructor
  · intro h; rw [h, norm_zero] at hs; linarith
  · intro h; rw [h, norm_one] at hs; linarith

-- pin: gapsw80_t15_sat_polynomialFactor_orderBound (S_NumberField_exists_completedDedekindZeta_package.lean:308)
theorem log_norm_mul_sub_one_le_two_mul_norm_mul_log :
    ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖s * (s - 1)‖ ≤ 2 * ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  intro s hs
  obtain ⟨h0, h1⟩ := ne_zero_and_ne_one_of_two_le_norm hs
  have hns : (0:ℝ) < ‖s‖ := lt_of_lt_of_le (by norm_num) hs
  have hprod_pos : (0:ℝ) < ‖s * (s - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr (sub_ne_zero.mpr h1))

  have hub : ‖s * (s - 1)‖ ≤ 2 * ‖s‖ ^ 2 := by
    rw [norm_mul, sq]
    have hs1 : ‖s - 1‖ ≤ 2 * ‖s‖ :=
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le s 1
        _ = ‖s‖ + 1 := by rw [norm_one]
        _ ≤ ‖s‖ + ‖s‖ := by linarith
        _ = 2 * ‖s‖ := by ring
    nlinarith [norm_nonneg s]

  have hlog1 : Real.log ‖s * (s - 1)‖ ≤ Real.log (2 * ‖s‖ ^ 2) :=
    Real.log_le_log hprod_pos hub
  have hlog2 : Real.log (2 * ‖s‖ ^ 2) = Real.log 2 + 2 * Real.log ‖s‖ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring

  have hlogs : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : Real.log 2 + 2 * Real.log ‖s‖ ≤ 2 * ‖s‖ * Real.log ‖s‖ := by
    have hprod : (1:ℝ) * Real.log 2 ≤ (‖s‖ - 1) * Real.log ‖s‖ :=
      mul_le_mul (by linarith) hlogs hlog2_pos.le (by linarith)
    nlinarith [hprod]
  linarith

end XiOrderBound

/-! ### The completed Dedekind zeta function and the functional equation it must satisfy -/

section CompletedZetaObligation

-- pin: gapsw80_t1_completedDedekindZeta (S_NumberField_exists_completedDedekindZeta_package.lean:356)
noncomputable def completedDedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|discr K| : ℤ) : ℂ)) ^ (s / 2)
    * Gammaℝ s ^ nrRealPlaces K
    * Gammaℂ s ^ nrComplexPlaces K
    * dedekindZeta K s

-- pin: gapsw80_t1_DedekindCompletedFE (S_NumberField_exists_completedDedekindZeta_package.lean:363)
def exists_completedDedekindZeta_functionalEquation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ {(0 : ℂ), 1}ᶜ ∧
      (∀ s : ℂ, 1 < s.re → Λ s = completedDedekindZeta K s) ∧
      (∀ s : ℂ, Λ (1 - s) = Λ s)

end CompletedZetaObligation

/-! ### The ideal lattice in the mixed space and its coordinate matrix -/

section IdealLattice

variable (K : Type) [Field K] [NumberField K]

-- pin: nK (S_NumberField_exists_completedDedekindZeta_package.lean:389)
abbrev nK := finrank ℚ K

-- pin: eIdx (S_NumberField_exists_completedDedekindZeta_package.lean:391)
def indexEquivFin : index K ≃ Fin (nK K) :=
  Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank])

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

-- pin: eI (S_NumberField_exists_completedDedekindZeta_package.lean:397)
def chooseBasisIndexEquivFin :
    Free.ChooseBasisIndex ℤ (I : FractionalIdeal (𝓞 K)⁰ K) ≃ Fin (nK K) :=
  Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, RingOfIntegers.rank])

-- pin: latE (S_NumberField_exists_completedDedekindZeta_package.lean:401)
def euclideanIdealLatticeBasis (i : Fin (nK K)) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (fractionalIdealLatticeBasis K I ((chooseBasisIndexEquivFin K I).symm i))

-- pin: latE_linearIndependent (S_NumberField_exists_completedDedekindZeta_package.lean:404)
theorem euclideanIdealLatticeBasis_linearIndependent :
    LinearIndependent ℝ (euclideanIdealLatticeBasis K I) := by
  have h := (fractionalIdealLatticeBasis K I).linearIndependent
  have h' := h.map' (euclidean.toMixed K).symm.toLinearMap
    (LinearEquiv.ker _)
  exact h'.comp _ (chooseBasisIndexEquivFin K I).symm.injective

-- pin: fILB_linearIndependent_int (S_NumberField_exists_completedDedekindZeta_package.lean:410)
theorem fractionalIdealLatticeBasis_linearIndependent_int :
    LinearIndependent ℤ (⇑(fractionalIdealLatticeBasis K I)) :=
  (fractionalIdealLatticeBasis K I).linearIndependent.restrict_scalars
    (by simp only [zsmul_one]; exact Int.cast_injective)

-- pin: idealZBasis (S_NumberField_exists_completedDedekindZeta_package.lean:415)
def idealLatticeBasisInt : Basis (Fin (nK K)) ℤ (mixedEmbedding.idealLattice K I) :=
  ((Basis.span (fractionalIdealLatticeBasis_linearIndependent_int K I)).map
      (LinearEquiv.ofEq _ _ (span_idealLatticeBasis K I))).reindex (chooseBasisIndexEquivFin K I)

-- pin: idealZBasis_apply (S_NumberField_exists_completedDedekindZeta_package.lean:420)
@[scoped simp]
theorem idealLatticeBasisInt_apply (i : Fin (nK K)) :
    (idealLatticeBasisInt K I i : mixedSpace K)
      = fractionalIdealLatticeBasis K I ((chooseBasisIndexEquivFin K I).symm i) := by
  have h : ((Basis.span (fractionalIdealLatticeBasis_linearIndependent_int K I))
        ((chooseBasisIndexEquivFin K I).symm i) : mixedSpace K)
      = fractionalIdealLatticeBasis K I ((chooseBasisIndexEquivFin K I).symm i) :=
    Basis.coe_span_apply _ _
  simp only [idealLatticeBasisInt, Basis.coe_reindex, Function.comp_apply, Basis.map_apply]
  exact h

-- pin: gapsw80_t3_idealGram (S_NumberField_exists_completedDedekindZeta_package.lean:429)
def idealGram : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.gram ℝ (euclideanIdealLatticeBasis K I)

-- pin: gapsw80_t3_idealGram_posDef (S_NumberField_exists_completedDedekindZeta_package.lean:432)
theorem idealGram_posDef : (idealGram K I).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (euclideanIdealLatticeBasis_linearIndependent K I)

-- pin: stdONBFin (S_NumberField_exists_completedDedekindZeta_package.lean:435)
def stdOrthonormalBasisFin : OrthonormalBasis (Fin (nK K)) ℝ (euclidean.mixedSpace K) :=
  (euclidean.stdOrthonormalBasis K).reindex (indexEquivFin K)

-- pin: stdBasisFin (S_NumberField_exists_completedDedekindZeta_package.lean:438)
def stdBasisFin : Basis (Fin (nK K)) ℝ (mixedSpace K) :=
  (mixedEmbedding.stdBasis K).reindex (indexEquivFin K)

-- pin: stdBasisFin_repr_eq (S_NumberField_exists_completedDedekindZeta_package.lean:441)
theorem stdBasisFin_repr_eq (x : mixedSpace K) (i : Fin (nK K)) :
    (stdBasisFin K).repr x i
      = (stdOrthonormalBasisFin K).repr ((euclidean.toMixed K).symm x) i := by
  simp only [stdBasisFin, stdOrthonormalBasisFin, Basis.repr_reindex_apply,
    OrthonormalBasis.repr_reindex, ← euclidean.stdOrthonormalBasis_map_eq K,
    Basis.map_repr, LinearEquiv.trans_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  rfl

-- pin: coordMatrix (S_NumberField_exists_completedDedekindZeta_package.lean:449)
def coordMatrix : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.of fun i j => (stdOrthonormalBasisFin K).repr (euclideanIdealLatticeBasis K I j) i

-- pin: gapsw80_t3_idealGram_eq_transpose_mul (S_NumberField_exists_completedDedekindZeta_package.lean:452)
theorem idealGram_eq_transpose_mul :
    idealGram K I = (coordMatrix K I)ᵀ * (coordMatrix K I) := by
  have h := Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasisFin K)
    (euclideanIdealLatticeBasis K I)
  simpa only [idealGram, coordMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    using h

-- pin: coordMatrix_eq_toMatrix (S_NumberField_exists_completedDedekindZeta_package.lean:458)
theorem coordMatrix_eq_toMatrix :
    coordMatrix K I = (stdBasisFin K).toMatrix (fun i => ↑(idealLatticeBasisInt K I i)) := by
  ext i j
  rw [coordMatrix, Matrix.of_apply, Basis.toMatrix_apply, idealLatticeBasisInt_apply,
    stdBasisFin_repr_eq]
  rfl

-- pin: volume_fundamentalDomain_stdBasisFin (S_NumberField_exists_completedDedekindZeta_package.lean:465)
theorem volume_fundamentalDomain_stdBasisFin :
    MeasureTheory.volume.real (ZSpan.fundamentalDomain (stdBasisFin K)) = 1 := by
  rw [stdBasisFin, ZSpan.fundamentalDomain_reindex, MeasureTheory.measureReal_def,
    volume_fundamentalDomain_stdBasis, ENNReal.toReal_one]

-- pin: abs_det_coordMatrix (S_NumberField_exists_completedDedekindZeta_package.lean:470)
theorem abs_det_coordMatrix :
    |(coordMatrix K I).det| = ZLattice.covolume (mixedEmbedding.idealLattice K I) := by
  have h := ZLattice.covolume_eq_det_mul_measureReal
    (b := idealLatticeBasisInt K I) (b₀ := stdBasisFin K)
  rw [volume_fundamentalDomain_stdBasisFin, mul_one] at h
  rw [coordMatrix_eq_toMatrix, ← Basis.det_apply]
  exact h.symm

-- pin: zEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:478)
def idealLatticeEquiv : (Fin (nK K) → ℤ) ≃ₗ[ℤ] mixedEmbedding.idealLattice K I :=
  (idealLatticeBasisInt K I).equivFun.symm

-- pin: coe_zEquiv_apply (S_NumberField_exists_completedDedekindZeta_package.lean:481)
theorem idealLatticeEquiv_apply (v : Fin (nK K) → ℤ) :
    (idealLatticeEquiv K I v : mixedSpace K)
      = ∑ i, (v i : ℝ) • fractionalIdealLatticeBasis K I ((chooseBasisIndexEquivFin K I).symm i) := by
  have h := (idealLatticeBasisInt K I).equivFun_symm_apply v
  calc (idealLatticeEquiv K I v : mixedSpace K)
      = ((∑ i, v i • idealLatticeBasisInt K I i : idealLattice K I) : mixedSpace K) := by
        rw [idealLatticeEquiv, h]
    _ = ∑ i, v i • (idealLatticeBasisInt K I i : mixedSpace K) := by push_cast; ring_nf
    _ = ∑ i, (v i : ℝ) • fractionalIdealLatticeBasis K I ((chooseBasisIndexEquivFin K I).symm i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [idealLatticeBasisInt_apply, ← Int.cast_smul_eq_zsmul ℝ]

end IdealLattice

/-! ### The theta kernel and its dual -/

section ThetaKernel

variable {n : ℕ}

-- pin: zcastR (S_NumberField_exists_completedDedekindZeta_package.lean:517)
abbrev intCastVec (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

-- pin: rQuad (S_NumberField_exists_completedDedekindZeta_package.lean:519)
abbrev realQuadForm (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := v ⬝ᵥ (A *ᵥ v)

-- pin: cQuad (S_NumberField_exists_completedDedekindZeta_package.lean:521)
abbrev complexQuadForm (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ := v ⬝ᵥ (A *ᵥ v)

-- pin: liftC (S_NumberField_exists_completedDedekindZeta_package.lean:523)
abbrev liftToComplex (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map ((↑) : ℝ → ℂ)

-- pin: thetaTerm (S_NumberField_exists_completedDedekindZeta_package.lean:526)
def thetaTerm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ)
    (v : Fin n → ℤ) : ℂ :=
  cexp (-(π : ℂ) * (t : ℂ) * (realQuadForm A (intCastVec v) : ℂ)
    + 2 * π * ∑ i, b i * (v i : ℂ))

-- pin: dualTerm (S_NumberField_exists_completedDedekindZeta_package.lean:530)
def dualTerm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ)
    (w : Fin n → ℤ) : ℂ :=
  cexp (-(π : ℂ) / (t : ℂ) *
    complexQuadForm (liftToComplex A⁻¹) (fun i => (w i : ℂ) + Complex.I * b i))

-- pin: PoissonLaw (S_NumberField_exists_completedDedekindZeta_package.lean:535)
def PoissonLaw (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ) : Prop :=
  (∑' v, thetaTerm A t b v)
    = (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, dualTerm A t b w

end ThetaKernel

end

end NumberField.CompletedDedekindZeta
