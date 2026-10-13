/-
  Summability of the theta kernel and the Poisson summation law.

  This is wave 2 of the `completedDedekindZeta` package. It proves that the theta
  term `thetaTerm A t b` and its dual `dualTerm A t b` are absolutely summable for
  positive-definite `A` (`summable_thetaTerm`, `summable_dualTerm`), through the
  one-dimensional Gaussian bound `summable_real_exp_quadratic_int` and the
  finite-product lemma `summable_prod_fin`; it lands the Schur-complement identities
  for the block matrix `fromBlocks P q qᵀ D`, the positive definiteness of the Schur
  complement `P - q * ⅟D * qᵀ`, and the induction step
  `poissonLawBlock_of_poissonLaw` for the `2 × 2` block form `PoissonLawBlock` of the
  Poisson law; and it assembles the rank-`n` Gaussian Poisson transformation law
  `poissonLaw_of_posDef` with its linear-term-free corollary
  `poissonSummation_posDef`.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:541–1599`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.Gapsw80T2RankNGaussianPoisson` block. The pin's obligation prefix and
  its `namespace FLT.Gapsw80T2RankNGaussianPoisson` are dropped; every declaration
  carries the pin's own name and line in the `-- pin:` comment above it
  (playbook §2.3, §4).

  The pin's `set_option maxHeartbeats 6400000` is file-wide there and is not
  transcribed; the port's global cap is `4000000`.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Lattice
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace NumberField.CompletedDedekindZeta

open Matrix
open Module
open WithLp
open Real
open NumberField.mixedEmbedding
open _root_.Complex hiding exp
open scoped Classical
open scoped RealInnerProductSpace

noncomputable section

/-! ### Summability of the theta terms -/

section Summability

variable {n : ℕ}

-- pin: gapsw80_t2_posDef_quadForm_lower (S_NumberField_exists_completedDedekindZeta_package.lean:541)
theorem posDef_quadForm_lower {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ realQuadForm A x := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hE | hNE
  · exact ⟨1, one_pos, fun x => by simp [realQuadForm, dotProduct]⟩
  obtain ⟨i₀, hmin⟩ := Finite.exists_min hA.1.eigenvalues
  refine ⟨hA.1.eigenvalues i₀, hA.eigenvalues_pos i₀, fun x => ?_⟩
  have hquad :=
    quadForm_eq_sum_eigen hA (WithLp.toLp 2 x)
  have hxx : x ⬝ᵥ x
      = ∑ i, (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
    have h1 : x ⬝ᵥ x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) :=
      dotProduct_ofLp_eq_inner
        (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    have h2 := (hA.1.eigenvectorBasis.repr.inner_map_map
      (WithLp.toLp 2 x) (WithLp.toLp 2 x)).symm
    have h3 := (dotProduct_ofLp_eq_inner
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))).symm
    rw [h1, h2, h3]; simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  calc hA.1.eigenvalues i₀ * (x ⬝ᵥ x)
      = ∑ i, hA.1.eigenvalues i₀ *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
        rw [hxx, Finset.mul_sum]
    _ ≤ ∑ i, hA.1.eigenvalues i *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
    _ = realQuadForm A x := hquad.symm

-- pin: gapsw80_t2_summable_1D (S_NumberField_exists_completedDedekindZeta_package.lean:572)
lemma summable_norm_exp_quadratic_int {a : ℝ} (ha : 0 < a) (b : ℂ) :
    Summable fun k : ℤ =>
      ‖cexp (-(π : ℂ) * (a : ℂ) * (k : ℂ) ^ 2 + 2 * π * b * (k : ℂ))‖ := by
  have hre : (-(π : ℂ) * (a : ℂ)).re < 0 := by
    simp only [neg_mul, neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    exact neg_neg_of_pos (mul_pos pi_pos ha)
  have hO := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hre (2 * π * b)
    (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  simp only [Function.comp_def, Complex.ofReal_intCast] at hO
  exact (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hO).norm

-- pin: gapsw80_t2_summable_prod_fin (S_NumberField_exists_completedDedekindZeta_package.lean:583)
lemma summable_prod_fin :
    ∀ {n : ℕ} {f : Fin n → ℤ → ℝ}, (∀ i k, 0 ≤ f i k) → (∀ i, Summable (f i)) →
      Summable fun v : Fin n → ℤ => ∏ i, f i (v i) := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    have hU : Subsingleton (Fin 0 → ℤ) := inferInstance
    refine ⟨1, ?_⟩
    have hconst : (fun v : Fin 0 → ℤ => ∏ i, f i (v i)) = fun _ => 1 := by
      funext v; exact Finset.prod_empty
    rw [hconst]
    simp
  | succ m IH =>
    intro f hpos hsum
    set e : (Fin (m + 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
      { toFun := fun v => ⟨v ∘ Fin.castSucc, v (Fin.last m)⟩
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun v => by
          funext i; dsimp only
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun p => by
          ext
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last] }
    have hIH : Summable fun v : Fin m → ℤ => ∏ i, f (Fin.castSucc i) (v i) :=
      IH (fun i k => hpos _ k) fun i => hsum _
    have hprod :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          (∏ i, f (Fin.castSucc i) (p.1 i)) * f (Fin.last m) p.2 :=
      hIH.mul_of_nonneg (hsum _) (fun v => Finset.prod_nonneg fun i _ => hpos _ _)
        (fun k => hpos _ k)
    have hprod' :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          ∏ i, f i ((Fin.snoc p.1 p.2 : Fin (m + 1) → ℤ) i) := by
      refine hprod.congr fun p => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact e.symm.summable_iff.mp hprod'

-- pin: gapsw80_t2_summable_1D_real (S_NumberField_exists_completedDedekindZeta_package.lean:625)
lemma summable_real_exp_quadratic_int {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Summable fun k : ℤ => rexp (-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) := by
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  have h := summable_norm_exp_quadratic_int (a := a / π) (div_pos ha pi_pos)
    (((r / (2 * π)) : ℝ) : ℂ)
  refine h.congr fun k => ?_
  have heq : (-(π : ℂ) * ((a / π : ℝ) : ℂ) * (k : ℂ) ^ 2
        + 2 * π * (((r / (2 * π)) : ℝ) : ℂ) * (k : ℂ))
      = (((-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [heq, Complex.norm_exp, Complex.ofReal_re]

-- pin: gapsw80_t2_summable_gaussian_Zn (S_NumberField_exists_completedDedekindZeta_package.lean:638)
lemma summable_exp_neg_mul_sum_sq_int {c : ℝ} (hc : 0 < c) :
    Summable fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)) := by
  have hrew : (fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)))
      = fun v => ∏ i, rexp (-(c * (v i : ℝ) ^ 2)) := by
    funext v; rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hrew]
  exact summable_prod_fin (n := n)
    (f := fun _ k => rexp (-(c * (k : ℝ) ^ 2)))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => (summable_real_exp_quadratic_int hc 0).congr fun k => by
      rw [zero_mul, add_zero])

-- pin: gapsw80_t2_re_cQuad_liftC (S_NumberField_exists_completedDedekindZeta_package.lean:650)
lemma complexQuadForm_liftToComplex_re (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    (complexQuadForm (liftToComplex A) z).re
      = realQuadForm A (fun i => (z i).re) - realQuadForm A (fun i => (z i).im) := by
  have hmv : ∀ i, ((liftToComplex A) *ᵥ z) i = ∑ j, (A i j : ℂ) * z j := fun i => by
    simp only [Matrix.mulVec, dotProduct, liftToComplex, Matrix.map_apply]
  have hmvR : ∀ (x : Fin n → ℝ) i, (A *ᵥ x) i = ∑ j, A i j * x j := fun x i => by
    simp only [Matrix.mulVec, dotProduct]
  unfold complexQuadForm realQuadForm
  simp only [dotProduct, hmv, hmvR]
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.re_sum, Complex.im_sum]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]

-- pin: gapsw80_t2_summable_thetaTerm (S_NumberField_exists_completedDedekindZeta_package.lean:664)
theorem summable_thetaTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun v : Fin n → ℤ => ‖thetaTerm A t b v‖ := by
  obtain ⟨c, hc, hQ⟩ := posDef_quadForm_lower hA
  have hxx : ∀ v : Fin n → ℤ, intCastVec v ⬝ᵥ intCastVec v = ∑ i, (v i : ℝ) ^ 2 := fun v => by
    simp only [dotProduct, intCastVec]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  set g : Fin n → ℤ → ℝ := fun i k =>
    rexp (-(π * t * c * (k : ℝ) ^ 2) + 2 * π * (b i).re * (k : ℝ))
  have hmajor : Summable fun v : Fin n → ℤ => ∏ i, g i (v i) :=
    summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le)
      (fun i => (summable_real_exp_quadratic_int (a := π * t * c) (by positivity)
          (2 * π * (b i).re)).congr
        fun k => by unfold g; ring_nf)
  refine hmajor.of_nonneg_of_le (fun v => norm_nonneg _) fun v => ?_
  unfold thetaTerm
  rw [Complex.norm_exp]
  have hre : (-(π : ℂ) * (t : ℂ) * (realQuadForm A (intCastVec v) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)).re
      = -(π * t * realQuadForm A (intCastVec v)) + 2 * π * ∑ i, (b i).re * (v i : ℝ) := by
    have h1 : -(π : ℂ) * (t : ℂ) * (realQuadForm A (intCastVec v) : ℂ)
        = (((-(π * t * realQuadForm A (intCastVec v))) : ℝ) : ℂ) := by push_cast; ring
    have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by
      simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  rw [hre, show (∏ i, g i (v i)) = rexp (∑ i,
      (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ))) from
    (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQv := hQ (intCastVec v); rw [hxx v] at hQv
  have hsplit : (∑ i, (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ)))
      = -(π * t) * (c * ∑ i, (v i : ℝ) ^ 2)
        + (2 * π) * ∑ i, (b i).re * (v i : ℝ) := by
    rw [Finset.sum_add_distrib]; congr 1
    · rw [← mul_assoc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  nlinarith [mul_pos pi_pos ht]

-- pin: gapsw80_t2_summable_dualTerm (S_NumberField_exists_completedDedekindZeta_package.lean:708)
theorem summable_dualTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun w : Fin n → ℤ => ‖dualTerm A t b w‖ := by
  obtain ⟨c, hc, hQ⟩ := posDef_quadForm_lower hA.inv
  set d : Fin n → ℝ := fun i => (b i).im
  set C₁ : ℝ := rexp (π / t * realQuadForm A⁻¹ (fun i => (b i).re))
  have hC₁ : 0 ≤ C₁ := (Real.exp_pos _).le

  have hconst : ∀ w : Fin n → ℤ,
      ‖dualTerm A t b w‖
        = C₁ * rexp (-(π / t) * realQuadForm A⁻¹ (fun i => (w i : ℝ) - d i)) := by
    intro w
    unfold dualTerm
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have hcoef : -(π : ℂ) / (t : ℂ) = (((-(π / t)) : ℝ) : ℂ) := by push_cast; ring
    rw [hcoef, Complex.re_ofReal_mul, complexQuadForm_liftToComplex_re]
    have hre : (fun i => ((w i : ℂ) + Complex.I * b i).re)
        = fun i => (w i : ℝ) - d i := by
      funext i; simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, d]; ring
    have him : (fun i => ((w i : ℂ) + Complex.I * b i).im)
        = fun i => (b i).re := by
      funext i; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hre, him]; ring

  set g : Fin n → ℤ → ℝ := fun i k => rexp (-(π * c / t) * ((k : ℝ) - d i) ^ 2)
  have hg_sum : ∀ i, Summable (g i) := fun i => by
    refine ((summable_real_exp_quadratic_int (a := π * c / t) (by positivity)
        (2 * (π * c / t) * d i)).mul_left (rexp (-(π * c / t) * (d i) ^ 2))).congr
      fun k => ?_
    unfold g; rw [← Real.exp_add]; ring_nf
  have hmajor : Summable fun w : Fin n → ℤ => ∏ i, g i (w i) :=
    summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le) hg_sum
  refine (hmajor.mul_left C₁).of_nonneg_of_le (fun w => norm_nonneg _) fun w => ?_
  rw [hconst w]
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  rw [show (∏ i, g i (w i))
      = rexp (∑ i, -(π * c / t) * ((w i : ℝ) - d i) ^ 2) from (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQw := hQ (fun i => (w i : ℝ) - d i)
  have hdot : (fun i => (w i : ℝ) - d i) ⬝ᵥ (fun i => (w i : ℝ) - d i)
      = ∑ i, ((w i : ℝ) - d i) ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [hdot] at hQw
  rw [← Finset.mul_sum, show -(π * c / t) = -(π / t) * c by ring, mul_assoc]
  have hnp : -(π / t) ≤ 0 := neg_nonpos_of_nonneg (div_pos pi_pos ht).le
  exact mul_le_mul_of_nonpos_left hQw hnp

end Summability

/-! ### The Schur complement of a `2 × 2` block matrix -/

section BilinearSchur

variable {R : Type*} [CommRing R] {m k : ℕ}

-- pin: gapsw80_t2_bilin_schur_eq₂₂ (S_NumberField_exists_completedDedekindZeta_package.lean:765)
theorem schurComplement_bilin_eq
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ᵥ* (fromBlocks P q qᵀ D) ⬝ᵥ (Sum.elim x y)
      = ((⅟D * qᵀ) *ᵥ x + y) ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x + y)
        + x ᵥ* (P - q * ⅟D * qᵀ) ⬝ᵥ x := by

  have hDinv : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hD] at this
    exact (invOf_eq_right_inv this).symm
  have hz : ((⅟D * qᵀ) *ᵥ x) ᵥ* D = x ᵥ* q := by
    rw [← vecMul_transpose, Matrix.transpose_mul, hDinv, Matrix.transpose_transpose,
      vecMul_vecMul, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  have hDz : D *ᵥ ((⅟D * qᵀ) *ᵥ x) = qᵀ *ᵥ x := by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hxy : x ᵥ* q ⬝ᵥ y = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hqS : x ᵥ* (q * ⅟D * qᵀ) ⬝ᵥ x = x ᵥ* q ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) := by
    rw [Matrix.mul_assoc, ← vecMul_vecMul, ← dotProduct_mulVec]
  have hyDz : y ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, hDz, dotProduct_mulVec]
  simp only [vecMul_fromBlocks, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, add_vecMul, vecMul_sub, add_dotProduct,
    dotProduct_add, sub_dotProduct, hz, hyDz, hqS]
  ring

-- pin: gapsw80_t2_bilin_schur_eq₂₂' (S_NumberField_exists_completedDedekindZeta_package.lean:794)
theorem schurComplement_bilin_mulVec_eq
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ (Sum.elim x y))
      = ((⅟D * qᵀ) *ᵥ x + y) ⬝ᵥ (D *ᵥ ((⅟D * qᵀ) *ᵥ x + y))
        + x ⬝ᵥ ((P - q * ⅟D * qᵀ) *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec]
  exact schurComplement_bilin_eq P q D hD x y

-- pin: gapsw80_t2_bilin_schur_inv_scalar (S_NumberField_exists_completedDedekindZeta_package.lean:804)
theorem schurComplement_inv_scalar_bilin_eq
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin 1) R)
    (a : R) [Invertible a] (hP : Pᵀ = P)
    [Invertible (P - q * ⅟a • qᵀ)]
    (X : Fin m → R) (Y : R) :
    (Sum.elim X (fun _ => Y)) ⬝ᵥ
        ((fromBlocks P q qᵀ ((a : R) • (1 : Matrix (Fin 1) (Fin 1) R)))⁻¹
          *ᵥ (Sum.elim X (fun _ => Y)))
      = (X - (⅟a * Y) • (fun i => q i 0)) ⬝ᵥ
          ((P - q * ⅟a • qᵀ)⁻¹ *ᵥ (X - (⅟a * Y) • (fun i => q i 0)))
        + ⅟a * Y ^ 2 := by
  classical
  set D : Matrix (Fin 1) (Fin 1) R := (a : R) • 1 with hD
  have hDi : Invertible D :=
    ⟨⅟a • 1, by rw [hD, smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟D = (⅟a : R) • (1 : Matrix (Fin 1) (Fin 1) R) :=
    invOf_eq_right_inv
      (by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) R := P - q * ⅟a • qᵀ with hS
  have hSeq : P - q * ⅟D * qᵀ = S := by
    rw [hS, hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  have : Invertible (P - q * ⅟D * qᵀ) := hSeq ▸ (inferInstance : Invertible S)
  have hMi : Invertible (fromBlocks P q qᵀ D) := fromBlocks₂₂Invertible P q qᵀ D

  set q₀ : Fin m → R := fun i => q i 0
  have hq0T : ∀ x : Fin m → R, qᵀ *ᵥ x = fun _ => q₀ ⬝ᵥ x := fun x => by
    funext j; fin_cases j; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, q₀]
  have hq0 : ∀ y : Fin 1 → R, q *ᵥ y = y 0 • q₀ := fun y => by
    funext i; simp [Matrix.mulVec, dotProduct, q₀, mul_comm]
  have hF1 : ∀ (c : R) (y : Fin 1 → R), (fun _ => c) ⬝ᵥ y = c * y 0 := fun c y => by
    simp [dotProduct]
  have hSiT : (⅟S)ᵀ = ⅟S := by
    have hST : Sᵀ = S := by
      rw [hS, Matrix.transpose_sub, hP, Matrix.transpose_mul, Matrix.transpose_smul,
        Matrix.transpose_transpose, Matrix.smul_mul, ← Matrix.mul_smul]
    have h1 : Sᵀ * (⅟S)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hST] at h1; exact (invOf_eq_right_inv h1).symm
  have hswap : ∀ x y : Fin m → R, x ⬝ᵥ (⅟S *ᵥ y) = y ⬝ᵥ (⅟S *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose (⅟S) x, hSiT, dotProduct_comm]
  have hDy : ⅟D *ᵥ (fun _ => Y : Fin 1 → R) = fun _ => ⅟a * Y := by
    funext j; fin_cases j
    simp only [hiD, smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]

  rw [← Matrix.invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  simp only [hSeq]

  have hTop : (⅟S *ᵥ X + (-(⅟S * q * ⅟D)) *ᵥ fun _ => Y)
      = ⅟S *ᵥ X - (⅟a * Y) • (⅟S *ᵥ q₀) := by
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDy,
      hq0, Matrix.mulVec_smul, sub_eq_add_neg]
  have hBot : ((-(⅟D * qᵀ * ⅟S)) *ᵥ X + (⅟D + ⅟D * qᵀ * ⅟S * q * ⅟D) *ᵥ fun _ => Y)
      = fun _ => -(⅟a * (q₀ ⬝ᵥ (⅟S *ᵥ X)))
          + (⅟a * Y + ⅟a ^ 2 * Y * (q₀ ⬝ᵥ (⅟S *ᵥ q₀))) := by
    funext j; fin_cases j
    simp only [Matrix.neg_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      hq0, Matrix.mulVec_smul, hq0T, hiD, smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
    ring
  rw [hTop, hBot, hF1]
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hswap X q₀]
  ring

-- pin: gapsw80_t2_posDef_schur (S_NumberField_exists_completedDedekindZeta_package.lean:871)
theorem schurComplement_posDef
    {P : Matrix (Fin m) (Fin m) ℝ} {q : Matrix (Fin m) (Fin k) ℝ}
    {D : Matrix (Fin k) (Fin k) ℝ} [Invertible D] (hD : D.IsHermitian)
    (hM : (fromBlocks P q qᵀ D).PosDef) :
    (P - q * ⅟D * qᵀ).PosDef := by
  have hMi := (posDef_iff_dotProduct_mulVec).mp hM
  have hDT : Dᵀ = D := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hD
  have hDiT : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, invOf_mul_self, Matrix.transpose_one]
    rw [hDT] at this; exact (invOf_eq_right_inv this).symm
  have hPherm : P.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp hMi.1).1
  have hPT : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hPherm
  have hSH : (P - q * ⅟D * qᵀ).IsHermitian := by
    show (P - q * ⅟D * qᵀ)ᴴ = P - q * ⅟D * qᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hPT, hDiT, Matrix.mul_assoc]
  refine (posDef_iff_dotProduct_mulVec).mpr ⟨hSH, fun x hx => ?_⟩

  set y : Fin k → ℝ := -((⅟D * qᵀ) *ᵥ x) with hy
  have hxy : Sum.elim x y ≠ 0 := fun h => hx (funext fun i => by
    have := congrFun h (Sum.inl i); simpa using this)
  have key : 0 < star (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ Sum.elim x y) :=
    hMi.2 hxy
  rw [show star (Sum.elim x y) = Sum.elim x y from rfl,
    schurComplement_bilin_mulVec_eq P q D hDT x y] at key
  simp only [hy] at key
  simpa [show star x = x from rfl] using key

end BilinearSchur

/-! ### The Poisson transformation law by induction on the rank -/

section InductionStep

variable {m : ℕ}

-- pin: PoissonLawBlock (S_NumberField_exists_completedDedekindZeta_package.lean:911)
def PoissonLawBlock (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ)
    (t : ℝ) (b : (Fin m ⊕ Fin 1) → ℂ) : Prop :=
  (∑' v : (Fin m ⊕ Fin 1) → ℤ,
      cexp (-(π : ℂ) * t *
          (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)))
    = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) *
      ∑' w : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t *
          ((fun i => (w i : ℂ) + Complex.I * b i) ⬝ᵥ
            ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ) + Complex.I * b i)))

-- pin: gapsw80_t2_poisson_step (S_NumberField_exists_completedDedekindZeta_package.lean:925)
theorem poissonLawBlock_of_poissonLaw
    (IH : ∀ (S : Matrix (Fin m) (Fin m) ℝ), S.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin m → ℂ, PoissonLaw S t b)
    (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ) (hM : M.PosDef)
    {t : ℝ} (ht : 0 < t) (b : (Fin m ⊕ Fin 1) → ℂ) :
    PoissonLawBlock M t b := by
  classical

  set P : Matrix (Fin m) (Fin m) ℝ := M.toBlocks₁₁
  set q : Matrix (Fin m) (Fin 1) ℝ := M.toBlocks₁₂
  set a : ℝ := M (Sum.inr 0) (Sum.inr 0)
  set b' : Fin m → ℂ := b ∘ Sum.inl
  set b₁ : ℂ := b (Sum.inr 0)
  set q₀ : Fin m → ℝ := fun i => q i 0
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM.1
  have hMblock : M = fromBlocks P q qᵀ ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    conv_lhs => rw [← M.fromBlocks_toBlocks]
    congr 1
    · ext i j
      have := congrFun (congrFun hMT (Sum.inl j)) (Sum.inr i)
      simp [Matrix.transpose_apply] at this
      exact this
    · ext i j; fin_cases i; fin_cases j
      simp [Matrix.toBlocks₂₂, a, Matrix.smul_apply]
  have ha : 0 < a := by
    set v₀ : (Fin m ⊕ Fin 1) → ℝ := Sum.elim 0 (fun _ => (1 : ℝ)) with hv₀
    have hne : v₀ ≠ 0 := fun h =>
      (one_ne_zero : (1 : ℝ) ≠ 0) (by have := congrFun h (Sum.inr 0); simp [hv₀] at this)
    have key : 0 < star v₀ ⬝ᵥ (M *ᵥ v₀) :=
      (posDef_iff_dotProduct_mulVec.mp hM).2 hne
    have heval : star v₀ ⬝ᵥ (M *ᵥ v₀) = a := by
      rw [show (star v₀ : _ → ℝ) = v₀ from rfl, hv₀, hMblock, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add,
        smul_mulVec, Matrix.one_mulVec, dotProduct,
        Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rwa [heval] at key
  have haI : Invertible a := invertibleOfNonzero ha.ne'
  have haCI : Invertible (a : ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.mpr ha.ne')
  have hia : (⅟a : ℝ) = a⁻¹ := invOf_eq_inv a
  have hiaC : (⅟(a : ℂ) : ℂ) = (a : ℂ)⁻¹ := invOf_eq_inv (a : ℂ)
  have hDi : Invertible ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ⟨⅟a • 1, by rw [smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (⅟a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
    invOf_eq_right_inv (by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) ℝ := P - q * ⅟a • qᵀ with hS
  have hSpd : S.PosDef := by
    have hDh : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
      show _ = _; rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_smul, Matrix.transpose_one]
    have hSalt :
        (P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ).PosDef :=
      schurComplement_posDef hDh (hMblock ▸ hM)
    rwa [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.mul_smul] at hSalt
  have hdetS : 0 < S.det := hSpd.det_pos
  have hSI : Invertible S :=
    Matrix.invertibleOfIsUnitDet S (isUnit_iff_ne_zero.mpr hdetS.ne')
  have hPT : Pᵀ = P := by
    ext i j
    have := congrFun (congrFun hMT (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.transpose_apply, P, Matrix.toBlocks₁₁] using this

  set e : ((Fin m ⊕ Fin 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
    { toFun := fun v => ⟨v ∘ Sum.inl, v (Sum.inr 0)⟩
      invFun := fun p => Sum.elim p.1 (fun _ => p.2)
      left_inv := fun v => by funext i; cases i with
        | inl i => rfl
        | inr j => fin_cases j; rfl
      right_inv := fun p => rfl }
  set q₀u : (Fin m → ℤ) → ℝ := fun u => ∑ i, q₀ i * (u i : ℝ)

  have hQsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
          ⬝ᵥ (M *ᵥ fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = a * (a⁻¹ * q₀u u + (k : ℝ)) ^ 2 + realQuadForm S (intCastVec u) := by
    intro u k
    have hcast : (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = Sum.elim (intCastVec u) (fun _ => (k : ℝ)) := by
      funext i; cases i with | inl i => rfl | inr j => rfl
    rw [hcast, hMblock,
      schurComplement_bilin_mulVec_eq P q ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (by rw [Matrix.transpose_smul, Matrix.transpose_one])
        (intCastVec u) (fun _ => (k : ℝ))]
    have hSeq : P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ = S := by
      rw [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_smul]
    rw [hSeq]
    congr 1
    have hv : (⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ) *ᵥ intCastVec u
          + (fun _ => (k : ℝ))
        = fun _ => a⁻¹ * q₀u u + (k : ℝ) := by
      funext j
      simp only [hiD, Matrix.smul_mul, Matrix.one_mul, smul_mulVec, Matrix.mulVec,
        dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
        q₀u, q₀, intCastVec, hia, Fin.eq_zero j]
    rw [hv, smul_mulVec, Matrix.one_mulVec]
    simp only [dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    ring

  have hLsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (∑ i, b i * ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ))
        = (∑ i, b' i * (u i : ℂ)) + b₁ * (k : ℂ) := by
    intro u k
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, b', b₁,
      Function.comp_apply]

  set β : (Fin m → ℤ) → ℂ := fun u => b₁ - (t : ℂ) * (q₀u u : ℂ)
  have htare : 0 < ((t * a : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact mul_pos ht ha

  have h1D : ∀ u : Fin m → ℤ,
      (∑' k : ℤ, cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
          + 2 * π * (β u) * (k : ℂ)))
        = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
              * ((w : ℂ) + Complex.I * (β u)) ^ 2) :=
    fun u => Complex.tsum_exp_neg_quadratic htare (β u)

  set β' : ℤ → (Fin m → ℂ) :=
    fun w i => b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hqsum : ∀ u : Fin m → ℤ,
      (∑ i, (q₀ i : ℂ) * (u i : ℂ)) = ((q₀u u : ℝ) : ℂ) := fun u => by
    simp only [q₀u, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hβ'sum : ∀ (w : ℤ) (u : Fin m → ℤ), (∑ i, (β' w) i * (u i : ℂ))
      = (∑ i, b' i * (u i : ℂ))
        + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀u u : ℂ) := fun w u => by
    rw [← hqsum u]
    simp only [β', add_mul, Finset.sum_add_distrib, Finset.mul_sum]; ring_nf

  have hExpEq : ∀ (u : Fin m → ℤ) (w : ℤ),
      (-(π : ℂ) * (t : ℂ)
            * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)
          + 2 * π * (∑ i, b' i * (u i : ℂ))
          + (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * (β u)) ^ 2))
        = (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          + 2 * π * (∑ i, (β' w) i * (u i : ℂ)) := by
    intro u w
    rw [hβ'sum w u]
    simp only [β, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_inv]
    have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    field_simp
    ring_nf
    simp only [hI2]
    ring

  set Fuw : (Fin m → ℤ) × ℤ → ℂ := fun p =>
    cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)
      * thetaTerm S t (β' p.2) p.1
  have haiC : ((a : ℂ))⁻¹ = (((a⁻¹ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_inv]
  have hReβ' : ∀ w i, (β' w i).re = (b' i).re - a⁻¹ * b₁.re * q₀ i := fun w i => by
    have h1 : β' w i
        = b' i + (((a⁻¹ * q₀ i : ℝ)) : ℂ) * (Complex.I * (w : ℂ) - b₁) := by
      simp only [β', haiC]; push_cast; ring_nf; simp [Complex.I_sq]; ring
    rw [h1, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.intCast_im]
    ring
  have hR2' : Summable fun p : (Fin m → ℤ) × ℤ => ‖Fuw p‖ := by
    obtain ⟨c, hc, hQ⟩ := posDef_quadForm_lower hSpd
    set gU : Fin m → ℤ → ℝ := fun i k =>
      rexp (-(π * t * c * (k : ℝ) ^ 2)
        + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (k : ℝ))
    have hUmaj : Summable fun u : Fin m → ℤ => ∏ i, gU i (u i) :=
      summable_prod_fin (n := m) (f := gU)
        (fun _ _ => (Real.exp_pos _).le)
        (fun i => (summable_real_exp_quadratic_int (a := π * t * c) (by positivity)
            (2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i))).congr
          fun k => by unfold gU; ring_nf)
    have hWmaj : Summable fun w : ℤ =>
        ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
          * ((w : ℂ) + Complex.I * b₁) ^ 2)‖ := by
      have hcoef : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
          = (((-(π / (t * a))) : ℝ) : ℂ) := by push_cast; ring
      have hnorm : ∀ w : ℤ,
          ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)‖
            = rexp (-(π / (t * a)) * ((w : ℝ) - b₁.im) ^ 2)
              * rexp ((π / (t * a)) * b₁.re ^ 2) := fun w => by
        rw [Complex.norm_exp, hcoef, Complex.re_ofReal_mul, ← Real.exp_add]
        congr 1
        have : ((w : ℂ) + Complex.I * b₁).re = (w : ℝ) - b₁.im ∧
            ((w : ℂ) + Complex.I * b₁).im = b₁.re := by
          refine ⟨?_, ?_⟩ <;>
            simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
              Complex.intCast_im, zero_mul, one_mul, zero_sub,
              zero_add]; ring
        rw [show (((w : ℂ) + Complex.I * b₁) ^ 2).re
            = ((w : ℝ) - b₁.im) ^ 2 - b₁.re ^ 2 by
          rw [sq, Complex.mul_re, this.1, this.2]; ring]
        ring
      simp_rw [hnorm]
      exact (((summable_real_exp_quadratic_int (a := π / (t * a))
          (div_pos pi_pos (mul_pos ht ha)) (2 * (π / (t * a)) * b₁.im)).mul_left
        (rexp (-(π / (t * a)) * b₁.im ^ 2))).congr fun w => by
          rw [← Real.exp_add]; ring_nf).mul_right _

    have hbound : ∀ p : (Fin m → ℤ) × ℤ,
        ‖Fuw p‖ ≤ ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
            * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)‖ * ∏ i, gU i (p.1 i) := fun p => by
      unfold Fuw
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold thetaTerm
      rw [Complex.norm_exp,
        show (∏ i, gU i (p.1 i)) = rexp (∑ i,
          (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ))) from
          (Real.exp_sum _ _).symm]
      apply Real.exp_le_exp.mpr
      have hre : (-(π : ℂ) * (t : ℂ) * (realQuadForm S (intCastVec p.1) : ℂ)
            + 2 * π * ∑ i, (β' p.2) i * (p.1 i : ℂ)).re
          = -(π * t * realQuadForm S (intCastVec p.1))
            + 2 * π * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        have h1 : -(π : ℂ) * (t : ℂ) * (realQuadForm S (intCastVec p.1) : ℂ)
            = (((-(π * t * realQuadForm S (intCastVec p.1))) : ℝ) : ℂ) := by push_cast; ring
        have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
          Complex.re_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by
          rw [Complex.mul_re, hReβ' p.2 i, Complex.intCast_re, Complex.intCast_im,
            mul_zero, sub_zero]
      rw [hre]
      have hxx : intCastVec p.1 ⬝ᵥ intCastVec p.1 = ∑ i, (p.1 i : ℝ) ^ 2 := by
        simp only [dotProduct, intCastVec]
        exact Finset.sum_congr rfl fun i _ => (sq _).symm
      have hQv := hQ (intCastVec p.1); rw [hxx] at hQv
      have hsplit : (∑ i, (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ)))
          = -(π * t) * (c * ∑ i, (p.1 i : ℝ) ^ 2)
            + (2 * π) * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        rw [Finset.sum_add_distrib]; congr 1
        · rw [← mul_assoc, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit]
      nlinarith [mul_pos pi_pos ht]
    exact (hUmaj.mul_of_nonneg hWmaj
        (fun u => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
        (fun w => norm_nonneg _)).of_nonneg_of_le
      (fun p => norm_nonneg _)
      (fun p => by rw [mul_comm]; exact hbound p)

  have hdetM : M.det = a * S.det := by
    have hdD : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det = a := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]
    rw [hMblock, Matrix.det_fromBlocks₂₂, hdD, hiD, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Matrix.mul_smul]
  have hpref : (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
        * (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) := by
    have hta : (0 : ℝ) < t * a := mul_pos ht ha
    have htmS : (0 : ℝ) < t ^ m * S.det := mul_pos (pow_pos ht m) hdetS
    rw [one_div, ← Complex.cpow_neg,
      show ((t ^ (m + 1) * M.det : ℝ) : ℂ)
        = ((t * a : ℝ) : ℂ) * ((t ^ m * S.det : ℝ) : ℂ) by
          push_cast; rw [hdetM]; push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg hta.le htmS.le]

  set Pc : Matrix (Fin m) (Fin m) ℂ := P.map ((↑) : ℝ → ℂ)
  set qc : Matrix (Fin m) (Fin 1) ℂ := q.map ((↑) : ℝ → ℂ)
  have hqcT : qcᵀ = qᵀ.map ((↑) : ℝ → ℂ) := by
    ext i j; simp [qc, Matrix.transpose_apply, Matrix.map_apply]
  have hPcT : Pcᵀ = Pc := by
    ext i j; simp only [Pc, Matrix.transpose_apply, Matrix.map_apply]
    rw [← congrFun (congrFun hPT i) j, Matrix.transpose_apply]
  have hMc : (M.map ((↑) : ℝ → ℂ))
      = fromBlocks Pc qc qcᵀ ((a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    rw [hMblock]; ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        Pc, qc, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
        apply_ite ((↑) : ℝ → ℂ)]

  have hMI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  have hMinvC : (M⁻¹).map ((↑) : ℝ → ℂ) = (M.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : M.map ((↑) : ℝ → ℂ) * (M⁻¹).map ((↑) : ℝ → ℂ)
        = (M * M⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hSinvC' : (S⁻¹).map ((↑) : ℝ → ℂ) = (S.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : S.map ((↑) : ℝ → ℂ) * (S⁻¹).map ((↑) : ℝ → ℂ)
        = (S * S⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hdetSc : (liftToComplex S).det = ((S.det : ℝ) : ℂ) := by
    have := (RingHom.map_det Complex.ofRealHom S).symm
    simp [RingHom.mapMatrix_apply] at this
    exact this
  have hSc : liftToComplex S = Pc - qc * ⅟(a : ℂ) • qcᵀ := by
    unfold liftToComplex; rw [hS]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, Pc, qc,
      Matrix.smul_apply, Matrix.transpose_apply, Fin.sum_univ_one, hiaC, hia,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv, smul_eq_mul]
  have hScI : Invertible (Pc - qc * ⅟(a : ℂ) • qcᵀ) := by
    rw [← hSc]
    exact (liftToComplex S).invertibleOfIsUnitDet
      (hdetSc ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hdetS.ne'))
  have hSinvC : liftToComplex S⁻¹ = (Pc - qc * ⅟(a : ℂ) • qcᵀ)⁻¹ := by
    have h1 : liftToComplex S⁻¹ = (S⁻¹).map ((↑) : ℝ → ℂ) := rfl
    have h2 : S.map ((↑) : ℝ → ℂ) = liftToComplex S := rfl
    rw [h1, hSinvC', h2, hSc]
  have hDualSplit : ∀ (w' : Fin m → ℤ) (w : ℤ),
      cexp (-(π : ℂ) / (t : ℂ)
          * ((fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)
            ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
              *ᵥ fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)))
        = cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          * dualTerm S t (β' w) w' := by
    intro w' w
    set X : Fin m → ℂ := fun i => (w' i : ℂ) + Complex.I * b' i
    set Y : ℂ := (w : ℂ) + Complex.I * b₁
    have hcast : (fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
          + Complex.I * b i)
        = Sum.elim X (fun _ => Y) := by
      funext i; cases i with
      | inl i => simp [X, b']
      | inr j => fin_cases j; simp [Y, b₁]
    rw [hcast, hMinvC, hMc,
      schurComplement_inv_scalar_bilin_eq Pc qc (a : ℂ) hPcT X Y]
    unfold dualTerm complexQuadForm
    rw [hSinvC, ← Complex.exp_add]
    congr 1
    have hXshift : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0)
        = fun i => (w' i : ℂ) + Complex.I * (β' w) i := by
      funext i
      have hlhs : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        simp only [X, Y, qc, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, hiaC, q₀]
      have hrhs : (w' i : ℂ) + Complex.I * (β' w) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        have hβ'i : (β' w) i
            = b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁)
              * (q₀ i : ℂ) := rfl
        rw [hβ'i, mul_add,
          show Complex.I * (Complex.I * (a : ℂ)⁻¹
              * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
            = -((a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) by
              rw [show Complex.I * (Complex.I * (a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
                  = (Complex.I * Complex.I) * ((a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) from by ring,
                Complex.I_mul_I]; ring]
        ring
      rw [hlhs, hrhs]
    rw [hXshift, hiaC]
    have hcoef2 : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
        = (-(π : ℂ) / (t : ℂ)) * (a : ℂ)⁻¹ := by push_cast; field_simp
    rw [hcoef2, mul_add]
    ring

  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  have hA' : (Matrix.reindex eF eF M).PosDef := by
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply,
        ← congrFun (congrFun hMT (eF.symm i)) (eF.symm j), Matrix.transpose_apply]
    · intro x hx
      have hxe : (fun i => x (eF i)) ≠ 0 := fun h => hx (funext fun j => by
        have := congrFun h (eF.symm j); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hM).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial]
      refine Fintype.sum_equiv eF (fun i => x (eF i) * ∑ j, M i j * x (eF j))
        (fun i => x i * ∑ j, M (eF.symm i) (eF.symm j) * x j) fun i => ?_
      simp only [Equiv.symm_apply_apply]
      congr 1
      exact Fintype.sum_equiv eF (fun j => M i j * x (eF j))
        (fun j => M i (eF.symm j) * x j) fun j => by
          simp only [Equiv.symm_apply_apply]

  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩

  have hQeq : ∀ w : Fin (m + 1) → ℤ,
      realQuadForm (Matrix.reindex eF eF M) (intCastVec w)
        = (fun i => ((ePi w) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi w) i : ℝ)) := fun w => by
    simp only [realQuadForm, intCastVec, dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, ePi, Equiv.coe_fn_mk, Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hLeq : ∀ w : Fin (m + 1) → ℤ,
      (∑ j, (b ∘ eF.symm) j * (w j : ℂ)) = ∑ i, b i * ((ePi w) i : ℂ) := fun w =>
    Fintype.sum_equiv eF.symm _ _ fun j => by
      simp only [ePi, Equiv.coe_fn_mk, Function.comp_apply, Equiv.apply_symm_apply]

  let LB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) * t
        * (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
      + 2 * π * ∑ i, b i * (v i : ℂ))
  let RB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) / t *
      ((fun i => (v i : ℂ) + Complex.I * b i) ⬝ᵥ
        ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (v i : ℂ) + Complex.I * b i)))
  have hLBsum : Summable LB := by
    refine (Equiv.summable_iff ePi).mp
      (((summable_thetaTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show thetaTerm _ _ _ w = LB (ePi w)
    simp only [thetaTerm, LB, hQeq w, hLeq w]
  have hLHSsum : Summable fun p : (Fin m → ℤ) × ℤ => LB (e.symm p) :=
    (e.symm.summable_iff (f := LB)).mpr hLBsum

  have hRBsum : Summable RB := by
    refine (Equiv.summable_iff ePi).mp
      (((summable_dualTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show dualTerm _ _ _ w = RB (ePi w)
    simp only [dualTerm, complexQuadForm, liftToComplex, RB, Matrix.inv_reindex]
    congr 2
    simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.map_apply, ePi, Equiv.coe_fn_mk,
      Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg₂ _ rfl (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hRHSsum : Summable fun p : (Fin m → ℤ) × ℤ => RB (e.symm p) :=
    (e.symm.summable_iff (f := RB)).mpr hRBsum

  have hLHSrw : ∀ p : (Fin m → ℤ) × ℤ,
      LB (e.symm p)
        = cexp (-(π : ℂ) * t * (realQuadForm S (intCastVec p.1) : ℂ)
              + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
            + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
          * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (p.2 : ℂ) ^ 2
              + 2 * π * (β p.1) * (p.2 : ℂ)) := fun p => by
    show cexp _ = _
    rw [show e.symm p = Sum.elim p.1 (fun _ => p.2) from rfl,
      hQsplit p.1 p.2, hLsplit p.1 p.2, ← Complex.exp_add]
    congr 1; simp only [β]; push_cast; field_simp; ring

  have hFuwEq : ∀ p : (Fin m → ℤ) × ℤ,
      cexp (-(π : ℂ) * t * (realQuadForm S (intCastVec p.1) : ℂ)
            + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
          + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
        * cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * (β p.1)) ^ 2)
      = Fuw p := fun p => by
    unfold Fuw thetaTerm realQuadForm; rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have key := hExpEq p.1 p.2
    linear_combination key

  have hR2'a : Summable Fuw := hR2'.of_norm
  have hFuwcomm : (∑' u, ∑' w, Fuw (u, w)) = ∑' w, ∑' u, Fuw (u, w) :=
    (Summable.tsum_comm (f := fun u w => Fuw (u, w))
      (show Summable (Function.uncurry fun u w => Fuw (u, w)) from hR2'a)).symm
  have hRHScomm : (∑' (w' : Fin m → ℤ), ∑' (w : ℤ), RB (e.symm (w', w)))
      = ∑' (w : ℤ), ∑' (w' : Fin m → ℤ), RB (e.symm (w', w)) :=
    (Summable.tsum_comm (f := fun w' w => RB (e.symm (w', w)))
      (show Summable (Function.uncurry fun w' w => RB (e.symm (w', w))) from
        hRHSsum)).symm
  show (∑' v, LB v) = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w
  calc (∑' v, LB v)
      = ∑' p : (Fin m → ℤ) × ℤ, LB (e.symm p) := (e.symm.tsum_eq LB).symm
    _ = ∑' u : Fin m → ℤ, ∑' k : ℤ,
          cexp (-(π : ℂ) * t * (realQuadForm S (intCastVec u) : ℂ)
                + 2 * π * (∑ i, b' i * (u i : ℂ))
              + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)))
            * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
                + 2 * π * (β u) * (k : ℂ)) := by
        rw [tsum_congr hLHSrw, (hLHSsum.congr hLHSrw).tsum_prod]
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' u : Fin m → ℤ, ∑' w : ℤ, Fuw (u, w) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun u => by
          rw [tsum_mul_left, h1D u, ← mul_assoc,
            mul_comm _ (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w => hFuwEq (u, w))
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
                * ((w : ℂ) + Complex.I * b₁) ^ 2)
              * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                  * ∑' w', dualTerm S t (β' w) w') := by
        rw [hFuwcomm]
        exact congrArg _ (tsum_congr fun w => by
          simp only [Fuw]; rw [tsum_mul_left]
          exact congrArg _ (IH S hSpd ht (β' w)))
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
          * ∑' w : ℤ, ∑' w' : Fin m → ℤ, RB (e.symm (w', w)) := by
        have hperm : ∀ w : ℤ,
            cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
                * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                    * ∑' w', dualTerm S t (β' w) w')
              = (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                * ∑' w', RB (e.symm (w', w)) := fun w => by
          rw [← mul_assoc,
            mul_comm _ ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w' => (hDualSplit w' w).symm)
        rw [tsum_congr hperm, tsum_mul_left, ← mul_assoc, hpref]
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w := by
        rw [← hRHScomm, ← hRHSsum.tsum_prod, e.symm.tsum_eq]

end InductionStep

/-! ### The rank-`n` Poisson transformation law -/

section RankNGaussianPoisson

variable {n : ℕ}

-- pin: gapsw80_t2_poissonLaw_reindex (S_NumberField_exists_completedDedekindZeta_package.lean:1451)
lemma poissonLaw_reindex {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (t : ℝ) (b : Fin (m + 1) → ℂ) :
    PoissonLaw A t b ↔
      PoissonLawBlock (reindex finSumFinEquiv.symm finSumFinEquiv.symm A) t
        (b ∘ finSumFinEquiv) := by
  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  set M := reindex eF.symm eF.symm A with hM
  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩
  have hMentry : ∀ i j, M i j = A (eF i) (eF j) := fun i j => by
    simp only [hM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hdet : M.det = A.det := Matrix.det_reindex_self _ _
  have hMinv : ∀ i j, M⁻¹ i j = A⁻¹ (eF i) (eF j) := fun i j => by
    rw [hM, Matrix.inv_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hQeq : ∀ v : Fin (m + 1) → ℤ,
      realQuadForm A (intCastVec v)
        = (fun i => ((ePi v) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi v) i : ℝ)) := fun v => by
    simp only [realQuadForm, intCastVec, dotProduct, Matrix.mulVec, ePi, Equiv.coe_fn_mk,
      Function.comp_apply, hMentry]
    exact (Fintype.sum_equiv eF _ _ fun i => by
      exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)).symm
  have hLeq : ∀ v : Fin (m + 1) → ℤ,
      (∑ j, b j * (v j : ℂ)) = ∑ i, (b ∘ eF) i * ((ePi v) i : ℂ) := fun v =>
    (Fintype.sum_equiv eF _ _ fun i => rfl).symm
  have hDeq : ∀ w : Fin (m + 1) → ℤ,
      complexQuadForm (liftToComplex A⁻¹) (fun j => (w j : ℂ) + Complex.I * b j)
        = (fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i)
          ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
            *ᵥ fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i) := fun w => by
    simp only [complexQuadForm, liftToComplex, dotProduct, Matrix.mulVec, Matrix.map_apply, ePi,
      Equiv.coe_fn_mk, Function.comp_apply, hMinv]
    refine (Fintype.sum_equiv eF _ _ fun i => ?_).symm
    exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)
  have hLHSeq : (∑' v, thetaTerm A t b v)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) * t
            * (((fun i => (x i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (x i : ℝ)) : ℝ) : ℂ)
          + 2 * π * ∑ i, (b ∘ eF) i * (x i : ℂ)) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun v => by unfold thetaTerm; rw [hQeq v, hLeq v]
  have hRHSeq : (∑' w, dualTerm A t b w)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t
            * ((fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i)
              ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
                *ᵥ fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i))) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun w => by unfold dualTerm; rw [hDeq w]
  unfold PoissonLaw PoissonLawBlock
  rw [hLHSeq, hRHSeq, hdet]

-- pin: gapsw80_t2_rankNGaussianPoisson (S_NumberField_exists_completedDedekindZeta_package.lean:1505)
theorem poissonLaw_of_posDef :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin n → ℂ, PoissonLaw A t b := by
  intro n
  induction n with
  | zero =>
    intro A hA t ht b
    unfold PoissonLaw thetaTerm dualTerm realQuadForm complexQuadForm
    simp only [dotProduct, Matrix.mulVec, Finset.univ_eq_empty, Finset.sum_empty,
      Complex.ofReal_zero, mul_zero, add_zero, Complex.exp_zero, pow_zero,
      one_mul, Matrix.det_fin_zero, Complex.ofReal_one, Complex.one_cpow]
  | succ m IH =>
    intro A hA t ht b
    rw [poissonLaw_reindex]
    refine poissonLawBlock_of_poissonLaw IH _ ?_ ht _
    have hAT : Aᵀ = A := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA.1
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Equiv.symm_symm,
        ← congrFun (congrFun hAT (finSumFinEquiv i)) (finSumFinEquiv j)]
    · intro x hx
      have hxe : (fun j => x (finSumFinEquiv.symm j)) ≠ 0 := fun h =>
        hx (funext fun i => by
          have := congrFun h (finSumFinEquiv i); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hA).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial, Equiv.symm_symm]
      refine Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j => ?_
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j' => by
        simp only [Equiv.apply_symm_apply])

-- pin: gapsw80_t2_rankNGaussianPoisson_real (S_NumberField_exists_completedDedekindZeta_package.lean:1542)
theorem poissonSummation_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) {t : ℝ} (ht : 0 < t) :
    (∑' v : Fin n → ℤ,
        cexp ((-(π * t * (intCastVec v ⬝ᵥ A *ᵥ intCastVec v)) : ℝ) : ℂ))
      = (((t ^ n * A.det) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin n → ℤ,
          cexp ((-(π * (intCastVec w ⬝ᵥ A⁻¹ *ᵥ intCastVec w) / t) : ℝ) : ℂ) := by
  have h := poissonLaw_of_posDef n A hA ht (fun _ => 0)
  have hpos : (0 : ℝ) < t ^ n * A.det := mul_pos (pow_pos ht n) hA.det_pos
  have hpref : (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ n * A.det) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [show (-(1 / 2) : ℂ) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le]
  have hθ0 : ∀ v, thetaTerm A t (fun _ => 0) v
      = cexp ((-(π * t * (intCastVec v ⬝ᵥ A *ᵥ intCastVec v)) : ℝ) : ℂ) := fun v => by
    unfold thetaTerm realQuadForm
    simp only [zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    push_cast; ring_nf
  have hδ0 : ∀ w, dualTerm A t (fun _ => 0) w
      = cexp ((-(π * (intCastVec w ⬝ᵥ A⁻¹ *ᵥ intCastVec w) / t) : ℝ) : ℂ) := fun w => by
    unfold dualTerm complexQuadForm liftToComplex
    simp only [mul_zero, add_zero]
    congr 1
    have hQ : (fun i => (w i : ℂ)) ⬝ᵥ ((A⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ))
        = (((intCastVec w ⬝ᵥ A⁻¹ *ᵥ intCastVec w : ℝ)) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, intCastVec,
        Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [hQ]; push_cast; ring
  unfold PoissonLaw at h
  rw [tsum_congr hθ0, tsum_congr hδ0, hpref] at h
  exact h

end RankNGaussianPoisson

end

end NumberField.CompletedDedekindZeta
