/-
  The slash action of `SL(2, ℤ)` on a `Γ₁`-cusp form's conjugates and on a primitive form.

  * `CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj`: a `Γ₁(N)`-cusp form of weight `k` is
    determined by its conjugate `conj ∘ f`: there is a `Γ₁(N)`-form `g` with `g = conj ∘ f` and
    `qCoeff g n = conj (qCoeff f n)`.
  * `CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one`: the Fricke action — for
    `d` with `d ^ 2 = 1` there is a `Γ₁(N)`-form `g` with `g τ = d ^ k • f (d⁻¹ • τ)`.
  * `CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj`: the inverse of a primitive form (in the
    `q`-coefficient sense) is again primitive.
  * `CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm`: the Fricke pseudo-eigenvalue —
    a primitive `g` is transported along `d • ·` with a `d ^ k` factor.
  * `CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd` and
    `…_comp_heckeDiagMatrix_apply_eq_of_not_dvd`: the two halves of the `S · T^{z} · S⁻¹` coset sum —
    the sum is `q`-coefficient-readable at `d ∣ n` (`PrimitiveCosetSum`) and, in the `q ∤ n` case,
    the `heckeDiagMatrix q`-composite collapses (`OldFormCosetSum`).

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj.lean` (126 lines),
  `S_…_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.lean` (168),
  `S_…_isPrimitiveForm_inv_of_qCoeff_eq_conj.lean` (177),
  `S_…_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.lean` (115),
  `S_…_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.lean` (188) and
  `S_…_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.lean` (250), with the
  statements from the wrappers of the same names.  The pin label namespaces are word names and are kept:
  `ConjFormGamma1`, `FrickeGamma1`, `ConjPrimitiveForm`, `FrickePseudoEigenvalue`, `PrimitiveCosetSum`,
  `OldFormCosetSum`.

  Assumes from earlier modules: `ModularForms/NewformDecomposition.lean` (the eigenform decomposition),
  `ModularForms/Analytic/HeckeEigenvalueConj.lean` (the conjugate eigenvalue),
  `ModularForms/HeckeULevel.lean` (`exists_gamma1_coe_eq_heckeU_of_dvd`) and
  `ModularForms/HeckeDiagDegeneracy.lean` (the degeneracy lift).

  spec-pin: Theorems/Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj.lean
  spec-pin: Theorems/Thm_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.lean
  spec-pin: Theorems/Thm_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj.lean
  spec-pin: P2M/Sol/S_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj.lean
  spec-pin: Theorems/Thm_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.lean
  spec-pin: Theorems/Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.lean
  spec-pin: P2M/Sol/S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.lean
  spec-pin: Theorems/Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.lean
  spec-pin: P2M/Sol/S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.lean
-/
import FLTForHuman.ModularForms.NewformDecomposition
import FLTForHuman.ModularForms.Analytic.HeckeEigenvalueConj
import FLTForHuman.ModularForms.HeckeULevel
import FLTForHuman.ModularForms.HeckeDiagDegeneracy
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.HeckeNebentypusFricke
import FLTForHuman.ModularForms.HeckeFrickeTrace
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm ComplexConjugate

namespace ConjFormGamma1

def conjNeg (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have := Matrix.det_fin_two γ.1
    rw [γ.2] at this
    linear_combination (-1 : ℤ) * this⟩

@[scoped simp] theorem conjNeg_apply_00 (γ : SL(2, ℤ)) : (conjNeg γ) 0 0 = γ 0 0 := rfl

@[scoped simp] theorem conjNeg_apply_01 (γ : SL(2, ℤ)) : (conjNeg γ) 0 1 = -γ 0 1 := rfl

@[scoped simp] theorem conjNeg_apply_10 (γ : SL(2, ℤ)) : (conjNeg γ) 1 0 = -γ 1 0 := rfl

@[scoped simp] theorem conjNeg_apply_11 (γ : SL(2, ℤ)) : (conjNeg γ) 1 1 = γ 1 1 := rfl

theorem conjNeg_conjNeg (γ : SL(2, ℤ)) : conjNeg (conjNeg γ) = γ := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjNeg]

theorem conjNeg_mem_Gamma1_iff (M : ℕ) (γ : SL(2, ℤ)) :
    conjNeg γ ∈ Gamma1 M ↔ γ ∈ Gamma1 M := by
  simp only [Gamma1_mem, conjNeg_apply_00, conjNeg_apply_11, conjNeg_apply_10, Int.cast_neg,
    neg_eq_zero]

theorem J_mul_coe_mul_J (γ : SL(2, ℤ)) :
    J * (γ : GL (Fin 2) ℝ) * J = ((conjNeg γ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_matrix_coe] <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, conjNeg, Matrix.vecMul, dotProduct]

open ConjAct Pointwise

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem J_inv : (J : GL (Fin 2) ℝ)⁻¹ = J := by
  rw [inv_eq_iff_mul_eq_one, ← sq, J_sq]

theorem mem_map_Gamma1_iff (M : ℕ) (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (γ : GL (Fin 2) ℝ) = x :=
  Subgroup.mem_map

theorem J_mul_mul_J_mem (M : ℕ) {x : GL (Fin 2) ℝ} (hx : x ∈ (Γ₁ℝ M)) : J * x * J ∈ (Γ₁ℝ M) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff M x).1 hx
  rw [J_mul_coe_mul_J]
  exact (mem_map_Gamma1_iff M _).2 ⟨conjNeg γ, (conjNeg_mem_Gamma1_iff M γ).2 hγ, rfl⟩

theorem toConjAct_J_inv_smul (M : ℕ) : toConjAct (J : GL (Fin 2) ℝ)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul,
    J_inv]
  constructor
  · intro h
    have := J_mul_mul_J_mem M h
    rwa [← mul_assoc, ← mul_assoc, ← sq, J_sq, one_mul, mul_assoc, ← sq, J_sq, mul_one] at this
  · exact J_mul_mul_J_mem M

theorem slash_J_apply (f : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (f ∣[k] J) τ = conj (f (ofComplex (-conj (τ : ℂ)))) := by
  simp [ModularForm.slash_def, J_smul]

noncomputable def conjForm {M : ℕ} {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k :=
  (CuspForm.translate g J).copy (fun τ => conj (g (ofComplex (-conj (τ : ℂ)))))
    (by funext τ; rw [CuspForm.translate]; exact (slash_J_apply g k τ).symm)
    (toConjAct_J_inv_smul M).symm

theorem conjForm_apply {M : ℕ} {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    conjForm g τ = conj (g (ofComplex (-conj (τ : ℂ)))) := rfl

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem conj_qParam_J_smul (τ : ℍ) :
    conj (Function.Periodic.qParam 1 (↑(J • τ) : ℂ)) = Function.Periodic.qParam 1 (τ : ℂ) := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_conj, coe_J_smul]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_neg,
    Complex.conj_conj, Complex.ofReal_one, div_one]
  ring

theorem qCoeff_conjForm {M : ℕ} {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    ModularFormClass.qCoeff (conjForm g) n = conj (ModularFormClass.qCoeff g n) := by
  have hbdd : IsBoundedAtImInfty (g : ℍ → ℂ) := by
    have hcusp : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
      ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
    exact ModularFormClass.bdd_at_infty g
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => conj ((qExpansion 1 g).coeff m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (conjForm g τ) := by
    intro τ
    have h := UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods M))
      (CuspForm.holo' g) hbdd (J • τ)
    have h' := h.map (starRingEnd ℂ) Complex.continuous_conj
    rw [conjForm_apply, ← J_smul]
    convert h' using 1
    funext m
    simp only [Function.comp_apply, smul_eq_mul, map_mul, map_pow, conj_qParam_J_smul]
  symm
  exact ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods M)
    (f := conjForm g) hsum n

end ConjFormGamma1

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
    (M : ℕ) (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ g' : CuspForm (Gamma1 M) k,
      (∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = -(starRingEnd ℂ (τ : ℂ)) →
        g' τ = starRingEnd ℂ (g τ')) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n) := by
  refine ⟨ConjFormGamma1.conjForm g, fun τ τ' h => ?_, ConjFormGamma1.qCoeff_conjForm g⟩
  rw [ConjFormGamma1.conjForm_apply]
  congr 2
  apply UpperHalfPlane.ext
  rw [h, UpperHalfPlane.ofComplex_apply_of_im_pos]
  simpa using τ.im_pos

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace FrickeGamma1

open ConjAct Pointwise

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) [NeZero M]

noncomputable def frickeGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem det_frickeGL_pos : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

variable {M}

def frickeConj (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / M); -(M * γ 0 1), γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have h1 := Matrix.det_fin_two γ.1
    rw [γ.2] at h1
    obtain ⟨c', hc'⟩ := hγ
    have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [hc', Int.mul_ediv_cancel_left _ hM]
    rw [hc'] at h1
    linear_combination (-1 : ℤ) * h1⟩

theorem frickeConj_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ hd : (M : ℤ) ∣ γ 1 0, frickeConj γ hd ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  have hdvd : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 hc
  refine ⟨hdvd, ?_⟩
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · show (((γ 1 1 : ℤ)) : ZMod M) = 1; exact hd
  · show (((γ 0 0 : ℤ)) : ZMod M) = 1; exact ha
  · show (((-(M * γ 0 1) : ℤ)) : ZMod M) = 0
    rw [Int.cast_neg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, neg_zero]

theorem coe_frickeConj (γ : SL(2, ℤ)) (c' : ℤ) (hc' : γ 1 0 = M * c') :
    ((frickeConj γ ⟨c', hc'⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 1 1, -c'; -(M * γ 0 1), γ 0 0] := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hq : γ 1 0 / M = c' := by rw [hc', Int.mul_ediv_cancel_left _ hM]
  simp [frickeConj, hq]

theorem frickeGL_mul_coe (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * (γ : GL (Fin 2) ℝ) = ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) * frickeGL M := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

theorem coe_mul_frickeGL (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    (γ : GL (Fin 2) ℝ) * frickeGL M = frickeGL M * ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem mem_map_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (γ : GL (Fin 2) ℝ) = x :=
  Subgroup.mem_map

theorem frickeGL_mul_mul_inv_mem {x : GL (Fin 2) ℝ} (hx : x ∈ (Γ₁ℝ M)) :
    frickeGL M * x * (frickeGL M)⁻¹ ∈ (Γ₁ℝ M) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff x).1 hx
  obtain ⟨hd, hmem⟩ := frickeConj_mem_Gamma1 hγ
  rw [frickeGL_mul_coe γ hd, mul_inv_cancel_right]
  exact (mem_map_Gamma1_iff _).2 ⟨_, hmem, rfl⟩

theorem frickeGL_inv_mul_mul_mem {x : GL (Fin 2) ℝ} (hx : x ∈ (Γ₁ℝ M)) :
    (frickeGL M)⁻¹ * x * frickeGL M ∈ (Γ₁ℝ M) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff x).1 hx
  obtain ⟨hd, hmem⟩ := frickeConj_mem_Gamma1 hγ
  rw [mul_assoc, coe_mul_frickeGL γ hd, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (mem_map_Gamma1_iff _).2 ⟨_, hmem, rfl⟩

theorem toConjAct_frickeGL_inv_smul :
    toConjAct (frickeGL M)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    have := frickeGL_inv_mul_mul_mem h
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] at this
  · exact frickeGL_mul_mul_inv_mem

theorem coe_frickeGL_smul (τ : ℍ) : (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem denom_frickeGL (τ : ℍ) : UpperHalfPlane.denom (frickeGL M) τ = (M : ℂ) * (τ : ℂ) := by
  simp [UpperHalfPlane.denom]

theorem slash_frickeGL_apply (f : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (f ∣[k] frickeGL M) τ = (M : ℂ)⁻¹ * (τ : ℂ) ^ (-k) * f (frickeGL M • τ) := by
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, ite_eq_left (det_frickeGL_pos M), det_frickeGL,
    denom_frickeGL]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [ContinuousAlgEquiv.refl_apply,
    abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M) : (0 : ℝ) < M),
    Complex.ofReal_natCast, mul_zpow, zpow_neg (M : ℂ) k, zpow_sub_one₀ hM]
  field_simp

noncomputable def frickeForm {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k :=
  ((M : ℝ) • CuspForm.translate g (frickeGL M)).copy
    (fun τ => (τ : ℂ) ^ (-k) * g (frickeGL M • τ))
    (by
      funext τ
      rw [FunLike.coe_smul, Pi.smul_apply, CuspForm.translate]
      show _ = (M : ℝ) • ((⇑g ∣[k] frickeGL M) τ)
      rw [slash_frickeGL_apply, Complex.real_smul, Complex.ofReal_natCast]
      have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
      field_simp)
    (toConjAct_frickeGL_inv_smul).symm

theorem frickeForm_apply {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    frickeForm g τ = (τ : ℂ) ^ (-k) * g (frickeGL M • τ) := rfl

theorem eq_frickeGL_smul {τ τ' : ℍ} (h : (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1) :
    τ' = frickeGL M • τ := by
  apply UpperHalfPlane.ext
  rw [coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp
  linear_combination h

theorem apply_eq_zpow_mul_frickeForm {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) {τ τ' : ℍ}
    (h : (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1) :
    g τ' = (τ : ℂ) ^ k * frickeForm g τ := by
  rw [frickeForm_apply, eq_frickeGL_smul h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero τ),
    add_neg_cancel, zpow_zero, one_mul]

end FrickeGamma1

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one
    (M : ℕ) [NeZero M] (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ h : CuspForm (Gamma1 M) k,
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = (τ : ℂ) ^ k * h τ :=
  ⟨FrickeGamma1.frickeForm g, fun _ _ h => FrickeGamma1.apply_eq_zpow_mul_frickeForm g h⟩

open CongruenceSubgroup ModularFormClass UpperHalfPlane Function
open scoped MatrixGroups ComplexConjugate


namespace ConjPrimitiveForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ M) k) : Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M)

theorem bdd (f : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑f) := by
  have hcusp : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty f

theorem eq_of_qCoeff_eq (f₁ f₂ : CuspForm (Γ₁ℝ M) k) (h : ∀ n : ℕ, qCoeff f₁ n = qCoeff f₂ n) :
    f₁ = f₂ :=
  DFunLike.ext' (UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic f₁) f₁.holo' (bdd f₁)
    (periodic f₂) f₂.holo' (bdd f₂) h)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem eq_zero_of_qCoeff (f : CuspForm (Γ₁ℝ M) k) (h : ∀ n : ℕ, qCoeff f n = 0) : f = 0 :=
  eq_of_qCoeff_eq f 0 (fun n => by rw [h n, FunLike.coe_zero, qCoeff_zero_fun])

theorem conj_natCast_zpow (p : ℕ) (m : ℤ) : conj ((p : ℂ) ^ m) = (p : ℂ) ^ m := by
  rw [map_zpow₀, Complex.conj_natCast]

theorem conj_intCast (n : ℤ) : conj (n : ℂ) = n := map_intCast _ n

theorem conj_dirichlet [NeZero M] (ε : DirichletCharacter ℂ M) (a : ZMod M) :
    conj (ε a) = ε⁻¹ a := by
  have := MulChar.star_apply' ε a
  rwa [RCLike.star_def] at this

theorem conj_ite (P : Prop) [Decidable P] (a : ℂ) :
    conj (if P then a else 0) = if P then conj a else 0 := by
  split_ifs <;> simp

theorem conj_hecke_rel [NeZero M] (ε : DirichletCharacter ℂ M) (a : ℕ → ℂ) (p : ℕ) (lam : ℂ)
    (h : ∀ n : ℕ, a (p * n) + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then a (n / p) else 0) = lam * a n) (n : ℕ) :
    conj (a (p * n)) + ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then conj (a (n / p)) else 0) = conj lam * conj (a n) := by
  have := congrArg conj (h n)
  rw [map_add, map_mul, map_mul, map_mul, conj_dirichlet, conj_natCast_zpow, conj_ite] at this
  exact this

def conjNeg (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have := Matrix.det_fin_two γ.1
    rw [γ.2] at this
    linear_combination (-1 : ℤ) * this⟩

@[scoped simp] theorem conjNeg_apply_00 (γ : SL(2, ℤ)) : (conjNeg γ) 0 0 = γ 0 0 := rfl

@[scoped simp] theorem conjNeg_apply_01 (γ : SL(2, ℤ)) : (conjNeg γ) 0 1 = -γ 0 1 := rfl

@[scoped simp] theorem conjNeg_apply_10 (γ : SL(2, ℤ)) : (conjNeg γ) 1 0 = -γ 1 0 := rfl

@[scoped simp] theorem conjNeg_apply_11 (γ : SL(2, ℤ)) : (conjNeg γ) 1 1 = γ 1 1 := rfl

theorem conjNeg_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : conjNeg γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at hγ ⊢
  simp [hγ]

def negConj (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

@[scoped simp] theorem coe_negConj (τ : ℍ) : ((negConj τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

theorem coe_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

theorem coe_conjNeg_smul_negConj (γ : SL(2, ℤ)) (τ : ℍ) :
    ((conjNeg γ • negConj τ : ℍ) : ℂ) = -conj ((γ • τ : ℍ) : ℂ) := by
  rw [coe_sl_smul, coe_sl_smul, map_div₀]
  simp only [conjNeg_apply_00, conjNeg_apply_01, conjNeg_apply_10, conjNeg_apply_11, coe_negConj,
    Int.cast_neg, map_add, map_mul, conj_intCast]
  have e1 : ((γ 0 0 : ℤ) : ℂ) * -conj (τ : ℂ) + -((γ 0 1 : ℤ) : ℂ) =
      -(((γ 0 0 : ℤ) : ℂ) * conj (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) := by ring
  have e2 : -((γ 1 0 : ℤ) : ℂ) * -conj (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) =
      ((γ 1 0 : ℤ) : ℂ) * conj (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by ring
  rw [e1, e2, neg_div]

theorem hasNebentypus_inv_of_conj [NeZero M] {ε : DirichletCharacter ℂ M}
    {f f' : CuspForm (Γ₁ℝ M) k} (hf : CuspForm.HasNebentypus ε f)
    (hf' : ∀ τ τ' : ℍ, (τ' : ℂ) = -conj (τ : ℂ) → f' τ = conj (f τ')) :
    CuspForm.HasNebentypus ε⁻¹ f' := by
  intro γ hγ τ
  have h1 : f' (γ • τ) = conj (f (conjNeg γ • negConj τ)) :=
    hf' (γ • τ) (conjNeg γ • negConj τ) (coe_conjNeg_smul_negConj γ τ)
  have h2 := hf (conjNeg γ) (conjNeg_mem_Gamma0 hγ) (negConj τ)
  have h3 : f' τ = conj (f (negConj τ)) := hf' τ (negConj τ) rfl
  rw [h1, h2, map_mul, map_mul, conjNeg_apply_11, conjNeg_apply_10, conj_dirichlet, ← h3,
    map_zpow₀, map_add, map_mul]
  simp only [Int.cast_neg, map_neg, conj_intCast, coe_negConj, Complex.conj_conj,
    neg_mul_neg]

variable [NeZero M]

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Γ₁ℝ M) k)
    (hg' : ∀ n : ℕ, qCoeff g' n = conj (qCoeff g n)) :
    CuspForm.IsPrimitiveForm ε⁻¹ g' := by

  obtain ⟨g'', hpt, hcoef⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M k g
  have hgg : g' = g'' := eq_of_qCoeff_eq g' g'' (fun n => by rw [hg', hcoef])
  subst hgg
  have heig := hg.isEigenformWith
  refine ⟨⟨?_, ?_, ?_, hasNebentypus_inv_of_conj heig.hasNebentypus hpt⟩, ?_⟩
  · rw [hg', heig.qCoeff_one, map_one]
  · intro p hp hpM n
    have := conj_hecke_rel (k := k) ε (fun n => qCoeff g n) p (qCoeff g p)
      (heig.hecke_of_not_dvd hp hpM) n
    rw [hg', hg', hg', hg']
    exact this
  · intro ℓ hℓ hℓM n
    rw [hg', hg', hg', heig.hecke_of_dvd hℓ hℓM n, map_mul]
  ·
    intro M' hM' hne hocc
    have hne' : NeZero M' := ⟨fun h0 => NeZero.ne M (zero_dvd_iff.1 (h0 ▸ hM'))⟩
    obtain ⟨ε', h', hh'0, hh'neb, S, hS⟩ := hocc
    obtain ⟨h'', hpt'', hcoef''⟩ :=
      CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M' k h'
    apply hg.not_eigenpacketOccursAt hM' hne
    refine ⟨ε'⁻¹, h'', ?_, hasNebentypus_inv_of_conj hh'neb hpt'', S, fun p hp hpS => ⟨?_, ?_⟩⟩
    · intro h0
      apply hh'0
      apply eq_zero_of_qCoeff
      intro n
      have := hcoef'' n
      rw [h0, FunLike.coe_zero, qCoeff_zero_fun] at this
      have := congrArg conj this
      rwa [map_zero, Complex.conj_conj, eq_comm] at this
    · have h1 : ε' (p : ZMod M') = ε⁻¹ (p : ZMod M) := (hS p hp hpS).1
      show ε'⁻¹ (p : ZMod M') = ε (p : ZMod M)
      rw [MulChar.inv_apply_eq_inv', h1, MulChar.inv_apply_eq_inv', inv_inv]
    · intro n
      have hrel := (hS p hp hpS).2
      have hthis := conj_hecke_rel (k := k) ε' (fun n => qCoeff h' n) p (qCoeff g' p) hrel n
      simp only [hcoef'']
      rw [hg' p, Complex.conj_conj] at hthis
      exact hthis

end ConjPrimitiveForm

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    CuspForm.IsPrimitiveForm ε⁻¹ g' :=
  ConjPrimitiveForm.main ε g hg g' hg'

open CongruenceSubgroup ModularFormClass UpperHalfPlane
open scoped MatrixGroups ComplexConjugate


namespace FrickePseudoEigenvalue

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, FunLike.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, qCoeff g' n = conj (qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = c * (τ : ℂ) ^ k * g' τ := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have heig := hg.isEigenformWith

  obtain ⟨h, hh⟩ := CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one M k g

  obtain ⟨hneb, hhecke⟩ :=
    CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke M k ε g h heig.hasNebentypus hh

  have hadj : ∀ p : ℕ, p.Prime → ¬ p ∣ M →
      conj (qCoeff g p) = ε⁻¹ (p : ZMod M) * qCoeff g p := fun p hp hpM =>
    CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M k ε g hg0 heig.hasNebentypus p hp hpM
      (qCoeff g p) (heig.hecke_of_not_dvd hp hpM)

  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'

  have hmult : h = qCoeff h 1 • g' := by
    refine CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M k ε⁻¹ g' hg'prim h hneb ∅
      (fun p hp _ hpM n => ?_)
    rw [hg' p, hadj p hp hpM]
    exact hhecke p hp hpM (qCoeff g p) (heig.hecke_of_not_dvd hp hpM) n

  refine ⟨qCoeff h 1, fun hc => hg0 ?_, fun τ τ' hτ => ?_⟩
  ·
    rw [hc, zero_smul] at hmult
    apply DFunLike.ext
    intro τ'
    have key := hh (frickeGL M • τ') τ' (by
      have := frickeGL_smul_mul M τ'
      linear_combination this)
    rw [key, hmult, zero_apply, mul_zero, zero_apply]
  · have hpt : h τ = qCoeff h 1 * g' τ := by
      have := congrArg (fun F : CuspForm (Gamma1 M) k => F τ) hmult
      simpa only [smul_apply, smul_eq_mul] using this
    rw [hh τ τ' hτ, hpt]
    ring

end FrickePseudoEigenvalue

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) ^ k * g' τ :=
  FrickePseudoEigenvalue.main ε g hg g' hg'

open CongruenceSubgroup ModularFormClass UpperHalfPlane ModularForm
open scoped MatrixGroups ComplexConjugate ModularForm


namespace PrimitiveCosetSum

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Function.Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  have hcusp : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, FunLike.coe_smul, qExpansion_smul (analytic f), map_smul,
    smul_eq_mul]

end QCoeff

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem coe_frickeGL_smul (M : ℕ) [NeZero M] (τ : ℍ) :
    (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, FunLike.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (τ : ℍ) :
    ∑ j ∈ Finset.range q,
        ((⇑g : ℍ → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (M / q : ℕ)) * ModularGroup.S⁻¹ :
            SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * conj (qCoeff g q) * g (heckeMatrix q 0 • τ) := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M

  obtain ⟨g', -, hg'⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M k g
  obtain ⟨c, hc0, hc⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε g hg g' hg'
  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'
  have hgg' : ∀ n : ℕ, qCoeff g n = conj (qCoeff g' n) := fun n => by
    rw [hg' n, Complex.conj_conj]
  obtain ⟨c', -, hc'⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε⁻¹ g' hg'prim g hgg'

  have hcc' : c * c' = (-(M : ℂ)) ^ k := by
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, g τ₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hg0 (DFunLike.ext g 0 fun τ => by rw [h τ, zero_apply])
    set W : ℍ := frickeGL M • τ₀ with hW
    have hrelW : (W : ℂ) * ((M : ℂ) * (τ₀ : ℂ)) = -1 := frickeGL_smul_mul M τ₀
    have hrel0 : (τ₀ : ℂ) * ((M : ℂ) * (W : ℂ)) = -1 := by linear_combination hrelW
    have h1 : g τ₀ = c * (W : ℂ) ^ k * g' W := hc W τ₀ hrel0
    have h2 : g' W = c' * (τ₀ : ℂ) ^ k * g τ₀ := hc' τ₀ W hrelW
    have hWτ : (W : ℂ) * (τ₀ : ℂ) = -1 / (M : ℂ) := by
      have hτ₀ne : (τ₀ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ₀
      field_simp
      linear_combination hrelW
    have h3 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k * g τ₀ = g τ₀ := by
      rw [mul_zpow]
      calc c * c' * ((W : ℂ) ^ k * (τ₀ : ℂ) ^ k) * g τ₀
          = c * (W : ℂ) ^ k * (c' * (τ₀ : ℂ) ^ k * g τ₀) := by ring
        _ = g τ₀ := by rw [← h2, ← h1]
    have h4 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k = 1 := by
      have := mul_right_cancel₀ hτ₀ (h3.trans (one_mul (g τ₀)).symm)
      exact this
    rw [hWτ] at h4
    have hMk : (-(M : ℂ)) ^ k ≠ 0 := zpow_ne_zero k (neg_ne_zero.mpr hMC)
    have h5 : (-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k = 1 := by
      rw [← mul_zpow, show (-1 / (M : ℂ)) * (-(M : ℂ)) = 1 by field_simp, one_zpow]
    calc c * c' = c * c' * ((-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k) := by rw [h5, mul_one]
      _ = (c * c' * (-1 / (M : ℂ)) ^ k) * (-(M : ℂ)) ^ k := by ring
      _ = (-(M : ℂ)) ^ k := by rw [h4, one_mul]

  set H : CuspForm (Γ₁ℝ M) k := c • g' with hHdef
  have hH : ∀ τ : ℍ, H τ = c * g' τ := fun τ => by
    rw [hHdef, smul_apply, smul_eq_mul]
  obtain ⟨U, hUcoe, hUcoef, -⟩ := CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k hqM H
  have heig := hg.isEigenformWith
  have hUeq : U = conj (qCoeff g q) • H := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods M) fun n => ?_
    rw [hUcoef n, qCoeff_smul, hHdef, qCoeff_smul, qCoeff_smul, hg', hg',
      heig.hecke_of_dvd hq hqM n, map_mul]
    ring
  have hUfun : heckeU k q (⇑H) = fun τ => conj (qCoeff g q) * (c * g' τ) := by
    rw [← hUcoe, hUeq]
    funext τ
    rw [smul_apply, smul_eq_mul, hH]

  have key := UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU M k
    hq.ne_zero hqM (⇑g) (⇑H) (fun τ => conj (qCoeff g q) * (c * c') * g τ)
    (fun τ τ' hττ' => by rw [hH, hc τ τ' hττ']; ring)
    (fun τ τ' hττ' => by
      rw [hUfun]
      simp only
      rw [hc' τ τ' hττ']; ring)
    τ
  rw [key, hcc']
  have hMk : (-(M : ℂ)) ^ k ≠ 0 := zpow_ne_zero k (neg_ne_zero.mpr hMC)
  rw [zpow_neg]
  field_simp

end PrimitiveCosetSum

open scoped MatrixGroups ModularForm in

theorem CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((⇑g : UpperHalfPlane → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (M / q : ℕ)) * ModularGroup.S⁻¹ :
            SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) *
          g (ModularForm.heckeMatrix q 0 • τ) :=
  PrimitiveCosetSum.main ε g hg hq hqM τ

open CongruenceSubgroup ModularFormClass UpperHalfPlane ModularForm
open scoped MatrixGroups ComplexConjugate ModularForm


namespace OldFormCosetSum

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Function.Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  have hcusp : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, FunLike.coe_smul, qExpansion_smul (analytic f), map_smul,
    smul_eq_mul]

end QCoeff

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem coe_frickeGL_smul (M : ℕ) [NeZero M] (τ : ℍ) :
    (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, FunLike.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem qCoeff_sub (f g : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  have hM : M ≠ 0 := NeZero.ne M
  have hpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hper : Function.Periodic ((⇑f) ∘ ofComplex) 1 := periodic f
  rw [qCoeff, qCoeff, qCoeff, FunLike.coe_sub, qExpansion_sub (analytic f) (analytic g), map_sub]

theorem heckeDiagMatrix_smul_heckeMatrix_smul {q : ℕ} (hq : q ≠ 0) (τ : ℍ) :
    heckeDiagMatrix q • (heckeMatrix q 0 • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul hq, ModularForm.coe_heckeMatrix_smul hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast; field_simp; ring

theorem heckeMatrix_smul_heckeDiagMatrix_smul {q : ℕ} (hq : q ≠ 0) (τ : ℍ) :
    heckeMatrix q 0 • (heckeDiagMatrix q • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeMatrix_smul hq, ModularForm.coe_heckeDiagMatrix_smul hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast; field_simp; ring

theorem heckeDiagMatrix_one_smul (τ : ℍ) : heckeDiagMatrix 1 • τ = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul one_ne_zero]
  push_cast; ring

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (τ : ℍ) :
    ∑ j ∈ Finset.range q,
        ((fun σ : ℍ => g (heckeDiagMatrix q • σ)) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * M) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * conj (qCoeff g q) * g τ
          - conj (ε (q : ZMod M)) * (q : ℂ) ^ (-k) * g (heckeMatrix q 0 • τ) := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hNe : NeZero (q * M) := ⟨mul_ne_zero hq0 (NeZero.ne M)⟩

  obtain ⟨g', -, hg'⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M k g
  obtain ⟨c, hc0, hc⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε g hg g' hg'
  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'
  have hgg' : ∀ n : ℕ, qCoeff g n = conj (qCoeff g' n) := fun n => by
    rw [hg' n, Complex.conj_conj]
  obtain ⟨c', -, hc'⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε⁻¹ g' hg'prim g hgg'

  have hcc' : c * c' = (-(M : ℂ)) ^ k := by
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, g τ₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hg0 (DFunLike.ext g 0 fun τ => by rw [h τ, zero_apply])
    set W : ℍ := frickeGL M • τ₀ with hW
    have hrelW : (W : ℂ) * ((M : ℂ) * (τ₀ : ℂ)) = -1 := frickeGL_smul_mul M τ₀
    have hrel0 : (τ₀ : ℂ) * ((M : ℂ) * (W : ℂ)) = -1 := by linear_combination hrelW
    have h1 : g τ₀ = c * (W : ℂ) ^ k * g' W := hc W τ₀ hrel0
    have h2 : g' W = c' * (τ₀ : ℂ) ^ k * g τ₀ := hc' τ₀ W hrelW
    have hWτ : (W : ℂ) * (τ₀ : ℂ) = -1 / (M : ℂ) := by
      have hτ₀ne : (τ₀ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ₀
      field_simp
      linear_combination hrelW
    have h3 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k * g τ₀ = g τ₀ := by
      rw [mul_zpow]
      calc c * c' * ((W : ℂ) ^ k * (τ₀ : ℂ) ^ k) * g τ₀
          = c * (W : ℂ) ^ k * (c' * (τ₀ : ℂ) ^ k * g τ₀) := by ring
        _ = g τ₀ := by rw [← h2, ← h1]
    have h4 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k = 1 := by
      have := mul_right_cancel₀ hτ₀ (h3.trans (one_mul (g τ₀)).symm)
      exact this
    rw [hWτ] at h4
    have h5 : (-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k = 1 := by
      rw [← mul_zpow, show (-1 / (M : ℂ)) * (-(M : ℂ)) = 1 by field_simp, one_zpow]
    calc c * c' = c * c' * ((-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k) := by rw [h5, mul_one]
      _ = (c * c' * (-1 / (M : ℂ)) ^ k) * (-(M : ℂ)) ^ k := by ring
      _ = (-(M : ℂ)) ^ k := by rw [h4, one_mul]

  obtain ⟨G', hG'fun, hG'coef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (M := M) (N := q * M) (d := 1) ⟨q, by ring⟩ g'
  obtain ⟨Gq', hGq'fun, hGq'coef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (M := M) (N := q * M) (d := q) ⟨1, by ring⟩ g'
  have hG'val : ∀ σ : ℍ, G' σ = g' σ := fun σ => by rw [hG'fun σ, heckeDiagMatrix_one_smul]
  have hG'c : ∀ n : ℕ, qCoeff G' n = conj (qCoeff g n) := fun n => by
    rw [hG'coef n, ite_eq_left (one_dvd n), Nat.div_one, hg']
  have hGq'c : ∀ n : ℕ, qCoeff Gq' n = if q ∣ n then conj (qCoeff g (n / q)) else 0 := fun n => by
    rw [hGq'coef n]
    split_ifs <;> simp [hg']

  obtain ⟨U, hUcoe, hUcoef, -⟩ :=
    CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k (dvd_mul_right q M) (c • G')
  have heig := hg.isEigenformWith
  have hqk : conj ((q : ℂ) ^ (k - 1)) = (q : ℂ) ^ (k - 1) := by
    rw [map_zpow₀, Complex.conj_natCast]
  have hUeq : U = (c * conj (qCoeff g q)) • G' - (c * conj (ε (q : ZMod M)) * (q : ℂ) ^ (k - 1)) • Gq' := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods (q * M)) fun n => ?_
    rw [hUcoef n, qCoeff_smul, qCoeff_sub, qCoeff_smul, qCoeff_smul, hG'c, hG'c, hGq'c]
    have hrel := heig.hecke_of_not_dvd hq hqM n
    have hrel' : qCoeff g (q * n) = qCoeff g q * qCoeff g n
        - ε (q : ZMod M) * (q : ℂ) ^ (k - 1) * (if q ∣ n then qCoeff g (n / q) else 0) := by
      linear_combination hrel
    rw [hrel', map_sub, map_mul, map_mul, map_mul, hqk]
    split_ifs with hqn
    · ring
    · simp only [map_zero, mul_zero]; ring
  have hUval : ∀ σ : ℍ, heckeU k q (fun σ => c * g' σ) σ
      = c * conj (qCoeff g q) * g' σ
        - c * conj (ε (q : ZMod M)) * (q : ℂ) ^ (k - 1) * g' (heckeDiagMatrix q • σ) := by
    intro σ
    have hcG' : (fun σ => c * g' σ) = ⇑(c • G') := by
      funext σ; rw [smul_apply, smul_eq_mul, hG'val]
    rw [hcG', ← hUcoe, hUeq, sub_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
      hG'val, hGq'fun]

  have hcast : ((q * M : ℕ) : ℂ) = (q : ℂ) * (M : ℂ) := by push_cast; ring
  have key := UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU (q * M) k
    hq0 (dvd_mul_right q M) (fun σ : ℍ => g (heckeDiagMatrix q • σ)) (fun σ => c * g' σ)
    (fun σ => c * c' * (conj (qCoeff g q) * (q : ℂ) ^ k * g (heckeDiagMatrix q • σ)
        - conj (ε (q : ZMod M)) * (q : ℂ) ^ (k - 1) * g σ))
    (fun σ τ' hστ' => by

      have hrel : ((heckeDiagMatrix q • τ' : ℍ) : ℂ) * ((M : ℂ) * (σ : ℂ)) = -1 := by
        rw [ModularForm.coe_heckeDiagMatrix_smul hq0]; rw [hcast] at hστ'; linear_combination hστ'
      rw [hc σ _ hrel]; ring)
    (fun σ τ' hστ' => by
      rw [hUval]

      have hrela : (τ' : ℂ) * ((M : ℂ) * ((heckeDiagMatrix q • σ : ℍ) : ℂ)) = -1 := by
        rw [ModularForm.coe_heckeDiagMatrix_smul hq0]; rw [hcast] at hστ'; linear_combination hστ'
      have hrelb : ((heckeDiagMatrix q • τ' : ℍ) : ℂ) * ((M : ℂ) * (σ : ℂ)) = -1 := by
        rw [ModularForm.coe_heckeDiagMatrix_smul hq0]; rw [hcast] at hστ'; linear_combination hστ'
      rw [hc' _ τ' hrela, hc' σ _ hrelb, ModularForm.coe_heckeDiagMatrix_smul hq0, mul_zpow]
      ring)
    τ
  rw [Nat.mul_div_cancel_left M hq.pos] at key
  rw [key, heckeDiagMatrix_smul_heckeMatrix_smul hq0, hcc', hcast]
  have hMk : (-(M : ℂ)) ^ k ≠ 0 := zpow_ne_zero k (neg_ne_zero.mpr hMC)
  have hqk' : (q : ℂ) ^ k ≠ 0 := zpow_ne_zero k hqC
  rw [show -((q : ℂ) * (M : ℂ)) = (q : ℂ) * (-(M : ℂ)) by ring, mul_zpow, zpow_neg, zpow_neg,
    zpow_sub₀ hqC, zpow_sub₀ hqC, zpow_one]
  field_simp

end OldFormCosetSum

open scoped MatrixGroups ModularForm in

theorem CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((fun σ : UpperHalfPlane => g (ModularForm.heckeDiagMatrix q • σ)) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * M) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) * g τ
          - starRingEnd ℂ (ε (q : ZMod M)) * (q : ℂ) ^ (-k) *
              g (ModularForm.heckeMatrix q 0 • τ) :=
  OldFormCosetSum.main ε g hg hq hqM τ


end
