/-
  **Reserve: the χ₋₃ weight-one Eisenstein development's dead, project-unique declarations.**

  Moved verbatim out of `FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean`.
  Each is unreachable from that module's five public headlines and is the project's only
  copy of its statement: `tools/deps/shapes.py` finds no same-shape declaration in the pin
  (718 874 declarations, corpus `aa2d8b3`) or in any other port module.  The dead
  declarations that *do* have same-shape copies in unported pin files were left in the
  headline module, which is where they are to be refactored; see `CHI-NEG-THREE-DEAD.md`.

  One companion (`hexThetaH_ne_zero`, not unique) travels with them because it mentions
  two of them and would otherwise be left dangling.

  Provenance: `S_EisensteinWeightOne_e1Chi3IsModular.lean@aa2d8b3`, sections
  `File_FLT_AnalyticCore_*` (the pin's own module boundaries).  Nothing imports this module;
  it is a reading shelf, not part of the port's cone.
-/
import FLTForHuman.ModularForms.WeightOne.EisensteinChiNegThree

set_option autoImplicit false

noncomputable section

open Complex Real Matrix CongruenceSubgroup Subgroup ModularForm EisensteinWeightOne
open FLT.AnalyticCore FLT.AnalyticCore.LatticeSum
open A2HexPoisson
open CongruenceSubgroup.Gamma0Three
open scoped MatrixGroups ModularForm Manifold Topology UpperHalfPlane Finset Nat Finset.Nat
open scoped ArithmeticFunction CongruenceSubgroup CongruenceSubgroup.Gamma0Three
open FLT.EisensteinWeightOne



namespace FLT.AnalyticCore

private def e1Chi3ModularForm : ModularForm (Gamma1 3) 1 :=
  e1Chi3IsModular.choose

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private def mulE1Chi3 (g : CuspForm (Gamma1 3) 1) : CuspForm (Gamma1 3) 2 :=
  CuspForm.mcast (by norm_num) (g.mulModularForm e1Chi3ModularForm)

end FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma hexTheta_mul_I_eq_ofReal (t : ℝ) :
    hexTheta (I * (t : ℂ)) =
      ((∑' p : ℤ × ℤ,
        rexp (-(2 * π * t) * ((p.1 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2))) : ℝ) := by
  rw [hexTheta, Complex.ofReal_tsum]
  refine tsum_congr fun p => ?_
  rw [hexThetaTerm, Complex.ofReal_exp]
  refine congrArg cexp ?_
  push_cast
  linear_combination (2 * (π : ℂ) * (t : ℂ) *
    ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) * Complex.I_sq

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma hexTheta_mul_I_ne_zero {t : ℝ} (ht : 0 < t) : hexTheta (I * (t : ℂ)) ≠ 0 := by
  have him : (I * (t : ℂ)).im = t := by simp
  have hsum : Summable (hexThetaTerm (I * (t : ℂ))) :=
    summable_hexThetaTerm (by rw [him]; exact ht)
  have hsum' : Summable fun p : ℤ × ℤ =>
      rexp (-(2 * π * t) * ((p.1 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2)) := by
    refine (summable_norm_iff.mpr hsum).congr fun p => ?_
    rw [norm_hexThetaTerm, him]
  rw [hexTheta_mul_I_eq_ofReal t, Ne, Complex.ofReal_eq_zero]
  exact (hsum'.tsum_pos (fun p => (Real.exp_pos _).le) (0, 0) (Real.exp_pos _)).ne'

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma frickeFixedPoint_im_pos : 0 < frickeFixedPoint.im := by
  rw [frickeFixedPoint, show (I / ((Real.sqrt 3 : ℝ) : ℂ)) =
    ((((Real.sqrt 3)⁻¹ : ℝ)) : ℂ) * I by push_cast; ring, Complex.mul_I_im,
    Complex.ofReal_re]
  positivity

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma three_mul_frickeFixedPoint_sq : 3 * frickeFixedPoint ^ 2 = -1 := by
  rw [frickeFixedPoint, div_pow, Complex.I_sq,
    show ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num]
  norm_num

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma frickeFixedPoint_fixed : -1 / (3 * frickeFixedPoint) = frickeFixedPoint := by
  have h0 : frickeFixedPoint ≠ 0 := by
    rw [frickeFixedPoint]
    exact div_ne_zero Complex.I_ne_zero sqrt_three_ne_zero
  rw [div_eq_iff (mul_ne_zero (by norm_num) h0)]
  linear_combination -three_mul_frickeFixedPoint_sq

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma neg_I_mul_sqrt_three_mul_frickeFixedPoint :
    -I * (Real.sqrt 3 : ℂ) * frickeFixedPoint = 1 := by
  rw [frickeFixedPoint, show -I * ((Real.sqrt 3 : ℝ) : ℂ) * (I / ((Real.sqrt 3 : ℝ) : ℂ)) =
    -(I * I) * (((Real.sqrt 3 : ℝ) : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ)) by ring,
    Complex.I_mul_I, div_self sqrt_three_ne_zero]
  norm_num

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma I_mul_sqrt_three_mul_frickeFixedPoint :
    I * (Real.sqrt 3 : ℂ) * frickeFixedPoint = -1 := by
  linear_combination -neg_I_mul_sqrt_three_mul_frickeFixedPoint

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private lemma hexTheta_frickeFixedPoint_ne_zero : hexTheta frickeFixedPoint ≠ 0 := by
  rw [show frickeFixedPoint = I * ((((Real.sqrt 3)⁻¹ : ℝ)) : ℂ) by
    rw [frickeFixedPoint]; push_cast; ring]
  exact hexTheta_mul_I_ne_zero (by positivity)

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem not_hexTheta_eq_neg_multiplier_mul :
    ¬ (hexTheta (-1 / (3 * frickeFixedPoint)) =
        I * (Real.sqrt 3 : ℂ) * frickeFixedPoint * hexTheta frickeFixedPoint) := by
  intro hcon
  rw [frickeFixedPoint_fixed, I_mul_sqrt_three_mul_frickeFixedPoint, neg_one_mul] at hcon
  exact hexTheta_frickeFixedPoint_ne_zero (CharZero.eq_neg_self_iff.mp hcon)

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem TU_pow_three : (ModularGroup.T * U₃) ^ 3 = 1 := by decide

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem TU_ne_one : ModularGroup.T * U₃ ≠ 1 := by decide

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem TU_sq_ne_one : (ModularGroup.T * U₃) ^ 2 ≠ 1 := by decide

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem chi3_eq_chiNegThree (d : ℕ) (hd : (d : ZMod 3) ≠ 0) (γ : SL(2, ℤ))
    (hγd : (γ 1 1 : ZMod 3) = (d : ZMod 3)) :
    chi3 γ = _root_.EisensteinWeightOne.chiNegThree d := by
  have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  have hval : d % 3 = (d : ZMod 3).val := by rw [ZMod.val_natCast]
  unfold chi3 _root_.EisensteinWeightOne.chiNegThree
  rw [hγd, hval]
  rcases key _ hd with h | h <;> rw [h] <;> decide

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem hexThetaH_ne_zero : hexThetaH ≠ 0 := by
  intro h
  have hpt : hexThetaH ⟨frickeFixedPoint, frickeFixedPoint_im_pos⟩ = 0 := by rw [h]; rfl
  rw [hexThetaH_apply, latticeSum_eq_hexTheta] at hpt
  exact hexTheta_frickeFixedPoint_ne_zero hpt

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem not_hexTheta_U_law_weight_zero :
    ¬ (∀ z : ℂ, 0 < z.im → hexTheta (z / ((-3) * z + 1)) = hexTheta z) := by
  intro hcon
  have h0 : 0 < frickeFixedPoint.im := frickeFixedPoint_im_pos
  have h1 := hcon frickeFixedPoint h0
  have h2 := hexTheta_U_law h0
  rw [h1] at h2

  have h3 : (-3 : ℂ) * frickeFixedPoint * hexTheta frickeFixedPoint = 0 := by
    linear_combination -h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact mul_ne_zero (by norm_num : (-3 : ℂ) ≠ 0) (ne_zero_of_im_pos h0) h4
  · exact hexTheta_frickeFixedPoint_ne_zero h4

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem hexThetaH_slash_TU :
    hexThetaH ∣[(1 : ℤ)] (ModularGroup.T * U₃) = hexThetaH := by
  rw [SlashAction.slash_mul, hexThetaH_slash_T, hexThetaH_slash_U]

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem differentiableAt_latticeSum_I : DifferentiableAt ℂ latticeSum Complex.I :=
  differentiableAt_latticeSum (by simp)

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem not_summable_gaussian_prod_zero :
    ¬ Summable (fun v : ℤ × ℤ =>
      Real.exp (-(π * 0 * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * 0 * (v.2 : ℝ) ^ 2))) := by
  have h : (fun v : ℤ × ℤ =>
      Real.exp (-(π * 0 * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * 0 * (v.2 : ℝ) ^ 2)))
      = fun _ => (1 : ℝ) := by
    funext v
    simp
  rw [h, summable_const_iff]
  exact one_ne_zero

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem continuous_hexThetaH : Continuous hexThetaH :=
  mdifferentiable_hexThetaH.continuous

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem e1Chi3ModularForm_apply (z : UpperHalfPlane) :
    e1Chi3ModularForm z = ∑' n : ℕ,
      ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ)) :=
  e1Chi3IsModular.choose_spec z

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem e1Chi3ModularForm_eq_latticeSum (z : UpperHalfPlane) :
    e1Chi3ModularForm z = latticeSum z := by
  rw [e1Chi3ModularForm_apply]
  exact (latticeSum_eq_e1Chi3_qSeries representationCountAgrees z).symm

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem e1Chi3ModularForm_ne_zero : e1Chi3ModularForm ≠ 0 := by
  intro h
  have hpt : e1Chi3ModularForm ⟨frickeFixedPoint, frickeFixedPoint_im_pos⟩ = 0 := by
    rw [h]; rfl
  rw [e1Chi3ModularForm_eq_latticeSum, latticeSum_eq_hexTheta] at hpt
  exact hexTheta_frickeFixedPoint_ne_zero hpt

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem mulE1Chi3_apply (g : CuspForm (Gamma1 3) 1) (z : UpperHalfPlane) :
    mulE1Chi3 g z = g z * e1Chi3ModularForm z :=
  rfl

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem exists_cuspForm_two_mul_e1Chi3 (g : CuspForm (Gamma1 3) 1) :
    ∃ h : CuspForm (Gamma1 3) 2, ∀ z : UpperHalfPlane,
      h z = g z * ∑' n : ℕ,
        ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ)) :=
  ⟨mulE1Chi3 g, fun z => by rw [mulE1Chi3_apply, e1Chi3ModularForm_apply]⟩

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem U₃_not_mem_gamma0_nine : U₃ ∉ Gamma0 9 := by
  rw [Gamma0_mem]; decide

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.AnalyticCore.FLT.FLT.AnalyticCore

private theorem eq_zero_of_slashInvariant_gamma0
    (F : ℍ → ℂ) (h : ∀ γ ∈ Gamma0 3, F ∣[(1 : ℤ)] γ = F) : F = 0 := by
  have h1 : ((chi3 (-1 : SL(2, ℤ)) : ℤ) : ℂ) • F = F :=
    (slash_neg_one F).symm.trans (h (-1) neg_one_mem_gamma0_three)
  rw [chi3_neg_one] at h1
  ext τ
  have h2 : ((-1 : ℤ) : ℂ) * F τ = F τ := by
    have := congrFun h1 τ
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have h3 : (2 : ℂ) * F τ = 0 := by push_cast at h2; linear_combination -h2
  simpa [two_ne_zero] using mul_eq_zero.mp h3

end FLT.AnalyticCore.FLT.FLT.AnalyticCore

namespace FLT.EisensteinWeightOne

private theorem chiNegThree_eq_zero_iff {n : ℕ} : chiNegThree n = 0 ↔ 3 ∣ n := by
  simp only [chiNegThree]
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h <;> simp [h] <;> omega

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_prime {p : ℕ} (hp : p.Prime) : sigmaChi p = 1 + chiNegThree p := by
  rw [sigmaChi, Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne, chiNegThree_one]

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_two : sigmaChi 2 = 0 := by decide

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_three : sigmaChi 3 = 1 := by decide

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_four : sigmaChi 4 = 1 := by decide

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_five : sigmaChi 5 = 0 := by decide

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_six : sigmaChi 6 = 0 := by decide

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem sigmaChi_seven : sigmaChi 7 = 2 := by decide

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem coeff_two_e1Chi3 : PowerSeries.coeff 2 e1Chi3 = 0 := by
  rw [coeff_e1Chi3]
  norm_num [sigmaChi_two]

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem coeff_three_e1Chi3 : PowerSeries.coeff 3 e1Chi3 = 6 := by
  rw [coeff_e1Chi3]
  norm_num [sigmaChi_three]

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem coeff_four_e1Chi3 : PowerSeries.coeff 4 e1Chi3 = 6 := by
  rw [coeff_e1Chi3]
  norm_num [sigmaChi_four]

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem coeff_seven_e1Chi3 : PowerSeries.coeff 7 e1Chi3 = 12 := by
  rw [coeff_e1Chi3]
  norm_num [sigmaChi_seven]

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem six_dvd_coeff_e1Chi3_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (6 : ℤ) ∣ PowerSeries.coeff n e1Chi3 :=
  ⟨sigmaChi n, coeff_e1Chi3_of_ne_zero hn⟩

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem three_dvd_coeff_e1Chi3_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (3 : ℤ) ∣ PowerSeries.coeff n e1Chi3 :=
  dvd_trans (by norm_num) (six_dvd_coeff_e1Chi3_of_ne_zero hn)

end FLT.EisensteinWeightOne

namespace FLT.EisensteinWeightOne

private theorem three_dvd_coeff_e1Chi3_sub_one (n : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff n (e1Chi3 - 1) := by
  rw [map_sub, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_e1Chi3]
  · rw [ite_eq_right hn, sub_zero]
    exact three_dvd_coeff_e1Chi3_of_ne_zero hn

end FLT.EisensteinWeightOne

namespace FLT.AnalyticCore.LatticeSum

private theorem not_summable_latticeTerm_zero : ¬ Summable (latticeTerm 0) := by
  have h : latticeTerm 0 = fun _ ↦ (1 : ℂ) := by
    funext v; simp [latticeTerm]
  rw [h, summable_const_iff]
  exact one_ne_zero

end FLT.AnalyticCore.LatticeSum

namespace FLT.AnalyticCore.LatticeSum

private lemma finite_fiber_hexFormNat (n : ℕ) : (hexFormNat ⁻¹' {n}).Finite := by
  apply Set.Finite.subset
    ((Finset.Icc (-(2 * n : ℤ)) (2 * n) ×ˢ Finset.Icc (-(2 * n : ℤ)) (2 * n)).finite_toSet)
  rintro ⟨a, b⟩ hv
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hexFormNat_eq_iff] at hv
  have hbox : a ^ 2 + b ^ 2 ≤ 2 * (n : ℤ) := by
    have := sq_add_sq_le_two_mul_hexForm (a, b)
    simp only [hexForm_mk] at this hv
    omega
  have ha2 : a ^ 2 ≤ 2 * (n : ℤ) := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ 2 * (n : ℤ) := by nlinarith [sq_nonneg a]
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [Int.le_self_sq (-a)]
  · nlinarith [Int.le_self_sq a]
  · nlinarith [Int.le_self_sq (-b)]
  · nlinarith [Int.le_self_sq b]

end FLT.AnalyticCore.LatticeSum

namespace FLT.AnalyticCore.LatticeSum

private theorem repCount_one : repCount 1 = 6 := by
  have h : hexFormNat ⁻¹' {1} =
      (↑({((1 : ℤ), (0 : ℤ)), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)} :
        Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hexFormNat_eq_iff, Int.natCast_one,
      hexForm_mk, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro hab
      have hbox : a ^ 2 + b ^ 2 ≤ 2 := by nlinarith [sq_nonneg (a + b)]
      obtain ⟨ha1, ha2⟩ : -1 ≤ a ∧ a ≤ 1 := by
        constructor <;> nlinarith [Int.le_self_sq (-a), Int.le_self_sq a, sq_nonneg b]
      obtain ⟨hb1, hb2⟩ : -1 ≤ b ∧ b ≤ 1 := by
        constructor <;> nlinarith [Int.le_self_sq (-b), Int.le_self_sq b, sq_nonneg a]
      interval_cases a <;> interval_cases b <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        decide
  rw [repCount, h, Set.ncard_coe_finset]
  decide

end FLT.AnalyticCore.LatticeSum

namespace FLT.AnalyticCore.LatticeSum

private theorem representationCountAgrees_zero : (repCount 0 : ℤ) = PowerSeries.coeff 0 e1Chi3 := by
  simp [repCount_zero, coeff_e1Chi3]

end FLT.AnalyticCore.LatticeSum

namespace FLT.AnalyticCore.LatticeSum

private theorem representationCountAgrees_one : (repCount 1 : ℤ) = PowerSeries.coeff 1 e1Chi3 := by
  rw [repCount_one, coeff_one_e1Chi3]; rfl

end FLT.AnalyticCore.LatticeSum

namespace FLT.AnalyticCore

private lemma thetaBound_nonneg : 0 ≤ thetaBound :=
  tsum_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private def thetaBoundAt (T : ℝ) : ℝ :=
  ∑' v : ℤ × ℤ, Real.exp (-(π * T * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * T * (v.2 : ℝ) ^ 2))

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem norm_latticeSum_le_of_le_im {T : ℝ} (hT : 0 < T) {τ : ℂ} (hτ : T ≤ τ.im) :
    ‖latticeSum τ‖ ≤ thetaBoundAt T := by
  have hdom : ∀ v : ℤ × ℤ, ‖latticeTerm τ v‖
      ≤ Real.exp (-(π * T * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * T * (v.2 : ℝ) ^ 2)) :=
    fun v => norm_latticeTerm_le_of_le_im hT hτ v
  have hgauss : Summable fun v : ℤ × ℤ =>
      Real.exp (-(π * T * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * T * (v.2 : ℝ) ^ 2)) :=
    summable_gaussian_prod hT
  have hsum_norm : Summable fun v : ℤ × ℤ => ‖latticeTerm τ v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hgauss
  calc ‖latticeSum τ‖ ≤ ∑' v : ℤ × ℤ, ‖latticeTerm τ v‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' v : ℤ × ℤ, Real.exp (-(π * T * (v.1 : ℝ) ^ 2))
          * Real.exp (-(π * T * (v.2 : ℝ) ^ 2)) :=
        hsum_norm.tsum_le_tsum hdom hgauss
    _ = thetaBoundAt T := rfl

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem thetaBoundAt_one_eq : thetaBoundAt 1 = thetaBound := by
  unfold thetaBoundAt thetaBound
  simp only [mul_one]

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_two : reprCount 2 = 0 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_three : reprCount 3 = 6 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_four : reprCount 4 = 6 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_five : reprCount 5 = 0 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_six : reprCount 6 = 0 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_seven : reprCount 7 = 12 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_thirteen : reprCount 13 = 12 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_eq_coeff_e1Chi3_two :
    (reprCount 2 : ℤ) = PowerSeries.coeff 2 e1Chi3 := by
  rw [reprCount_two, coeff_two_e1Chi3]; norm_num

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_eq_coeff_e1Chi3_three :
    (reprCount 3 : ℤ) = PowerSeries.coeff 3 e1Chi3 := by
  rw [reprCount_three, coeff_three_e1Chi3]; norm_num

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_eq_coeff_e1Chi3_four :
    (reprCount 4 : ℤ) = PowerSeries.coeff 4 e1Chi3 := by
  rw [reprCount_four, coeff_four_e1Chi3]; norm_num

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_eq_coeff_e1Chi3_seven :
    (reprCount 7 : ℤ) = PowerSeries.coeff 7 e1Chi3 := by
  rw [reprCount_seven, coeff_seven_e1Chi3]; norm_num

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_eq_coeff_e1Chi3_thirteen :
    (reprCount 13 : ℤ) = PowerSeries.coeff 13 e1Chi3 := by
  rw [reprCount_thirteen, coeff_e1Chi3_of_ne_zero (by norm_num)]
  have : sigmaChi 13 = 2 := by decide
  rw [this]; norm_num

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private noncomputable def thetaHexQExpansion : PowerSeries ℤ :=
  PowerSeries.mk fun n => (reprCount n : ℤ)

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem thetaHexQExpansion_eq_e1Chi3 (h : ReprCountEqCoeffE1Chi3) :
    thetaHexQExpansion = e1Chi3 := by
  ext n
  rw [thetaHexQExpansion, PowerSeries.coeff_mk]
  exact h n

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCountEqCoeffE1Chi3_on_table :
    ∀ n ∈ ({0, 1, 2, 3, 4, 7, 13} : Finset ℕ),
      (reprCount n : ℤ) = PowerSeries.coeff n e1Chi3 := by
  intro n hn
  fin_cases hn
  · exact reprCount_eq_coeff_e1Chi3_zero
  · exact reprCount_eq_coeff_e1Chi3_one
  · exact reprCount_eq_coeff_e1Chi3_two
  · exact reprCount_eq_coeff_e1Chi3_three
  · exact reprCount_eq_coeff_e1Chi3_four
  · exact reprCount_eq_coeff_e1Chi3_seven
  · exact reprCount_eq_coeff_e1Chi3_thirteen

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private noncomputable def gaussianCountThree : ℕ :=
  ((reprBox 3).filter fun p => p.1 * p.1 + p.2 * p.2 = (3 : ℤ)).card

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem gaussianCountThree_ne : gaussianCountThree ≠ reprCount 3 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem multiplier_six_load_bearing : (reprCount 1 : ℤ) ≠ sigmaChi 1 := by
  rw [reprCount_one, sigmaChi_one]; norm_num

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem hexForm_two_neg_one : hexForm 2 (-1) = 3 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem reprCount_eq_zero_of_inert_dvd_of_not_sq_dvd (hp : p.Prime) (h2 : p % 3 = 2)
    {n : ℕ} (hdvd : p ∣ n) (hnsq : ¬p ^ 2 ∣ n) : reprCount n = 0 := by
  rw [reprCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ hxy
  have hQ : hexForm x y = (n : ℤ) := mem_reprSols_iff.mp hxy
  have hpd : (p : ℤ) ∣ hexForm x y := by rw [hQ]; exact_mod_cast hdvd
  have hsq : (p : ℤ) ^ 2 ∣ (n : ℤ) := by
    have h' := inert_sq_dvd_of_dvd_hexForm hp h2 hpd
    rwa [hQ] at h'
  refine hnsq ?_
  have : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by push_cast; exact hsq
  exact_mod_cast this

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem sigmaChi_eq_zero_of_inert_dvd_of_not_sq_dvd (hp : p.Prime) (h2 : p % 3 = 2)
    {n : ℕ} (hdvd : p ∣ n) (hnsq : ¬p ^ 2 ∣ n) : sigmaChi n = 0 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hpm : ¬p ∣ m := fun hm => hnsq (by obtain ⟨m', rfl⟩ := hm; exact ⟨m', by ring⟩)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  rw [sigmaChi_mul_of_coprime p m hcop, sigmaChi_prime hp]
  have hchi : chiNegThree p = -1 := by
    simp [chiNegThree, h2]
  rw [hchi]; ring

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem reprCount_eq_coeff_of_inert_exactly_dvd (hp : p.Prime) (h2 : p % 3 = 2)
    {n : ℕ} (hn : n ≠ 0) (hdvd : p ∣ n) (hnsq : ¬p ^ 2 ∣ n) :
    (reprCount n : ℤ) = PowerSeries.coeff n e1Chi3 := by
  rw [reprCount_eq_zero_of_inert_dvd_of_not_sq_dvd hp h2 hdvd hnsq,
    coeff_e1Chi3_of_ne_zero hn,
    sigmaChi_eq_zero_of_inert_dvd_of_not_sq_dvd hp h2 hdvd hnsq]
  ring

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem exists_dvd_hexForm_of_split {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ a : ℤ, (p : ℤ) ∣ hexForm a 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by rintro rfl; omega
  obtain ⟨t, ht⟩ := ModularCurve.exists_orderOf_eq_three hp h1
  have hroot : t ^ 2 + t + 1 = 0 :=
    (ModularCurve.sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 t).mpr ht
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective t
  refine ⟨a, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [hexForm]
  linear_combination hroot

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem reprCount_twelve : reprCount 12 = 6 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem reprCount_nine : reprCount 9 = 6 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem reprCount_ten : reprCount 10 = 0 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem orbitCountMultiplicative_three_four :
    6 * reprCount (3 * 4) = reprCount 3 * reprCount 4 := by
  norm_num [reprCount_twelve, reprCount_three, reprCount_four]

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem orbitCountMultiplicative_not_without_coprime :
    ¬(∀ m n : ℕ, 6 * reprCount (m * n) = reprCount m * reprCount n) := by
  intro h
  have h22 := h 2 2
  rw [reprCount_two] at h22
  norm_num [show (2 : ℕ) * 2 = 4 from rfl, reprCount_four] at h22

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem splitPrimePowCount_at_seven : reprCount (7 ^ 1) = 6 * (1 + 1) := by
  norm_num [reprCount_seven]

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem splitPrimePowCount_not_at_inert : reprCount (2 ^ 1) ≠ 6 * (1 + 1) := by
  norm_num [reprCount_two]

end FLT.AnalyticCore

namespace FLT.AnalyticCore

variable {p : ℕ}
private theorem residuals_jointly_satisfiable_on_table :
    (6 * reprCount (3 * 4) = reprCount 3 * reprCount 4) ∧
      (reprCount (7 ^ 1) = 6 * (1 + 1)) :=
  ⟨orbitCountMultiplicative_three_four, splitPrimePowCount_at_seven⟩

end FLT.AnalyticCore

namespace FLT.AnalyticCore.HexInt

private theorem isUnit_iff_mem {z : HexInt} : IsUnit z ↔ z ∈ unitFinset := by
  rw [isUnit_iff_norm_eq_one, norm_eq_one_iff_mem]

end FLT.AnalyticCore.HexInt

namespace FLT.AnalyticCore.HexInt

private theorem conj_mem_unitFinset {u : HexInt} (hu : u ∈ unitFinset) : u.conj ∈ unitFinset := by
  fin_cases hu <;> decide

end FLT.AnalyticCore.HexInt

namespace FLT.AnalyticCore

private theorem reprCountEqCoeffE1Chi3_of_splitPrimePowCount (hsplit : SplitPrimePowCount) :
    ReprCountEqCoeffE1Chi3 :=
  reprCountEqCoeffE1Chi3_of_residuals HexInt.orbitCountMultiplicative_holds hsplit

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem reprCount_twentyone : reprCount 21 = 12 := by
  rw [show (21 : ℕ) = 3 * 7 from rfl, reprCount_three_mul, reprCount_seven]

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem orbitCount_at_three_seven :
    6 * reprCount (3 * 7) = reprCount 3 * reprCount 7 :=
  HexInt.orbitCountMultiplicative_holds 3 7 (by norm_num)

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem orbitCount_three_seven_consistency :
    6 * reprCount 21 = reprCount 3 * reprCount 7 := by
  rw [reprCount_twentyone, reprCount_three, reprCount_seven]

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem orbitCount_coprimality_load_bearing :
    OrbitCountMultiplicative ∧
      ¬(∀ m n : ℕ, 6 * reprCount (m * n) = reprCount m * reprCount n) :=
  ⟨HexInt.orbitCountMultiplicative_holds, orbitCountMultiplicative_not_without_coprime⟩

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem representationCountAgrees_of_splitPrimePowCount
    (hsplit : SplitPrimePowCount) : LatticeSum.RepresentationCountAgrees :=
  representationCountAgrees_of_reprCountEqCoeffE1Chi3
    (reprCountEqCoeffE1Chi3_of_splitPrimePowCount hsplit)

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem latticeSum_eq_e1Chi3_qSeries_of_reprCount
    (h : ReprCountEqCoeffE1Chi3) (z : UpperHalfPlane) :
    LatticeSum.latticeSum z
      = ∑' n : ℕ, ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ)) :=
  LatticeSum.latticeSum_eq_e1Chi3_qSeries
    (representationCountAgrees_of_reprCountEqCoeffE1Chi3 h) z

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem repCount_one_two_routes :
    LatticeSum.repCount 1 = reprCount 1 ∧ LatticeSum.repCount 1 = 6 ∧ reprCount 1 = 6 :=
  ⟨repCount_eq_reprCount 1, LatticeSum.repCount_one, reprCount_one⟩

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem latticeSum_repCount_seven : LatticeSum.repCount 7 = 12 := by
  rw [repCount_eq_reprCount]
  exact reprCount_seven

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem latticeSum_repCount_thirteen : LatticeSum.repCount 13 = 12 := by
  rw [repCount_eq_reprCount]
  exact reprCount_thirteen

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem representationCountAgrees_on_table :
    ∀ n ∈ ({0, 1, 2, 3, 4, 7, 13} : Finset ℕ),
      (LatticeSum.repCount n : ℤ) = PowerSeries.coeff n e1Chi3 := by
  intro n hn
  rw [repCount_eq_reprCount]
  exact reprCountEqCoeffE1Chi3_on_table n hn

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem hexForm_two_one : hexForm 2 1 = 7 := by decide

end FLT.AnalyticCore

namespace FLT.AnalyticCore

private theorem not_exists_hexForm_eq_two : ¬∃ x y : ℤ, hexForm x y = ((2 : ℕ) : ℤ) := by
  rintro ⟨x, y, hxy⟩
  have hmem : ((x : ℤ), (y : ℤ)) ∈ reprSols 2 := mem_reprSols_iff.mpr hxy
  have h2 : (reprSols 2).card = 0 := reprCount_two
  rw [Finset.card_eq_zero] at h2
  rw [h2] at hmem
  exact absurd hmem (Finset.notMem_empty _)

end FLT.AnalyticCore
