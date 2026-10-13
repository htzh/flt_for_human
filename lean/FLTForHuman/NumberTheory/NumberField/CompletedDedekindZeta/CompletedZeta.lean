/-
  The completed Dedekind zeta function as a class sum, and its functional equation.

  This is wave 7 of the `completedDedekindZeta` package: the arithmetic normalising
  constant `constK`, the class representatives `classRepr` of the ideal class group
  together with their covolumes, the completed zeta function
  `completedDedekindZeta_classSum` as the finite sum of the per-class completed
  partial zeta functions, the archimedean factor `gammaFactor`, and its analytic
  properties: differentiability on the complement of `{0, 1}`, the
  functional equation `completedDedekindZeta_classSum_functionalEquation`, and the
  bridge `completedDedekindZeta_classSum_eq_completedDedekindZeta` to the closed form
  `completedDedekindZeta` of wave 1.  It closes with the extension
  `completedDedekindZeta_continuousExtension`, which is differentiable and satisfies
  the functional equation on all of `ℂ`, discharging the headline obligation
  `exists_completedDedekindZeta_functionalEquation` of wave 1, and with the three
  `Prop` obligations the later waves consume: `xiOrderOneHadamard`,
  `xi_endpointNonvanishing` and `completedDedekindZeta_realSuperlinear`.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:5460–6052`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.Gapsw80T9ClassSumA1Closure`, `FLT.Gapsw80T10DedekindZetaBridgeA1Discharge`,
  `FLT.Gapsw80T11ExplicitFormulaA34Decomp`, `FLT.Gapsw80T32D1aBoundaryCaseDecomp` and
  `FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof` blocks.  The pin's obligation prefixes
  and per-obligation namespaces are dropped; every declaration carries the pin's own
  name and line in the `-- pin:` comment above it (playbook §2.3, §4).  The pin's
  class-sum completed zeta function (pin 5491) is renamed
  `completedDedekindZeta_classSum`, because `completedDedekindZeta` is already the
  wave-1 closed form (pin 356).

  The pin's file-wide `set_option maxHeartbeats 6400000` and its per-declaration
  `… in` overrides are not transcribed; the port's global cap is `4000000`.  Proofs
  are adapted to mathlib `v4.34.0`.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Unfolding
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

namespace NumberField.CompletedDedekindZeta

open Matrix
open Module
open WithLp
open MeasureTheory
open Real
open NumberField
open NumberField.InfinitePlace
open NumberField.mixedEmbedding
open NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open _root_.Complex hiding exp
open Asymptotics Filter Set
open _root_.Ideal
open scoped Classical
open scoped RealInnerProductSpace
open scoped nonZeroDivisors
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-! ### The class-sum form of the completed zeta function -/


-- pin: gapsw80_t9_constK (S_NumberField_exists_completedDedekindZeta_package.lean:5460)
noncomputable def constK : ℂ :=
  (torsionOrder K : ℂ)
    / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ))

-- pin: gapsw80_t9_constK_def (S_NumberField_exists_completedDedekindZeta_package.lean:5464)
theorem constK_def :
    constK K = (torsionOrder K : ℂ)
      / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1)
          * (nK K : ℂ) * (regulator K : ℂ)) := rfl

-- pin: gapsw80_t9_constK_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:5469)
theorem constK_ne_zero : constK K ≠ 0 := by
  refine div_ne_zero ?_ (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact_mod_cast (torsionOrder_pos K).ne'
  · exact pow_ne_zero _ two_ne_zero
  · exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  · exact Complex.ofReal_ne_zero.mpr (regulator_pos K).ne'

-- pin: gapsw80_t9_classRepr (S_NumberField_exists_completedDedekindZeta_package.lean:5476)
noncomputable def classRepr (C : ClassGroup (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (FractionalIdeal.mk0 K (ClassGroup.mk0_surjective C).choose)⁻¹

-- pin: gapsw80_t9_mk_classRepr (S_NumberField_exists_completedDedekindZeta_package.lean:5480)
theorem mk_classRepr (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (classRepr K C) = C⁻¹ := by
  unfold classRepr
  rw [map_inv, ClassGroup.mk_mk0, (ClassGroup.mk0_surjective C).choose_spec]

-- pin: gapsw80_t9_covolRepr (S_NumberField_exists_completedDedekindZeta_package.lean:5485)
noncomputable abbrev covolRepr (C : ClassGroup (𝓞 K)) : ℝ :=
  ZLattice.covolume (mixedEmbedding.idealLattice K (classRepr K C))

-- pin: gapsw80_t9_covolRepr_pos (S_NumberField_exists_completedDedekindZeta_package.lean:5488)
theorem covolRepr_pos (C : ClassGroup (𝓞 K)) :
    0 < covolRepr K C := covolume_pos K _

-- pin: gapsw80_t9_completedDedekindZeta (S_NumberField_exists_completedDedekindZeta_package.lean:5491)
noncomputable def completedDedekindZeta_classSum (s : ℂ) : ℂ :=
  (constK K)⁻¹
    * ∑ C : ClassGroup (𝓞 K),
        ((covolRepr K C : ℝ) : ℂ) ^ s
          * (heckeWeakFEPair K (classRepr K C)).Λ ((nK K : ℂ) * s / 2)

-- pin: gapsw80_t9_gammaFactor (S_NumberField_exists_completedDedekindZeta_package.lean:5497)
noncomputable abbrev gammaFactor (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

-- pin: gapsw80_t9_sigma_one_sub (S_NumberField_exists_completedDedekindZeta_package.lean:5500)
theorem nK_mul_one_sub_div_two (s : ℂ) :
    (nK K : ℂ) * (1 - s) / 2
      = (((nK K : ℝ) / 2 : ℝ) : ℂ) - (nK K : ℂ) * s / 2 := by
  push_cast; ring

-- pin: gapsw80_t9_perClass_FE_step (S_NumberField_exists_completedDedekindZeta_package.lean:5505)
theorem perClass_functionalEquation_step (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (1 - s)
        * (heckeWeakFEPair K I).Λ ((nK K : ℂ) * (1 - s) / 2)
      = ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2) := by
  have hFE := (heckeWeakFEPair K I).functional_equation ((nK K : ℂ) * s / 2)
  have hk : (heckeWeakFEPair K I).k = (nK K : ℝ) / 2 := rfl
  have hε : (heckeWeakFEPair K I).ε
      = ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹ := rfl
  rw [hk, hε, smul_eq_mul] at hFE
  have hcov : ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (covolume_pos K I).ne'
  rw [nK_mul_one_sub_div_two, hFE, ← mul_assoc]
  congr 1
  rw [show (1:ℂ) - s = (-s) + 1 from by ring, Complex.cpow_add _ _ hcov, Complex.cpow_one,
    mul_assoc, mul_inv_cancel₀ hcov, mul_one]

-- pin: gapsw80_t9_four_cpow_cancel (S_NumberField_exists_completedDedekindZeta_package.lean:5522)
theorem four_cpow_cancel (s : ℂ) :
    ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * (((4:ℝ)⁻¹ ^ nrComplexPlaces K : ℝ) : ℂ) ^ (-s)
      = 1 := by
  have h4 : ((4:ℝ):ℂ) ≠ 0 := by norm_num
  have harg : Complex.arg ((4:ℝ):ℂ) = 0 :=
    Complex.arg_ofReal_of_nonneg (by norm_num)
  have harg' : Complex.arg (((4:ℝ):ℂ)^nrComplexPlaces K) ≠ Real.pi := by
    rw [show ((4:ℝ):ℂ) ^ nrComplexPlaces K = ((4 ^ nrComplexPlaces K : ℝ) : ℂ) from
      by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm

  have hinv : (((4:ℝ)⁻¹^nrComplexPlaces K : ℝ):ℂ) = (((4:ℝ):ℂ)^nrComplexPlaces K)⁻¹ := by
    rw [inv_pow]; push_cast; ring
  rw [hinv, Complex.inv_cpow _ _ harg',
    ← Complex.cpow_nat_mul' (x := ((4:ℝ):ℂ))
      (by rw [harg, mul_zero]; linarith [Real.pi_pos])
      (by rw [harg, mul_zero]; exact Real.pi_pos.le) (-s),
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ h4]
  convert Complex.cpow_zero _ using 2
  ring

-- pin: gapsw80_t9_covol_cancel (S_NumberField_exists_completedDedekindZeta_package.lean:5545)
theorem covol_cancel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
          * ((ZLattice.covolume (mixedEmbedding.idealLattice K
              (traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s))
      = 1 := by
  have hI := (covolume_pos K I).le
  have hJ := (covolume_pos K (traceDualIdeal K I)).le
  rw [show ∀ a b c : ℂ, a*(b*c) = b*(a*c) from fun a b c => by ring,
    ← Complex.mul_cpow_ofReal_nonneg hI hJ, ← Complex.ofReal_mul,
    covolume_mul_covolume_traceDualIdeal]
  exact four_cpow_cancel K s

-- pin: gapsw80_t9_perClass_identified (S_NumberField_exists_completedDedekindZeta_package.lean:5558)
theorem perClass_identified (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = constK K
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s
        * partialDedekindZeta K
            (ClassGroup.mk K (traceDualIdeal K I))⁻¹ s := by
  rw [symmLambda_eq_completedPartialZeta K I hs, ← constK_def]
  linear_combination
    (constK K * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
      * gammaFactor K s
      * partialDedekindZeta K
          (ClassGroup.mk K (traceDualIdeal K I))⁻¹ s)
    * covol_cancel K I s

-- pin: gapsw80_t9_diffIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:5574)
noncomputable def differentIdealNonzero : (Ideal (𝓞 K))⁰ :=
  ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_iff_ne_zero.mpr differentIdeal_ne_bot⟩

-- pin: gapsw80_t9_diffClass (S_NumberField_exists_completedDedekindZeta_package.lean:5577)
noncomputable def differentIdealClass : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (differentIdealNonzero K)

-- pin: gapsw80_t9_traceDualIdeal_eq (S_NumberField_exists_completedDedekindZeta_package.lean:5580)
theorem traceDualIdeal_eq_inv_mul_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdeal K I
      = (FractionalIdeal.mk0 K (differentIdealNonzero K))⁻¹ * I⁻¹ := by
  apply Units.ext
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
  congr 1
  have h := coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)
  rw [differentIdealNonzero, h, inv_inv]

-- pin: gapsw80_t9_mk_traceDualIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:5590)
theorem mk_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (traceDualIdeal K I)
      = (differentIdealClass K)⁻¹ * (ClassGroup.mk K I)⁻¹ := by
  rw [traceDualIdeal_eq_inv_mul_inv, map_mul, map_inv, map_inv, ClassGroup.mk_mk0,
    differentIdealClass]

-- pin: gapsw80_t9_classBijection (S_NumberField_exists_completedDedekindZeta_package.lean:5596)
noncomputable def diffClassMulInvEquiv : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft (differentIdealClass K))

-- pin: gapsw80_t9_classBijection_apply (S_NumberField_exists_completedDedekindZeta_package.lean:5599)
theorem diffClassMulInvEquiv_apply (C : ClassGroup (𝓞 K)) :
    diffClassMulInvEquiv K C = differentIdealClass K * C⁻¹ := rfl

-- pin: gapsw80_t9_sum_bijection_partialZeta (S_NumberField_exists_completedDedekindZeta_package.lean:5602)
theorem sum_partialDedekindZeta_diffClassMulInv (s : ℂ) :
    ∑ C : ClassGroup (𝓞 K),
        partialDedekindZeta K (differentIdealClass K * C⁻¹) s
      = ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s :=
  Finset.sum_equiv (diffClassMulInvEquiv K) (fun _ => by simp)
    (fun C _ => by rw [diffClassMulInvEquiv_apply])

-- pin: gapsw80_t9_completedDedekindZeta_eq_sum (S_NumberField_exists_completedDedekindZeta_package.lean:5609)
theorem completedDedekindZeta_classSum_eq_sum {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta_classSum K s
      = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s
        * ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s := by
  unfold completedDedekindZeta_classSum covolRepr gammaFactor
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [heckeLambda_eq_completedPartialZeta K (classRepr K C) hs,
    mk_classRepr, inv_inv, ← constK_def]
  set cov : ℂ := ((ZLattice.covolume
      (mixedEmbedding.idealLattice K (classRepr K C)) : ℝ) : ℂ) with hcov_def
  have hcov : cov ≠ 0 := Complex.ofReal_ne_zero.mpr (covolume_pos K _).ne'
  have key : (constK K)⁻¹ * cov ^ s * (constK K * cov ^ (-s)) = 1 := by
    rw [show ∀ a b c d : ℂ, a*b*(c*d) = (a*c)*(b*d) from fun a b c d => by ring,
      inv_mul_cancel₀ (constK_ne_zero K),
      ← Complex.cpow_add _ _ hcov, add_neg_cancel, Complex.cpow_zero, one_mul]
  linear_combination
    (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K
      * Gammaℂ s ^ nrComplexPlaces K * partialDedekindZeta K C s) * key

-- pin: gapsw80_t9_completedDedekindZeta_one_sub_eq_sum (S_NumberField_exists_completedDedekindZeta_package.lean:5629)
theorem completedDedekindZeta_classSum_one_sub_eq_sum {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta_classSum K (1 - s)
      = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s
        * ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s := by
  unfold completedDedekindZeta_classSum covolRepr
  rw [← sum_partialDedekindZeta_diffClassMulInv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [perClass_functionalEquation_step, perClass_identified K _ hs,
    mk_traceDualIdeal, mk_classRepr, inv_inv, mul_inv, inv_inv]
  linear_combination
    (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s
      * partialDedekindZeta K (differentIdealClass K * C⁻¹) s)
    * inv_mul_cancel₀ (constK_ne_zero K)

-- pin: gapsw80_t9_FE_halfplane (S_NumberField_exists_completedDedekindZeta_package.lean:5643)
theorem completedDedekindZeta_classSum_functionalEquation_halfplane {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta_classSum K (1 - s) = completedDedekindZeta_classSum K s :=
  (completedDedekindZeta_classSum_one_sub_eq_sum K hs).trans
    (completedDedekindZeta_classSum_eq_sum K hs).symm

-- pin: gapsw80_t9_isClosed_pair (S_NumberField_exists_completedDedekindZeta_package.lean:5648)
theorem isClosed_pair_zero_one : IsClosed ({(0:ℂ), 1} : Set ℂ) :=
  ((Set.finite_singleton (1:ℂ)).insert 0).isClosed

-- pin: gapsw80_t9_isPreconnected_compl (S_NumberField_exists_completedDedekindZeta_package.lean:5651)
theorem isPreconnected_compl_pair_zero_one :
    IsPreconnected ({(0:ℂ), 1}ᶜ : Set ℂ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank
    (rank_real_complex ▸ Nat.one_lt_ofNat)
    (((Set.finite_singleton (1:ℂ)).insert 0).countable)).isPreconnected

-- pin: gapsw80_t9_nK_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:5657)
theorem nK_ne_zero : (nK K : ℂ) ≠ 0 := by
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'

-- pin: gapsw80_t9_differentiableOn_completedDedekindZeta (S_NumberField_exists_completedDedekindZeta_package.lean:5660)
theorem differentiableOn_completedDedekindZeta_classSum :
    DifferentiableOn ℂ (completedDedekindZeta_classSum K) {(0:ℂ), 1}ᶜ := by
  refine (differentiableOn_const _).mul (DifferentiableOn.fun_sum (fun C _ => ?_))
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  refine ((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (covolRepr_pos K C).ne'))).mul ?_
    ).differentiableWithinAt
  refine ((heckeWeakFEPair K (classRepr K C)).differentiableAt_Λ
    ?_ ?_).comp s ((differentiableAt_const _).mul differentiableAt_id |>.div_const _)
  · left
    exact fun h => hs.1 (by
      have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right two_ne_zero)
      exact this.resolve_left (nK_ne_zero K))
  · left
    intro h
    apply hs.2
    have hk : ((heckeWeakFEPair K (classRepr K C)).k : ℂ)
        = (nK K : ℂ) / 2 := by
      show (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2; push_cast; ring
    rw [hk, div_eq_div_iff (two_ne_zero) (two_ne_zero)] at h
    have h' := mul_right_cancel₀ (two_ne_zero (α := ℂ)) h
    exact mul_left_cancel₀ (nK_ne_zero K) (h'.trans (mul_one _).symm)

-- pin: gapsw80_t9_analyticOnNhd_completedDedekindZeta (S_NumberField_exists_completedDedekindZeta_package.lean:5684)
theorem analyticOnNhd_completedDedekindZeta_classSum :
    AnalyticOnNhd ℂ (completedDedekindZeta_classSum K) {(0:ℂ), 1}ᶜ :=
  (differentiableOn_completedDedekindZeta_classSum K).analyticOnNhd
    isClosed_pair_zero_one.isOpen_compl

-- pin: gapsw80_t9_completedDedekindZeta_FE (S_NumberField_exists_completedDedekindZeta_package.lean:5689)
theorem completedDedekindZeta_classSum_functionalEquation {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedDedekindZeta_classSum K (1 - s) = completedDedekindZeta_classSum K s := by
  have hU : IsOpen ({(0:ℂ), 1}ᶜ : Set ℂ) := (isClosed_pair_zero_one).isOpen_compl
  have hAf := analyticOnNhd_completedDedekindZeta_classSum K
  have hAg : AnalyticOnNhd ℂ
      (fun z => completedDedekindZeta_classSum K (1 - z)) {(0:ℂ), 1}ᶜ := by
    have hswap : Set.MapsTo (fun z : ℂ => 1 - z) {(0:ℂ), 1}ᶜ {(0:ℂ), 1}ᶜ := by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, sub_eq_zero, sub_eq_self] at hz ⊢
      exact ⟨fun h => hz.2 h.symm, hz.1⟩
    exact fun z hz => (hAf _ (hswap hz)).comp (analyticAt_const.sub analyticAt_id)
  have hsU : s ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩
  have h2U : (2:ℂ) ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by norm_num
  refine (hAg.eqOn_of_preconnected_of_frequently_eq hAf
    isPreconnected_compl_pair_zero_one h2U ?_ hsU)

  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2mem : (2:ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
  exact ((Filter.eventually_of_mem (hopen.mem_nhds h2mem)
    (fun z hz => completedDedekindZeta_classSum_functionalEquation_halfplane K hz)).filter_mono
      nhdsWithin_le_nhds).frequently

-- pin: gapsw80_t10_fiberEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:5741)
noncomputable def absNorm_fiberEquiv {n : ℕ} (hn : n ≠ 0) :
    {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n}
      ≃ {I : Ideal (𝓞 K) // absNorm I = n} where
  toFun J := ⟨J.1.1, J.2⟩
  invFun I := ⟨⟨I.1, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp
    (by rw [I.2]; exact hn)⟩, I.2⟩
  left_inv J := by ext; rfl
  right_inv I := rfl

-- pin: gapsw80_t10_fiberCard (S_NumberField_exists_completedDedekindZeta_package.lean:5750)
theorem absNorm_fiberCard {n : ℕ} (hn : n ≠ 0) :
    Nat.card {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n}
      = Nat.card {I : Ideal (𝓞 K) // absNorm I = n} :=
  Nat.card_congr (absNorm_fiberEquiv K hn)

-- pin: gapsw80_t10_fiberFinite (S_NumberField_exists_completedDedekindZeta_package.lean:5755)
scoped instance absNorm_fiberFinite (n : ℕ) :
    Finite {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} := by
  have : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  exact Finite.of_injective
    (fun J => (⟨J.1.1, J.2⟩ : {I : Ideal (𝓞 K) // absNorm I = n}))
    (fun J₁ J₂ h => Subtype.ext (Subtype.ext (by
      simpa only [Subtype.mk.injEq] using h)))

-- pin: gapsw80_t10_LSeriesSummable_dedekindZeta (S_NumberField_exists_completedDedekindZeta_package.lean:5764)
theorem LSeriesSummable_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have key : LSeriesSummable
      (fun n ↦ ((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) : ℂ)) s := by
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun _ => Nat.cast_nonneg _)
      zero_le_one hs

    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ) (r := 1) <| by
      simp only [Real.rpow_one]
      refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp
        tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
      simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
      congr
      rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
        show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
        show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
          simp [Ideal.absNorm_eq_zero_iff],
        Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
        ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
      simp [Set.coe_eq_subtype]
  exact (LSeriesSummable_congr s (fun {n} _ => by push_cast; ring)).mp key

-- pin: gapsw80_t10_term_eq (S_NumberField_exists_completedDedekindZeta_package.lean:5787)
theorem LSeries_term_eq_card_absNorm_fiber (s : ℂ) (n : ℕ) :
    (Nat.card {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} : ℂ)
        * ((n : ℂ)) ^ (-s)
      = LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hE : IsEmpty {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = 0} :=
      ⟨fun J => (Ideal.absNorm_ne_zero_of_nonZeroDivisors J.1) J.2⟩
    simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, absNorm_fiberCard K hn, div_eq_mul_inv,
      ← Complex.cpow_neg]

-- pin: gapsw80_t10_fiber_hasSum (S_NumberField_exists_completedDedekindZeta_package.lean:5798)
theorem hasSum_fiber_absNorm_cpow (s : ℂ) (n : ℕ) :
    HasSum (fun J : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
        ((absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n) := by
  have : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} :=
    Fintype.ofFinite _
  have h1 : (fun J : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
      ((absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) = fun _ => (n : ℂ) ^ (-s) := by
    funext J; rw [J.2]
  rw [h1, ← LSeries_term_eq_card_absNorm_fiber K s n, ← nsmul_eq_mul, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ← Finset.sum_const]
  exact hasSum_fintype _

-- pin: gapsw80_t10_summable_idealNorm (S_NumberField_exists_completedDedekindZeta_package.lean:5811)
theorem summable_idealNorm_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : (Ideal (𝓞 K))⁰ ↦
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by
  rw [← (Equiv.sigmaFiberEquiv
    (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).summable_iff]
  refine Summable.of_norm ?_
  refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨?_, ?_⟩
  · exact fun n =>
      have : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} := Fintype.ofFinite _
      (hasSum_fintype _).summable
  · refine ((LSeriesSummable_dedekindZeta K hs).norm).congr fun n => ?_
    have : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} :=
      Fintype.ofFinite _
    rw [tsum_fintype]
    calc ‖LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n‖
        = ‖(Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} : ℂ)
            * (n : ℂ) ^ (-s)‖ := by rw [LSeries_term_eq_card_absNorm_fiber K s n]
      _ = (Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} : ℝ)
            * ‖(n : ℂ) ^ (-s)‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ∑ c : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n},
            ‖((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
              (Equiv.sigmaFiberEquiv
                (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K))))) ⟨n, c⟩‖ := by
          rw [show (fun c : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
              ‖((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
                (Equiv.sigmaFiberEquiv _)) ⟨n, c⟩‖)
              = fun _ => ‖(n : ℂ) ^ (-s)‖ from funext fun c => by
            simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, c.2]]
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

-- pin: gapsw80_t10_sum_partialDedekindZeta_eq (S_NumberField_exists_completedDedekindZeta_package.lean:5842)
theorem sum_partialDedekindZeta_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s
      = dedekindZeta K s := by
  have hSum := summable_idealNorm_cpow_neg K hs

  have hHS : HasSum
      (fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (dedekindZeta K s) := by
    have hSig := (Equiv.sigmaFiberEquiv
      (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).summable_iff.mpr hSum
    refine (Equiv.sigmaFiberEquiv
      (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).hasSum_iff.mp ?_
    exact HasSum.sigma_of_hasSum
      (LSeriesSummable_dedekindZeta K hs).hasSum
      (hasSum_fiber_absNorm_cpow K s) hSig

  have stepC : ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s
      = ∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) := by
    have hSig : HasSum
        ((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
          (Equiv.sigmaFiberEquiv
            (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))))
        (∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) :=
      (Equiv.sigmaFiberEquiv
        (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))).hasSum_iff.mpr hSum.hasSum
    have hOuter : HasSum (fun C : ClassGroup (𝓞 K) => partialDedekindZeta K C s)
        (∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) :=
      hSig.sigma fun C => (hSum.subtype _).hasSum
    exact (hasSum_fintype _).unique hOuter
  rw [stepC, hHS.tsum_eq]

-- pin: gapsw80_t10_discrCoercion (S_NumberField_exists_completedDedekindZeta_package.lean:5873)
theorem discr_coercion :
    (((|discr K| : ℤ) : ℂ)) = (((|(discr K : ℝ)| : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_intCast, Int.cast_abs]

-- pin: gapsw80_t10_completedDedekindZeta_eq_T1 (S_NumberField_exists_completedDedekindZeta_package.lean:5877)
theorem completedDedekindZeta_classSum_eq_completedDedekindZeta {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta_classSum K s
      = completedDedekindZeta K s := by
  rw [completedDedekindZeta_classSum_eq_sum K hs,
    sum_partialDedekindZeta_eq_dedekindZeta K hs,
    completedDedekindZeta, discr_coercion,
    gammaFactor]
  ring

-- pin: gapsw80_t10_Lambda (S_NumberField_exists_completedDedekindZeta_package.lean:5886)
noncomputable def completedDedekindZeta_continuousExtension (s : ℂ) : ℂ :=
  if s = 0 ∨ s = 1 then completedDedekindZeta_classSum K 2
  else completedDedekindZeta_classSum K s

-- pin: gapsw80_t10_Lambda_eqOn (S_NumberField_exists_completedDedekindZeta_package.lean:5890)
theorem completedDedekindZeta_continuousExtension_eqOn :
    Set.EqOn (completedDedekindZeta_continuousExtension K) (completedDedekindZeta_classSum K)
      {(0 : ℂ), 1}ᶜ := by
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  exact ite_eq_right (not_or.mpr hs)

-- pin: gapsw80_t10_Lambda_differentiableOn (S_NumberField_exists_completedDedekindZeta_package.lean:5897)
theorem differentiableOn_completedDedekindZeta_continuousExtension :
    DifferentiableOn ℂ (completedDedekindZeta_continuousExtension K) {(0 : ℂ), 1}ᶜ :=
  (differentiableOn_completedDedekindZeta_classSum K).congr
    (completedDedekindZeta_continuousExtension_eqOn K)

-- pin: gapsw80_t10_Lambda_eq_T1 (S_NumberField_exists_completedDedekindZeta_package.lean:5902)
theorem completedDedekindZeta_continuousExtension_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta_continuousExtension K s = completedDedekindZeta K s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  rw [completedDedekindZeta_continuousExtension, ite_eq_right (not_or.mpr ⟨hs0, hs1⟩)]
  exact completedDedekindZeta_classSum_eq_completedDedekindZeta K hs

-- pin: gapsw80_t10_Lambda_FE (S_NumberField_exists_completedDedekindZeta_package.lean:5909)
theorem completedDedekindZeta_continuousExtension_functionalEquation (s : ℂ) :
    completedDedekindZeta_continuousExtension K (1 - s) = completedDedekindZeta_continuousExtension K s := by
  unfold completedDedekindZeta_continuousExtension
  by_cases h : s = 0 ∨ s = 1
  · have h' : (1 - s) = 0 ∨ (1 - s) = 1 := by
      rcases h with h0 | h1
      · exact Or.inr (by rw [h0]; ring)
      · exact Or.inl (by rw [h1]; ring)
    rw [ite_eq_left h', ite_eq_left h]
  · rw [not_or] at h
    have h' : ¬((1 - s) = 0 ∨ (1 - s) = 1) := by
      rw [not_or]
      exact ⟨fun hc => h.2 (sub_eq_zero.mp hc).symm, fun hc => h.1 (sub_eq_self.mp hc)⟩
    rw [ite_eq_right h', ite_eq_right (not_or.mpr h)]
    exact completedDedekindZeta_classSum_functionalEquation K h.1 h.2

-- pin: gapsw80_t10_A1_closed (S_NumberField_exists_completedDedekindZeta_package.lean:5925)
theorem completedDedekindZeta_functionalEquation_exists :
    exists_completedDedekindZeta_functionalEquation := by
  intro K
  exact ⟨completedDedekindZeta_continuousExtension K,
    differentiableOn_completedDedekindZeta_continuousExtension K,
    fun s hs => completedDedekindZeta_continuousExtension_eq K hs,
    completedDedekindZeta_continuousExtension_functionalEquation K⟩

-- pin: gapsw80_t11_XiOrderOneHadamard (S_NumberField_exists_completedDedekindZeta_package.lean:5952)
def xiOrderOneHadamard : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ ξ : ℂ → ℂ,
      Differentiable ℂ ξ ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
        ξ s = s * (s - 1) * completedDedekindZeta_classSum K s) ∧
      (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖)

-- pin: gapsw80_t32_XiEndpointNonvanishing (S_NumberField_exists_completedDedekindZeta_package.lean:5988)
def xi_endpointNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * completedDedekindZeta_classSum K s) →
    ξ 0 ≠ 0 ∧ ξ 1 ≠ 0

-- pin: gapsw80_t42_CompletedZetaRealSuperlinear (S_NumberField_exists_completedDedekindZeta_package.lean:6025)
def completedDedekindZeta_realSuperlinear : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ C : ℝ, ∃ s : ℂ,
    2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
    C * ‖s‖ < Real.log ‖s * (s - 1) * completedDedekindZeta_classSum K s‖


end

end NumberField.CompletedDedekindZeta
