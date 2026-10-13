/-
  The completed zeta function `xi`, its Hadamard product, and the order and strip
  bounds.

  This is wave 8 of the `completedDedekindZeta` package: the summand `xiSummand`
  (the `ξ` of the explicit formula, written class by class), the entire function
  `xi = s(s - 1) · completedDedekindZeta_classSum`, its functional equation
  `xi_functionalEquation`, the residue computation at the two endpoints that closes
  the obligation `xi_endpointNonvanishing`, and the whole `kwDyf2` order-bound block:
  the growth lemmas for `‖Γ‖`, `log Γ`, and `t log t`, the Mellin norm bound
  `mellinNormBound` and the `Λ₀` estimate `norm_LambdaZero_le`, the strip bound
  `norm_xiSummand_le` with its constants `xiSummandBound` and `xiBound`, and the
  assembled chain `xiStripBound_holds` → `xiHalfplaneBound` / `xiOrderBound` →
  `xiOrderOneHadamard`.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:6053–6900`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.KwDyf2XiEntireOrderDecomp`, `FLT.Gapsw80T36D1appXiEndpointResidueProof`,
  `FLT.KwDyf2XiOrderBoundDecomp`, `FLT.KwDyf2RealGammaLogBound` and
  `FLT.KwDyf2XiStripBoundAttack` blocks.  The pin's obligation prefixes and
  per-obligation namespaces are dropped; every declaration carries the pin's own name
  and line in the `-- pin:` comment above it (playbook §2.3, §4).

  The pin's file-wide `set_option maxHeartbeats 6400000` and its per-declaration
  `… in` overrides (`3200000`, `6400000`, `12800000`) are not transcribed; the port's
  global cap is `4000000`.  Proofs are adapted to mathlib `v4.34.0`.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.CompletedZeta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

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
open _root_.Complex hiding exp
open Asymptotics Filter Set
open scoped Classical
open scoped Nat
open scoped RealInnerProductSpace
open scoped nonZeroDivisors
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-! ### `xi` and its functional equation -/


-- pin: kwDyf2_P (S_NumberField_exists_completedDedekindZeta_package.lean:6053)
noncomputable abbrev heckeWeakFEPair_classRepr (C : ClassGroup (𝓞 K)) : WeakFEPair ℂ :=
  heckeWeakFEPair K (classRepr K C)

-- pin: kwDyf2_xiSummand (S_NumberField_exists_completedDedekindZeta_package.lean:6056)
noncomputable def xiSummand (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ((covolRepr K C : ℝ) : ℂ) ^ s
    * (s * (s - 1) * (heckeWeakFEPair_classRepr K C).Λ₀ ((nK K : ℂ) * s / 2)
        - 2 * (s - 1) / (nK K : ℂ)
        + 2 * s * (heckeWeakFEPair_classRepr K C).ε / (nK K : ℂ))

-- pin: kwDyf2_xi (S_NumberField_exists_completedDedekindZeta_package.lean:6062)
noncomputable def xi (s : ℂ) : ℂ :=
  (constK K)⁻¹ * ∑ C : ClassGroup (𝓞 K), xiSummand K C s

-- pin: kwDyf2_differentiable_const_cpow (S_NumberField_exists_completedDedekindZeta_package.lean:6065)
theorem differentiable_const_cpow {c : ℝ} (hc : 0 < c) :
    Differentiable ℂ (fun s : ℂ => (c : ℂ) ^ s) :=
  fun _ => differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))

-- pin: kwDyf2_differentiable_xiSummand (S_NumberField_exists_completedDedekindZeta_package.lean:6070)
theorem differentiable_xiSummand (C : ClassGroup (𝓞 K)) :
    Differentiable ℂ (xiSummand K C) := by
  unfold xiSummand
  refine (differentiable_const_cpow (covolRepr_pos K C)).mul ?_
  refine (((differentiable_id.mul (differentiable_id.sub_const 1)).mul ?_).sub
    ((differentiable_const 2 |>.mul (differentiable_id.sub_const 1)).div_const _)).add
    (((differentiable_const 2).mul differentiable_id |>.mul (differentiable_const _)).div_const _)
  exact (heckeWeakFEPair_classRepr K C).differentiable_Λ₀.comp
    (((differentiable_const _).mul differentiable_id).div_const _)

-- pin: kwDyf2_differentiable_xi (S_NumberField_exists_completedDedekindZeta_package.lean:6080)
theorem differentiable_xi : Differentiable ℂ (xi K) := by
  have _em := Classical.em
  unfold xi
  exact (differentiable_const _).mul
    (Differentiable.fun_sum (fun C _ => differentiable_xiSummand K C))

-- pin: kwDyf2_Pk_coe (S_NumberField_exists_completedDedekindZeta_package.lean:6086)
theorem heckeWeakFEPair_classRepr_k_coe (C : ClassGroup (𝓞 K)) :
    ((heckeWeakFEPair_classRepr K C).k : ℂ) = (nK K : ℂ) / 2 := by
  show (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2; push_cast; ring

-- pin: kwDyf2_xiSummand_eq (S_NumberField_exists_completedDedekindZeta_package.lean:6090)
theorem xiSummand_eq (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiSummand K C s =
      ((covolRepr K C : ℝ) : ℂ) ^ s
        * (s * (s - 1)
            * (heckeWeakFEPair_classRepr K C).Λ ((nK K : ℂ) * s / 2)) := by
  unfold xiSummand
  congr 1
  have hf0 : (heckeWeakFEPair_classRepr K C).f₀ = 1 := rfl
  have hg0 : (heckeWeakFEPair_classRepr K C).g₀ = 1 := rfl
  simp only [WeakFEPair.Λ, hf0, hg0, smul_eq_mul, mul_one]
  rw [heckeWeakFEPair_classRepr_k_coe K C]
  have hn : (nK K : ℂ) ≠ 0 := nK_ne_zero K
  have hσ : (nK K : ℂ) * s / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hn hs0) two_ne_zero
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hkσ : (nK K : ℂ) / 2 - (nK K : ℂ) * s / 2 ≠ 0 := by
    rw [div_sub_div_same, ← mul_one_sub]
    exact div_ne_zero (mul_ne_zero hn h1s) two_ne_zero
  field_simp
  ring

-- pin: kwDyf2_xi_eq (S_NumberField_exists_completedDedekindZeta_package.lean:6112)
theorem xi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi K s = s * (s - 1) * completedDedekindZeta_classSum K s := by
  have _em := Classical.em
  unfold xi completedDedekindZeta_classSum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [xiSummand_eq K C hs0 hs1]
  ring

-- pin: kwDyf2_XiOrderBound (S_NumberField_exists_completedDedekindZeta_package.lean:6121)
def xiOrderBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

-- pin: kwDyf2_B1_of_C1 (S_NumberField_exists_completedDedekindZeta_package.lean:6128)
theorem xiOrderOneHadamard_of_xiOrderBound (hC1 : xiOrderBound) :
    xiOrderOneHadamard := by
  have _em := Classical.em
  intro K _ _
  exact ⟨xi K, differentiable_xi K,
    fun s hs0 hs1 => xi_eq K hs0 hs1, hC1 K⟩

-- pin: kwDyf2_sat_xi_FE (S_NumberField_exists_completedDedekindZeta_package.lean:6137)
theorem xi_functionalEquation {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi K (1 - s) = xi K s := by
  have _em := Classical.em
  have h1s0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have h1s1 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
  rw [xi_eq K h1s0 h1s1, xi_eq K hs0 hs1,
    completedDedekindZeta_classSum_functionalEquation K hs0 hs1]
  ring

-- pin: gapsw80_t36_nK_cast_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:6178)
theorem nK_cast_ne_zero : (nK K : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'

-- pin: gapsw80_t36_nK_cast_half (S_NumberField_exists_completedDedekindZeta_package.lean:6181)
theorem nK_cast_half : (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2 := by
  push_cast; ring

-- pin: gapsw80_t36_affine_tendsto (S_NumberField_exists_completedDedekindZeta_package.lean:6184)
theorem nK_affine_tendsto_nhdsNE (a : ℂ) :
    Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] a) (𝓝[≠] ((nK K : ℂ) * a / 2)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (((continuous_const.mul continuous_id').div_const 2).tendsto a).mono_left
      nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall (fun s hs ↦ ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    exact fun h ↦ hs (mul_left_cancel₀ (nK_cast_ne_zero K)
      (by linear_combination 2 * h))

-- pin: gapsw80_t36_perClass_residue_one (S_NumberField_exists_completedDedekindZeta_package.lean:6196)
theorem perClass_residue_one (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ ((covolRepr K C : ℝ) : ℂ) ^ s
        * ((s - 1)
          * (heckeWeakFEPair K (classRepr K C)).Λ ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 1) (𝓝 (2 / (nK K : ℂ))) := by
  set P := heckeWeakFEPair K (classRepr K C)
  have hn := nK_cast_ne_zero K
  have hk : (P.k : ℂ) = (nK K : ℂ) / 2 := nK_cast_half K

  have hmap : Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) := by
    have := nK_affine_tendsto_nhdsNE K 1
    rwa [mul_one, ← hk] at this
  have hres : Tendsto (fun s : ℂ ↦ ((nK K : ℂ) * s / 2 - (P.k : ℂ))
        * P.Λ ((nK K : ℂ) * s / 2)) (𝓝[≠] 1) (𝓝 P.ε) := by
    have h := P.Λ_residue_k.comp hmap
    simpa only [Function.comp_def, smul_eq_mul,
      show (P.g₀ : ℂ) = 1 from rfl, mul_one] using h

  have hres' : Tendsto (fun s : ℂ ↦ (s - 1) * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 1) (𝓝 ((2 / (nK K : ℂ)) * P.ε)) := by
    refine (hres.const_mul (2 / (nK K : ℂ))).congr' (Eventually.of_forall fun s ↦ ?_)
    rw [hk, show (2 / (nK K : ℂ)) * (((nK K : ℂ) * s / 2 - (nK K : ℂ) / 2)
          * P.Λ ((nK K : ℂ) * s / 2))
        = ((2 / (nK K : ℂ)) * ((nK K : ℂ) / 2)) * ((s - 1) * P.Λ ((nK K : ℂ) * s / 2))
        from by ring,
      show (2 / (nK K : ℂ)) * ((nK K : ℂ) / 2) = 1 from by field_simp, one_mul]

  have hcvne : ((covolRepr K C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (covolRepr_pos K C).ne'
  have hcov : Tendsto (fun s : ℂ ↦ ((covolRepr K C : ℝ) : ℂ) ^ s)
      (𝓝[≠] 1) (𝓝 ((covolRepr K C : ℝ) : ℂ)) := by
    have := (continuousAt_const_cpow hcvne (b := 1)).tendsto
    simpa only [Complex.cpow_one] using this.mono_left nhdsWithin_le_nhds
  have hcε : ((covolRepr K C : ℝ) : ℂ) * P.ε = 1 := by
    show ((covolRepr K C : ℝ) : ℂ) * ((covolRepr K C : ℝ) : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hcvne
  have := hcov.mul hres'
  rwa [show ((covolRepr K C : ℝ) : ℂ) * ((2 / (nK K : ℂ)) * P.ε)
      = (2 / (nK K : ℂ)) * (((covolRepr K C : ℝ) : ℂ) * P.ε) from by ring,
    hcε, mul_one] at this

-- pin: gapsw80_t36_perClass_residue_zero (S_NumberField_exists_completedDedekindZeta_package.lean:6239)
theorem perClass_residue_zero (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ ((covolRepr K C : ℝ) : ℂ) ^ s
        * (s * (heckeWeakFEPair K (classRepr K C)).Λ
            ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 0) (𝓝 (-(2 / (nK K : ℂ)))) := by
  set P := heckeWeakFEPair K (classRepr K C)
  have hn := nK_cast_ne_zero K
  have hmap : Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    have := nK_affine_tendsto_nhdsNE K 0
    simpa using this
  have hres : Tendsto (fun s : ℂ ↦ ((nK K : ℂ) * s / 2) * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 0) (𝓝 (-1 : ℂ)) := by
    have h := P.Λ_residue_zero.comp hmap
    simpa only [Function.comp_def, smul_eq_mul,
      show (P.f₀ : ℂ) = 1 from rfl] using h
  have hres' : Tendsto (fun s : ℂ ↦ s * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 0) (𝓝 (-(2 / (nK K : ℂ)))) := by
    have h := hres.const_mul (2 / (nK K : ℂ))
    rw [show (2 / (nK K : ℂ)) * (-1) = -(2 / (nK K : ℂ)) from by ring] at h
    refine h.congr' (Eventually.of_forall fun s ↦ ?_)
    rw [show (2 / (nK K : ℂ)) * ((nK K : ℂ) * s / 2 * P.Λ ((nK K : ℂ) * s / 2))
        = ((2 / (nK K : ℂ)) * ((nK K : ℂ) / 2)) * (s * P.Λ ((nK K : ℂ) * s / 2))
        from by ring,
      show (2 / (nK K : ℂ)) * ((nK K : ℂ) / 2) = 1 from by field_simp, one_mul]
  have hcvne : ((covolRepr K C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (covolRepr_pos K C).ne'
  have hcov : Tendsto (fun s : ℂ ↦ ((covolRepr K C : ℝ) : ℂ) ^ s)
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have := (continuousAt_const_cpow hcvne (b := 0)).tendsto
    simpa only [Complex.cpow_zero] using this.mono_left nhdsWithin_le_nhds
  have := hcov.mul hres'
  rwa [one_mul] at this

-- pin: gapsw80_t36_xiResidueVal (S_NumberField_exists_completedDedekindZeta_package.lean:6272)
noncomputable def xiResidueVal : ℂ :=
  (constK K)⁻¹
    * (2 * (Fintype.card (ClassGroup (𝓞 K)) : ℂ) / (nK K : ℂ))

-- pin: gapsw80_t36_xiResidueVal_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:6276)
theorem xiResidueVal_ne_zero : xiResidueVal K ≠ 0 := by
  refine mul_ne_zero (inv_ne_zero (constK_ne_zero K)) (div_ne_zero ?_ ?_)
  · exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · exact nK_cast_ne_zero K

-- pin: gapsw80_t36_tendsto_xi_rhs_one (S_NumberField_exists_completedDedekindZeta_package.lean:6283)
theorem tendsto_xi_at_one :
    Tendsto (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta_classSum K s)
      (𝓝[≠] 1) (𝓝 (xiResidueVal K)) := by
  have hsum : Tendsto (fun s : ℂ ↦
        ∑ C : ClassGroup (𝓞 K), ((covolRepr K C : ℝ) : ℂ) ^ s
          * ((s - 1) * (heckeWeakFEPair K (classRepr K C)).Λ
              ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 1) (𝓝 (∑ _C : ClassGroup (𝓞 K), (2 / (nK K : ℂ)))) :=
    tendsto_finsetSum _ (fun C _ ↦ perClass_residue_one K C)
  have hs : Tendsto (fun s : ℂ ↦ s) (𝓝[≠] 1) (𝓝 (1:ℂ)) :=
    continuous_id.tendsto' 1 1 rfl |>.mono_left nhdsWithin_le_nhds
  have hG := (hsum.const_mul (constK K)⁻¹).mul hs
  have hval : (constK K)⁻¹
        * (∑ _C : ClassGroup (𝓞 K), (2 / (nK K : ℂ))) * 1
      = xiResidueVal K := by
    rw [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    unfold xiResidueVal; ring
  rw [← hval]
  refine hG.congr' (Eventually.of_forall fun s ↦ ?_)
  unfold completedDedekindZeta_classSum
  have hsum_eq : ∑ C : ClassGroup (𝓞 K),
        ((covolRepr K C : ℝ) : ℂ) ^ s * ((s - 1)
          * (heckeWeakFEPair K (classRepr K C)).Λ
              ((nK K : ℂ) * s / 2))
      = (s - 1) * ∑ C : ClassGroup (𝓞 K),
          ((covolRepr K C : ℝ) : ℂ) ^ s
            * (heckeWeakFEPair K (classRepr K C)).Λ
                ((nK K : ℂ) * s / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun C _ ↦ by ring)
  rw [hsum_eq]; ring

-- pin: gapsw80_t36_tendsto_xi_rhs_zero (S_NumberField_exists_completedDedekindZeta_package.lean:6316)
theorem tendsto_xi_at_zero :
    Tendsto (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta_classSum K s)
      (𝓝[≠] 0) (𝓝 (xiResidueVal K)) := by
  have hsum : Tendsto (fun s : ℂ ↦
        ∑ C : ClassGroup (𝓞 K), ((covolRepr K C : ℝ) : ℂ) ^ s
          * (s * (heckeWeakFEPair K (classRepr K C)).Λ
              ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 0) (𝓝 (∑ _C : ClassGroup (𝓞 K), (-(2 / (nK K : ℂ))))) :=
    tendsto_finsetSum _ (fun C _ ↦ perClass_residue_zero K C)
  have hs1 : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 0) (𝓝 (-1:ℂ)) := by
    have := (continuous_sub_right (1:ℂ)).tendsto (0:ℂ)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hG := (hsum.const_mul (constK K)⁻¹).mul hs1
  have hval : (constK K)⁻¹
        * (∑ _C : ClassGroup (𝓞 K), (-(2 / (nK K : ℂ)))) * (-1)
      = xiResidueVal K := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    unfold xiResidueVal; ring
  rw [← hval]
  refine hG.congr' (Eventually.of_forall fun s ↦ ?_)
  unfold completedDedekindZeta_classSum
  have hsum_eq : ∑ C : ClassGroup (𝓞 K),
        ((covolRepr K C : ℝ) : ℂ) ^ s * (s
          * (heckeWeakFEPair K (classRepr K C)).Λ
              ((nK K : ℂ) * s / 2))
      = s * ∑ C : ClassGroup (𝓞 K),
          ((covolRepr K C : ℝ) : ℂ) ^ s
            * (heckeWeakFEPair K (classRepr K C)).Λ
                ((nK K : ℂ) * s / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun C _ ↦ by ring)
  rw [hsum_eq]; ring

-- pin: gapsw80_t36_D1app_closed (S_NumberField_exists_completedDedekindZeta_package.lean:6350)
theorem xi_endpointNonvanishing_holds : xi_endpointNonvanishing := by
  have _em := Classical.em
  intro K _ _ ξ hdiff hagr

  have heq1 : (fun s ↦ s * (s - 1) * completedDedekindZeta_classSum K s)
      =ᶠ[𝓝[≠] (1:ℂ)] ξ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
        (isOpen_ne.mem_nhds (one_ne_zero (α := ℂ))),
      self_mem_nhdsWithin] with s hs0 hs1
    exact (hagr s hs0 hs1).symm
  have heq0 : (fun s ↦ s * (s - 1) * completedDedekindZeta_classSum K s)
      =ᶠ[𝓝[≠] (0:ℂ)] ξ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (zero_ne_one (α := ℂ)))]
      with s hs0 hs1
    exact (hagr s hs0 hs1).symm
  have hξ1 : ξ 1 = xiResidueVal K :=
    tendsto_nhds_unique
      ((hdiff.continuous.tendsto 1).mono_left nhdsWithin_le_nhds)
      ((tendsto_xi_at_one K).congr' heq1)
  have hξ0 : ξ 0 = xiResidueVal K :=
    tendsto_nhds_unique
      ((hdiff.continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
      ((tendsto_xi_at_zero K).congr' heq0)
  exact ⟨hξ0 ▸ xiResidueVal_ne_zero K, hξ1 ▸ xiResidueVal_ne_zero K⟩

-- pin: kwDyf2_norm_Gamma_le_Gamma_re (S_NumberField_exists_completedDedekindZeta_package.lean:6395)
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  have _em := Classical.em
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs,
    Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

-- pin: kwDyf2_norm_le_norm_one_sub (S_NumberField_exists_completedDedekindZeta_package.lean:6405)
theorem norm_le_norm_one_sub {s : ℂ} (hs : s.re ≤ 1/2) :
    ‖s‖ ≤ ‖1 - s‖ := by
  have h : ‖s‖^2 ≤ ‖1 - s‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, zero_sub, neg_mul_neg]
    nlinarith
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg s), Real.sqrt_sq (norm_nonneg (1 - s))] at this

-- pin: kwDyf2_norm_mul_log_norm_nonneg (S_NumberField_exists_completedDedekindZeta_package.lean:6414)
theorem norm_mul_log_norm_nonneg {s : ℂ} (hs : 2 ≤ ‖s‖) :
    0 ≤ ‖s‖ * Real.log ‖s‖ :=
  mul_nonneg (by linarith) (Real.log_nonneg (by linarith))

-- pin: kwDyf2_norm_one_sub_le (S_NumberField_exists_completedDedekindZeta_package.lean:6418)
theorem norm_one_sub_le {s : ℂ} (hs : 2 ≤ ‖s‖) :
    ‖1 - s‖ ≤ (3/2) * ‖s‖ :=
  calc ‖1 - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le 1 s
    _ = 1 + ‖s‖ := by rw [norm_one]
    _ ≤ (3/2) * ‖s‖ := by linarith

-- pin: kwDyf2_refl_growth_bound (S_NumberField_exists_completedDedekindZeta_package.lean:6424)
theorem norm_mul_log_norm_one_sub_le {s : ℂ} (hs : 2 ≤ ‖s‖) (hle : ‖s‖ ≤ ‖1 - s‖) :
    ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 3 * ‖s‖ * Real.log ‖s‖ := by
  have hlog2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hs
  have hlogpos : 0 < Real.log ‖s‖ :=
    lt_of_lt_of_le (Real.log_pos one_lt_two) hlog2
  have h32 : ‖1 - s‖ ≤ (3/2) * ‖s‖ := norm_one_sub_le hs
  have h1spos : (0:ℝ) < ‖1 - s‖ := lt_of_lt_of_le two_pos (hs.trans hle)
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hlog : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
    calc Real.log ‖1 - s‖ ≤ Real.log ((3/2) * ‖s‖) :=
          Real.log_le_log h1spos h32
      _ = Real.log (3/2) + Real.log ‖s‖ :=
          Real.log_mul (by norm_num) hspos.ne'
      _ ≤ Real.log 2 + Real.log ‖s‖ := by
          have : Real.log (3/2) ≤ Real.log 2 :=
            Real.log_le_log (by norm_num) (by norm_num)
          linarith
      _ ≤ 2 * Real.log ‖s‖ := by linarith
  calc ‖1 - s‖ * Real.log ‖1 - s‖
      ≤ (3/2) * ‖s‖ * (2 * Real.log ‖s‖) := by
        refine mul_le_mul h32 hlog ?_ (by linarith)
        exact Real.log_nonneg (le_trans one_le_two (hs.trans hle))
    _ = 3 * ‖s‖ * Real.log ‖s‖ := by ring

-- pin: kwDyf2_XiHalfplaneBound (S_NumberField_exists_completedDedekindZeta_package.lean:6448)
def xiHalfplaneBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → 2 ≤ ‖s‖ →
      Real.log ‖xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

-- pin: kwDyf2_C1_of_halfplane (S_NumberField_exists_completedDedekindZeta_package.lean:6453)
theorem xiOrderBound_of_xiHalfplaneBound (hHalf : xiHalfplaneBound) :
    xiOrderBound := by
  have _em := Classical.em
  intro K _ _
  obtain ⟨C, hC⟩ := hHalf K
  refine ⟨3 * max C 0, fun s hs => ?_⟩
  have hsln : 0 ≤ ‖s‖ * Real.log ‖s‖ := norm_mul_log_norm_nonneg hs
  rcases le_or_gt (1/2 : ℝ) s.re with hre | hre
  ·
    calc Real.log ‖xi K s‖
        ≤ C * ‖s‖ * Real.log ‖s‖ := hC s hre hs
      _ ≤ max C 0 * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr; exact le_max_left C 0
      _ ≤ 3 * max C 0 * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc (3 * max C 0)]
          gcongr
          nlinarith [le_max_right C 0]
  ·
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
    have hs1 : s ≠ 1 := fun h => by simp [h, Complex.one_re] at hre; linarith
    rw [← xi_functionalEquation K hs0 hs1]
    have h1re : 1/2 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have hle : ‖s‖ ≤ ‖1 - s‖ := norm_le_norm_one_sub hre.le
    have h1norm : 2 ≤ ‖1 - s‖ := le_trans hs hle
    calc Real.log ‖xi K (1 - s)‖
        ≤ C * ‖1 - s‖ * Real.log ‖1 - s‖ := hC (1 - s) h1re h1norm
      _ ≤ max C 0 * (‖1 - s‖ * Real.log ‖1 - s‖) := by
          rw [mul_assoc]; gcongr
          · exact norm_mul_log_norm_nonneg h1norm
          · exact le_max_left C 0
      _ ≤ max C 0 * (3 * ‖s‖ * Real.log ‖s‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_log_norm_one_sub_le hs hle)
            (le_max_right C 0)
      _ = 3 * max C 0 * ‖s‖ * Real.log ‖s‖ := by ring

-- pin: kwDyf2_XiRightHalfBound (S_NumberField_exists_completedDedekindZeta_package.lean:6489)
def xiRightHalfBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 3/2 ≤ s.re → 2 ≤ ‖s‖ →
      Real.log ‖xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

-- pin: kwDyf2_XiStripBound (S_NumberField_exists_completedDedekindZeta_package.lean:6494)
def xiStripBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → 2 ≤ ‖s‖ →
      Real.log ‖xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

-- pin: kwDyf2_halfplane_of_C1a_C1b (S_NumberField_exists_completedDedekindZeta_package.lean:6499)
theorem xiHalfplaneBound_of_rightHalfBound_stripBound
    (hC1a : xiRightHalfBound) (hC1b : xiStripBound) :
    xiHalfplaneBound := by
  have _em := Classical.em
  intro K _ _
  obtain ⟨Ca, hCa⟩ := hC1a K
  obtain ⟨Cb, hCb⟩ := hC1b K
  refine ⟨max (max Ca 0) (max Cb 0), fun s hre hs => ?_⟩
  have hsln : 0 ≤ ‖s‖ * Real.log ‖s‖ := norm_mul_log_norm_nonneg hs
  rcases le_or_gt (3/2 : ℝ) s.re with hre2 | hre2
  · calc Real.log ‖xi K s‖ ≤ Ca * ‖s‖ * Real.log ‖s‖ := hCa s hre2 hs
      _ ≤ max (max Ca 0) (max Cb 0) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr
          exact le_trans (le_max_left Ca 0) (le_max_left _ _)
  · calc Real.log ‖xi K s‖ ≤ Cb * ‖s‖ * Real.log ‖s‖ := hCb s hre hre2.le hs
      _ ≤ max (max Ca 0) (max Cb 0) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr
          exact le_trans (le_max_left Cb 0) (le_max_right _ _)

-- pin: kwDyf2_C1_of_C1a_C1b (S_NumberField_exists_completedDedekindZeta_package.lean:6520)
theorem xiOrderBound_of_rightHalfBound_stripBound
    (hC1a : xiRightHalfBound) (hC1b : xiStripBound) :
    xiOrderBound :=
  xiOrderBound_of_xiHalfplaneBound (xiHalfplaneBound_of_rightHalfBound_stripBound hC1a hC1b)

-- pin: kwDyf2_monotoneOn_mul_log (S_NumberField_exists_completedDedekindZeta_package.lean:6549)
theorem monotoneOn_mul_log : MonotoneOn (fun t => t * Real.log t) (Set.Ici 1) := by
  have _em := Classical.em
  intro a ha b hb hab
  exact mul_le_mul hab (Real.log_le_log (lt_of_lt_of_le one_pos ha) hab)
    (Real.log_nonneg ha) (le_trans (le_of_lt one_pos) hb)

-- pin: kwDyf2_log_factorial_le (S_NumberField_exists_completedDedekindZeta_package.lean:6555)
theorem log_factorial_le {n : ℕ} :
    Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have _em := Classical.em
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · calc Real.log (n ! : ℝ)
        ≤ Real.log ((n : ℝ) ^ n) := by
          refine Real.log_le_log (by exact_mod_cast n.factorial_pos) ?_
          exact_mod_cast Nat.factorial_le_pow n
      _ = (n : ℝ) * Real.log (n : ℝ) := by
          rw [Real.log_pow]

-- pin: kwDyf2_log_Gamma_le_self_mul_log (S_NumberField_exists_completedDedekindZeta_package.lean:6569)
theorem log_Gamma_le_self_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ x * Real.log x := by
  have _em := Classical.em
  set n := ⌊x⌋₊ with hn_def
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (le_trans zero_le_one hx)
  have hxn1 : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1

  have ha : 0 ≤ (n:ℝ) + 1 - x := by linarith
  have hb : 0 ≤ x - (n:ℝ) := by linarith
  have hab : ((n:ℝ) + 1 - x) + (x - (n:ℝ)) = 1 := by ring
  have hcomb : ((n:ℝ) + 1 - x) • (n : ℝ) + (x - (n:ℝ)) • ((n : ℝ) + 1) = x := by
    simp only [smul_eq_mul]; ring

  have hconv := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hnpos)
    (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < (n:ℝ) + 1)) ha hb hab
  rw [hcomb, Function.comp_apply, Function.comp_apply, Function.comp_apply,
    smul_eq_mul, smul_eq_mul] at hconv

  have hGn : Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hn1).symm
    rw [hcast]; exact_mod_cast Real.Gamma_nat_eq_factorial (n - 1)
  have hGn1 : Real.Gamma ((n : ℝ) + 1) = (n ! : ℝ) := by
    exact_mod_cast Real.Gamma_nat_eq_factorial n
  rw [hGn, hGn1] at hconv

  have hend1 : Real.log ((n - 1)! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc Real.log ((n - 1)! : ℝ)
        ≤ Real.log (n ! : ℝ) := by
          refine Real.log_le_log (by exact_mod_cast (n-1).factorial_pos) ?_
          exact_mod_cast Nat.factorial_le (Nat.sub_le n 1)
      _ ≤ (n : ℝ) * Real.log (n : ℝ) := log_factorial_le
  have hend2 : Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    log_factorial_le

  have hstep : Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    calc Real.log (Real.Gamma x)
        ≤ ((n:ℝ)+1-x) * Real.log ((n - 1)! : ℝ)
            + (x-(n:ℝ)) * Real.log (n ! : ℝ) := hconv
      _ ≤ ((n:ℝ)+1-x) * ((n : ℝ) * Real.log (n : ℝ))
            + (x-(n:ℝ)) * ((n : ℝ) * Real.log (n : ℝ)) := by gcongr
      _ = (n : ℝ) * Real.log (n : ℝ) := by rw [← add_mul, hab, one_mul]

  exact hstep.trans (monotoneOn_mul_log
    (Set.mem_Ici.mpr (by exact_mod_cast hn1)) (Set.mem_Ici.mpr hx) hnx)

-- pin: kwDyf2_log_norm_Gamma_le_re (S_NumberField_exists_completedDedekindZeta_package.lean:6617)
theorem log_norm_Gamma_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    Real.log ‖Complex.Gamma s‖ ≤ s.re * Real.log s.re := by
  have _em := Classical.em
  have hrepos : 0 < s.re := lt_of_lt_of_le one_pos hs
  have hΓ : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re :=
    norm_Gamma_le_Gamma_re hrepos
  have hΓne : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have : s.re = (-(m:ℂ)).re := by rw [hm]
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith
  calc Real.log ‖Complex.Gamma s‖
      ≤ Real.log (Real.Gamma s.re) :=
        Real.log_le_log (norm_pos_iff.mpr hΓne) hΓ
    _ ≤ s.re * Real.log s.re := log_Gamma_le_self_mul_log hs

-- pin: kwDyf2_log_norm_Gamma_le_norm_mul_log_norm (S_NumberField_exists_completedDedekindZeta_package.lean:6633)
theorem log_norm_Gamma_le_norm_mul_log_norm {s : ℂ}
    (hs : 1 ≤ s.re) :
    Real.log ‖Complex.Gamma s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  have hre_norm : s.re ≤ ‖s‖ := Complex.re_le_norm s
  exact (log_norm_Gamma_le_re hs).trans
    (monotoneOn_mul_log (Set.mem_Ici.mpr hs)
      (Set.mem_Ici.mpr (le_trans hs hre_norm)) hre_norm)

-- pin: kwDyf2_rpow_le_endpoints (S_NumberField_exists_completedDedekindZeta_package.lean:6671)
theorem rpow_le_endpoints {t a b σ : ℝ} (ht : 0 < t)
    (ha : a ≤ σ) (hb : σ ≤ b) : t ^ σ ≤ t ^ a + t ^ b := by
  have _em := Classical.em
  have hta : (0:ℝ) ≤ t ^ a := Real.rpow_nonneg ht.le a
  have htb : (0:ℝ) ≤ t ^ b := Real.rpow_nonneg ht.le b
  rcases le_total t 1 with h1 | h1
  · exact le_add_of_le_of_nonneg
      (Real.rpow_le_rpow_of_exponent_ge ht h1 ha) htb
  · exact le_add_of_nonneg_of_le hta
      (Real.rpow_le_rpow_of_exponent_le h1 hb)


/-! ### The Mellin norm bound on `Λ₀` -/

section LambdaZeroBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


-- pin: kwDyf2_MellinNormBound (S_NumberField_exists_completedDedekindZeta_package.lean:6685)
noncomputable def mellinNormBound (P : WeakFEPair E) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ‖(t : ℂ) ^ ((x:ℂ) - 1) • P.f_modif t‖

omit [CompleteSpace E] in
-- pin: kwDyf2_MellinNormBound_integrable (S_NumberField_exists_completedDedekindZeta_package.lean:6690)
theorem mellinNormBound_integrable (P : WeakFEPair E) (x : ℝ) :
    IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((x:ℂ) - 1) • P.f_modif t‖)
      (Set.Ioi (0:ℝ)) :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin (x:ℂ)).1.norm

omit [CompleteSpace E] in
-- pin: kwDyf2_MellinNormBound_nonneg (S_NumberField_exists_completedDedekindZeta_package.lean:6697)
theorem mellinNormBound_nonneg (P : WeakFEPair E) (x : ℝ) :
    0 ≤ mellinNormBound P x :=
  integral_nonneg (fun _ => norm_nonneg _)

omit [CompleteSpace E] in
-- pin: kwDyf2_norm_Λ₀_le (S_NumberField_exists_completedDedekindZeta_package.lean:6704)
theorem norm_LambdaZero_le (P : WeakFEPair E) {s : ℂ} {a b : ℝ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖P.Λ₀ s‖ ≤ mellinNormBound P a + mellinNormBound P b := by
  have _em := Classical.em

  show ‖mellin P.f_modif s‖ ≤ _
  unfold mellin

  refine (norm_integral_le_integral_norm _).trans ?_

  have hint_a := mellinNormBound_integrable P a
  have hint_b := mellinNormBound_integrable P b
  rw [show mellinNormBound P a + mellinNormBound P b
        = ∫ t in Set.Ioi (0:ℝ),
            (‖(t:ℂ)^((a:ℂ)-1) • P.f_modif t‖ + ‖(t:ℂ)^((b:ℂ)-1) • P.f_modif t‖)
      from (integral_add hint_a hint_b).symm]
  refine setIntegral_mono_on (P.isStrongFEPair_toStrongFEPair.hasMellin s).1.norm
    (hint_a.add hint_b) measurableSet_Ioi (fun t ht => ?_)

  have htpos : (0:ℝ) < t := ht
  simp only [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right
    (rpow_le_endpoints htpos (by linarith) (by linarith)) (norm_nonneg _)


end LambdaZeroBound

-- pin: kwDyf2_Bconst (S_NumberField_exists_completedDedekindZeta_package.lean:6735)
noncomputable def xiSummandBound (C : ClassGroup (𝓞 K)) : ℝ :=
  (covolRepr K C ^ (1/2 : ℝ) + covolRepr K C ^ (3/2 : ℝ))
    * ((3/2) * (mellinNormBound (heckeWeakFEPair_classRepr K C) ((nK K : ℝ)/4)
                  + mellinNormBound (heckeWeakFEPair_classRepr K C) ((3 * nK K : ℝ)/4))
        + 3 / (nK K : ℝ) + 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ))

-- pin: kwDyf2_norm_xiSummand_le (S_NumberField_exists_completedDedekindZeta_package.lean:6743)
theorem norm_xiSummand_le (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hre1 : 1/2 ≤ s.re) (hre2 : s.re ≤ 3/2) (hs : 2 ≤ ‖s‖) :
    ‖xiSummand K C s‖ ≤ xiSummandBound K C * ‖s‖^2 := by
  have _em := Classical.em
  have hnK : (0:ℝ) < (nK K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < nK K)
  have hcov := covolRepr_pos K C
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hs1 : ‖s - 1‖ ≤ (3/2) * ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + 1 := by
          have := norm_sub_le s 1; rwa [norm_one] at this
      _ ≤ (3/2) * ‖s‖ := by linarith
  have hsle : ‖s‖ ≤ ‖s‖^2 := by nlinarith

  have hcovpow : ‖((covolRepr K C : ℝ) : ℂ) ^ s‖
      ≤ covolRepr K C ^ (1/2:ℝ) + covolRepr K C ^ (3/2:ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcov]
    exact rpow_le_endpoints hcov hre1 hre2

  have hre_ns : ((nK K : ℂ) * s / 2).re = (nK K : ℝ) * s.re / 2 := by
    simp [Complex.mul_re]
  have hL0 : ‖(heckeWeakFEPair_classRepr K C).Λ₀ ((nK K : ℂ) * s / 2)‖
      ≤ mellinNormBound (heckeWeakFEPair_classRepr K C) ((nK K : ℝ)/4)
        + mellinNormBound (heckeWeakFEPair_classRepr K C) ((3 * nK K : ℝ)/4) := by
    refine norm_LambdaZero_le (heckeWeakFEPair_classRepr K C) ?_ ?_
    · rw [hre_ns]; nlinarith
    · rw [hre_ns]; nlinarith
  set Msum := mellinNormBound (heckeWeakFEPair_classRepr K C) ((nK K : ℝ)/4)
              + mellinNormBound (heckeWeakFEPair_classRepr K C) ((3 * nK K : ℝ)/4)
  have hMsum_nn : 0 ≤ Msum :=
    add_nonneg (mellinNormBound_nonneg _ _) (mellinNormBound_nonneg _ _)

  have hbracket :
      ‖s * (s - 1) * (heckeWeakFEPair_classRepr K C).Λ₀ ((nK K : ℂ) * s / 2)
        - 2 * (s - 1) / (nK K : ℂ) + 2 * s * (heckeWeakFEPair_classRepr K C).ε / (nK K : ℂ)‖
      ≤ ((3/2) * Msum + 3 / (nK K : ℝ) + 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ)) * ‖s‖^2 := by
    have hnorm_nK : ‖(nK K : ℂ)‖ = (nK K : ℝ) := by
      rw [show ((nK K : ℕ) : ℂ) = ((nK K : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg hnK.le]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) (le_refl _)).trans ?_
    have h1 : ‖s * (s - 1) * (heckeWeakFEPair_classRepr K C).Λ₀ ((nK K : ℂ) * s / 2)‖
        ≤ (3/2) * Msum * ‖s‖^2 := by
      rw [norm_mul, norm_mul]
      calc ‖s‖ * ‖s - 1‖ * ‖(heckeWeakFEPair_classRepr K C).Λ₀ ((nK K : ℂ) * s / 2)‖
          ≤ ‖s‖ * ((3/2)*‖s‖) * Msum := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)) hL0
              (norm_nonneg _) ?_
            positivity
        _ = (3/2) * Msum * ‖s‖^2 := by ring
    have h2 : ‖2 * (s - 1) / (nK K : ℂ)‖ ≤ 3 / (nK K : ℝ) * ‖s‖^2 := by
      rw [norm_div, norm_mul, hnorm_nK, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      calc 2 * ‖s - 1‖ / (nK K : ℝ)
          ≤ 2 * ((3/2)*‖s‖) / (nK K : ℝ) := by gcongr
        _ = 3 * ‖s‖ / (nK K : ℝ) := by ring
        _ ≤ 3 * ‖s‖^2 / (nK K : ℝ) := by gcongr
        _ = 3 / (nK K : ℝ) * ‖s‖^2 := by ring
    have h3 : ‖2 * s * (heckeWeakFEPair_classRepr K C).ε / (nK K : ℂ)‖
        ≤ 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by
      rw [norm_div, norm_mul, norm_mul, hnorm_nK, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      calc 2 * ‖s‖ * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ)
          ≤ 3 * ‖s‖^2 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ) := by
            gcongr; nlinarith [norm_nonneg s]
        _ = 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by ring
    calc _ ≤ (3/2) * Msum * ‖s‖^2 + 3 / (nK K : ℝ) * ‖s‖^2
              + 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by
          gcongr
      _ = ((3/2) * Msum + 3 / (nK K : ℝ) + 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ)) * ‖s‖^2 := by
          ring

  unfold xiSummand xiSummandBound
  rw [norm_mul]
  calc ‖((covolRepr K C : ℝ) : ℂ) ^ s‖ * ‖_‖
      ≤ (covolRepr K C ^ (1/2:ℝ) + covolRepr K C ^ (3/2:ℝ))
          * (((3/2) * Msum + 3 / (nK K : ℝ)
              + 3 * ‖(heckeWeakFEPair_classRepr K C).ε‖ / (nK K : ℝ)) * ‖s‖^2) :=
        mul_le_mul hcovpow hbracket (norm_nonneg _)
          (add_nonneg (Real.rpow_nonneg hcov.le _) (Real.rpow_nonneg hcov.le _))
    _ = _ := by ring

-- pin: kwDyf2_Aconst (S_NumberField_exists_completedDedekindZeta_package.lean:6823)
noncomputable def xiBound : ℝ :=
  max 1 (‖(constK K)⁻¹‖ * ∑ C : ClassGroup (𝓞 K), xiSummandBound K C)

-- pin: kwDyf2_one_le_Aconst (S_NumberField_exists_completedDedekindZeta_package.lean:6826)
theorem one_le_xiBound : 1 ≤ xiBound K := le_max_left _ _

-- pin: kwDyf2_norm_xi_le_Aconst_sq (S_NumberField_exists_completedDedekindZeta_package.lean:6830)
theorem norm_xi_le_xiBound_mul_sq {s : ℂ}
    (hre1 : 1/2 ≤ s.re) (hre2 : s.re ≤ 3/2) (hs : 2 ≤ ‖s‖) :
    ‖xi K s‖ ≤ xiBound K * ‖s‖^2 := by
  have _em := Classical.em
  unfold xi
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left
    ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun C _ =>
      norm_xiSummand_le K C hre1 hre2 hs))) (norm_nonneg _)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

-- pin: kwDyf2_one_le_norm_mul_log (S_NumberField_exists_completedDedekindZeta_package.lean:6842)
theorem one_le_norm_mul_log_norm {s : ℂ} (hs : 2 ≤ ‖s‖) :
    1 ≤ ‖s‖ * Real.log ‖s‖ := by
  have hlog2 : (1:ℝ) ≤ 2 * Real.log 2 := by
    have h : Real.log 2 ≥ 1/2 := by
      have := Real.add_one_le_exp (1/2 : ℝ)
      have hx : Real.exp (1/2) ≤ 2 := by
        have h2 : Real.exp (1/2) * Real.exp (1/2) ≤ 2 * 2 := by
          rw [← Real.exp_add]; norm_num
          exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))
        nlinarith [Real.exp_pos (1/2 : ℝ)]
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num),
                (Real.le_log_iff_exp_le two_pos).mpr hx]
    linarith
  calc (1:ℝ) ≤ 2 * Real.log 2 := hlog2
    _ ≤ ‖s‖ * Real.log ‖s‖ :=
        mul_le_mul hs (Real.log_le_log two_pos hs)
          (Real.log_nonneg one_le_two) (by linarith)

-- pin: kwDyf2_xiStripBound_proved (S_NumberField_exists_completedDedekindZeta_package.lean:6862)
theorem xiStripBound_holds : xiStripBound := by
  have _em := Classical.em
  intro K _ _
  refine ⟨Real.log (xiBound K) + 2, fun s hre1 hre2 hs => ?_⟩
  have hAK1 : 1 ≤ xiBound K := one_le_xiBound K
  have hAKpos : 0 < xiBound K := lt_of_lt_of_le one_pos hAK1
  have hlogA : 0 ≤ Real.log (xiBound K) := Real.log_nonneg hAK1
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hAs2 : 1 ≤ xiBound K * ‖s‖^2 := by nlinarith
  have hlogAs2 : 0 ≤ Real.log (xiBound K * ‖s‖^2) := Real.log_nonneg hAs2
  have hbnd : ‖xi K s‖ ≤ xiBound K * ‖s‖^2 :=
    norm_xi_le_xiBound_mul_sq K hre1 hre2 hs

  have hstep1 : Real.log ‖xi K s‖ ≤ Real.log (xiBound K * ‖s‖^2) := by
    rcases eq_or_lt_of_le (norm_nonneg (xi K s)) with h0 | h0
    · rw [← h0, Real.log_zero]; exact hlogAs2
    · exact Real.log_le_log h0 hbnd

  have hsplit : Real.log (xiBound K * ‖s‖^2)
      = Real.log (xiBound K) + 2 * Real.log ‖s‖ := by
    rw [Real.log_mul hAKpos.ne' (by positivity), Real.log_pow]; ring
  have hnl := one_le_norm_mul_log_norm hs
  have hlogs : Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
    nlinarith [Real.log_nonneg (le_trans one_le_two hs)]
  calc Real.log ‖xi K s‖
      ≤ Real.log (xiBound K) + 2 * Real.log ‖s‖ := by
        rw [← hsplit]; exact hstep1
    _ ≤ Real.log (xiBound K) * (‖s‖ * Real.log ‖s‖)
          + 2 * (‖s‖ * Real.log ‖s‖) := by
        gcongr
        calc Real.log (xiBound K)
            = Real.log (xiBound K) * 1 := (mul_one _).symm
          _ ≤ Real.log (xiBound K) * (‖s‖ * Real.log ‖s‖) :=
              mul_le_mul_of_nonneg_left hnl hlogA
    _ = (Real.log (xiBound K) + 2) * ‖s‖ * Real.log ‖s‖ := by ring

-- pin: kwDyf2_B1_of_C1a (S_NumberField_exists_completedDedekindZeta_package.lean:6900)
theorem xiOrderOneHadamard_of_xiRightHalfBound (hC1a : xiRightHalfBound) :
    xiOrderOneHadamard :=
  xiOrderOneHadamard_of_xiOrderBound (xiOrderBound_of_rightHalfBound_stripBound hC1a xiStripBound_holds)


end

end NumberField.CompletedDedekindZeta
