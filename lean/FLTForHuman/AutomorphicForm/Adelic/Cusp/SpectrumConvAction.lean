/-
  Right convolution on the cuspidal subcarrier.

  Right convolution by a factorisable test function `f` is an operator on automorphic functions
  (`rightConv`), and this module makes it one on the cuspidal carrier:

  * `exists_norm_toCarrier_rightConv_le`: a **norm bound** — there is `0 ≤ C` with
    `‖toCarrier (rightConv φ g)‖ ≤ C ‖toCarrier φ‖` for every `φ` in the continuous member submodule.
    Both `rightConv` memberships (`rightConv φ g` is again a member, and square-integrable) are
    produced, not assumed; the bound is the pairing calculation of the two adjointness rows.
  * `rightConv_mem_cuspMemberSubmodule`: convolution of a cusp member by a factorisable `f` is again a
    cusp member — `IsCuspidalFn` and `IsKfSmooth` for the convolution, plus the member submodule's
    three conjuncts.
  * `apply_mem_cuspSubcarrier_of_isLift_rightConv`: a bounded operator `T` that lifts `φ ↦ rightConv φ f`
    on the carrier maps the cuspidal subcarrier into itself.
  * `map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv`: if `f` is bi-invariant under the
    level-`N` subgroup `(fdPins F Φ₀).U N`, that image lands in the **level-`N`** subcarrier.

  Transcribed from the pin's four `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv.lean`

  Each of the four is a single declaration in the pin (no prelude).

  **Wiring.** `spec/check_port.py` owns the four public declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumPairing
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumSubrep
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.RightConvAdjoint
import FLTForHuman.AutomorphicForm.Adelic.RightConvPreservation
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace ENNReal ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

theorem exists_norm_toCarrier_rightConv_le
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ),
        ∃ hφg : rightConv F φ g ∈ memberSubmodule F Φ₀ ξ,
          ‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ≤ C * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ := by
  classical
  have hSC : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hHaar : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  set Wr : AdelicGL2 (𝓞 F) F → ℝ :=
    fun x => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) with hWr
  have hw_cont : Continuous fun y : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hrpow : ∀ p : ℝ, Continuous fun y : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ p :=
    fun p => hw_cont.rpow_const fun y => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hWr_cont : Continuous Wr := hrpow (-σ)
  have hWr_nonneg : ∀ x, 0 ≤ Wr x := fun x =>
    Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _

  have hres : μ.restrict Φ₀ = (μ.restrict (detNormSlab F α β)).restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet,
      Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μ.restrict Φ₀), x ∈ Φ₀ := by
    rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet
  set M : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hM
  have hbound : ∀ x ∈ Φ₀, Wr x ≤ M := by
    intro x hx
    obtain ⟨h1, h2⟩ := hΦ₀.subset hx
    rcases le_or_gt 0 (-σ) with hs | hs
    · exact (Real.rpow_le_rpow (hΦ₀.pos.le.trans h1) h2 hs).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hΦ₀.pos h1 hs.le).trans (le_max_left _ _)

  have hQint : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, MemLp ψ 2 (μ.restrict Φ₀) →
      Integrable (fun x => ‖ψ x‖ ^ 2 * Wr x) (μ.restrict Φ₀) := by
    intro ψ hψ
    have h2 : Integrable (fun x => ‖ψ x‖ ^ 2) (μ.restrict Φ₀) :=
      (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ
    refine h2.mul_bdd hWr_cont.aestronglyMeasurable (c := M) ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_of_nonneg (hWr_nonneg x)]
    exact hbound x hx

  set N1 : ℝ := ∫ y, ‖g y‖ ∂μ with hN1
  set N2 : ℝ := ∫ y, ‖g y‖ *
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ ∂μ with hN2
  have hN1_nonneg : 0 ≤ N1 := integral_nonneg fun _ => norm_nonneg _
  have hN2_nonneg : 0 ≤ N2 := integral_nonneg fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _)
  have hg1_int : Integrable (fun y => ‖g y‖) μ := (hg.norm).integrable_of_hasCompactSupport hgc.norm
  have hg2_int : Integrable (fun y => ‖g y‖ *
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ) μ :=
    ((hg.norm).mul (hrpow σ)).integrable_of_hasCompactSupport hgc.norm.mul_right
  refine ⟨Real.sqrt (N1 * N2), Real.sqrt_nonneg _, fun φ hφ => ?_⟩

  obtain ⟨hφlx, hφ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
  have hφc : Continuous φ := hφ.2
  have hA := AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀
    hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ hφlx hφlx hφc hφc hφ2 hφ2 g hg hgc
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ g) := by
    refine ⟨fun γ x => ?_, fun z x => ?_⟩
    · rw [← rightConv_comp_mul_left]
      simp_rw [hφlx.left_invariant γ]
    · rw [← rightConv_comp_mul_left]
      simp_rw [hφlx.central_transform z]
      simp only [rightConv_apply, mul_assoc]
      exact integral_const_mul _ _
  have hφg : rightConv F φ g ∈ memberSubmodule F Φ₀ ξ :=
    (mem_memberSubmodule_iff' F Φ₀ ξ _).mpr ⟨hlsxi, hA.1⟩
  refine ⟨hφg, ?_⟩

  have normsq : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ memberSubmodule F Φ₀ ξ),
      ‖toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩‖ ^ 2 = ∫ x in Φ₀, ‖ψ x‖ ^ 2 * Wr x ∂μ := by
    intro ψ hψ
    rw [← @inner_self_eq_norm_sq ℂ, MeasureTheory.L2.inner_def]
    have hae_a : (toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] ψ :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ hψ)
    have h1 : ∫ x, ⟪(toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ : AdelicGL2 (𝓞 F) F → ℂ) x,
          (toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ : AdelicGL2 (𝓞 F) F → ℂ) x⟫_ℂ
          ∂(weightedMeasure F Φ₀ σ) = ∫ x, ((‖ψ x‖ ^ 2 : ℝ) : ℂ) ∂(weightedMeasure F Φ₀ σ) := by
      apply integral_congr_ae
      filter_upwards [hae_a] with x hxa
      rw [hxa, RCLike.inner_apply, RCLike.mul_conj]
      norm_cast
    rw [h1]
    unfold weightedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul]
    · rw [← integral_re]
      · refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show RCLike.re ((ENNReal.ofReal (weight F σ x)).toReal •
          ((‖ψ x‖ ^ 2 : ℝ) : ℂ)) = ‖ψ x‖ ^ 2 * Wr x
        rw [weight_def, ENNReal.toReal_ofReal (hWr_nonneg x), Complex.real_smul,
          ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re, mul_comm]
      ·
        have hψ2 := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mp hψ).2
        have := (hQint ψ hψ2).ofReal (𝕜 := ℂ)
        refine (this.congr (ae_of_all _ fun x => ?_))
        show ((‖ψ x‖ ^ 2 * Wr x : ℝ) : ℂ) =
          (ENNReal.ofReal (weight F σ x)).toReal • ((‖ψ x‖ ^ 2 : ℝ) : ℂ)
        rw [weight_def, ENNReal.toReal_ofReal (hWr_nonneg x), Complex.real_smul]
        push_cast
        ring
    · exact (hWr_cont.measurable).ennreal_ofReal
    · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

  have htrans : ∀ y : AdelicGL2 (𝓞 F) F, MemLp (fun x => φ (x * y)) 2 (μ.restrict Φ₀) ∧
      ∫ x in Φ₀, ‖φ (x * y)‖ ^ 2 * Wr x ∂μ =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ *
          ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ := by
    intro y
    have hT1 := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos
      Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ hφlx hφlx hφc hφc hφ2 hφ2 y
    have hv_lx : IsLsXiFunction (𝓞 F) F ⊤ ξ (fun x => φ (x * y)) :=
      ⟨fun γ x => by simp only [mul_assoc]; exact hφlx.left_invariant γ (x * y),
       fun z x => by simp only [mul_assoc]; exact hφlx.central_transform z (x * y)⟩
    have hvc : Continuous (fun x => φ (x * y)) := hφc.comp (continuous_id.mul continuous_const)
    have hT2 := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos
      Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ (fun x => φ (x * y)) hφlx hv_lx hφc hvc
      hφ2 hT1.1 y
    refine ⟨hT1.1, ?_⟩
    have h3 := hT2.2.2
    simp only [inv_mul_cancel_right, RCLike.mul_conj] at h3
    rw [← hμ] at h3
    have h3' : ∫ x in Φ₀, ((‖φ (x * y)‖ : ℝ) : ℂ) ^ 2 *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂μ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
          ∫ x in Φ₀, ((‖φ x‖ : ℝ) : ℂ) ^ 2 *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
            ∂μ := h3
    have hcast : ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, ((∫ x in Φ₀, ‖θ x‖ ^ 2 * Wr x ∂μ : ℝ) : ℂ) =
        ∫ x in Φ₀, ((‖θ x‖ : ℝ) : ℂ) ^ 2 *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ := by
      intro θ
      refine (integral_ofReal (𝕜 := ℂ) (f := fun x => ‖θ x‖ ^ 2 * Wr x)).symm.trans ?_
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (((‖θ x‖ ^ 2 * Wr x : ℝ)) : ℂ) = ((‖θ x‖ : ℝ) : ℂ) ^ 2 *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
      push_cast
      rfl
    have hl := hcast (fun x => φ (x * y))
    have hr := hcast φ
    beta_reduce at hl
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, hl, hr]
    exact h3'

  have hJint : ∀ x, Integrable (fun y => ‖φ (x * y)‖ ^ 2 * ‖g y‖) μ := fun x =>
    (((hφc.comp (continuous_const.mul continuous_id)).norm.pow 2).mul hg.norm).integrable_of_hasCompactSupport
      hgc.norm.mul_left
  have hJ_nonneg : ∀ x, 0 ≤ ∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ := fun x =>
    integral_nonneg fun y => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (norm_nonneg _)
  have hpt : ∀ x, ‖rightConv F φ g x‖ ^ 2 ≤ N1 * ∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ := by
    intro x

    have hsg : Continuous fun y => Real.sqrt ‖g y‖ := Real.continuous_sqrt.comp hg.norm
    have hsg_supp : HasCompactSupport fun y => Real.sqrt ‖g y‖ :=
      hgc.norm.comp_left (g := Real.sqrt) Real.sqrt_zero
    have hf1 : Continuous fun y => ‖φ (x * y)‖ * Real.sqrt ‖g y‖ :=
      (hφc.comp (continuous_const.mul continuous_id)).norm.mul hsg
    have hf1_supp : HasCompactSupport fun y => ‖φ (x * y)‖ * Real.sqrt ‖g y‖ := hsg_supp.mul_left
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
      (ae_of_all _ fun y => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (ae_of_all _ fun y => Real.sqrt_nonneg _)
      (by simpa using hf1.memLp_of_hasCompactSupport (μ := μ) (p := 2) hf1_supp)
      (by simpa using hsg.memLp_of_hasCompactSupport (μ := μ) (p := 2) hsg_supp)
    have hprod : ∀ y, (‖φ (x * y)‖ * Real.sqrt ‖g y‖) * Real.sqrt ‖g y‖ = ‖φ (x * y)‖ * ‖g y‖ :=
      fun y => by rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have hsq1 : ∀ y, (‖φ (x * y)‖ * Real.sqrt ‖g y‖) ^ (2 : ℝ) = ‖φ (x * y)‖ ^ 2 * ‖g y‖ := fun y => by
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt (norm_nonneg _)]
    have hsq2 : ∀ y, (Real.sqrt ‖g y‖) ^ (2 : ℝ) = ‖g y‖ := fun y => by
      rw [Real.rpow_two, Real.sq_sqrt (norm_nonneg _)]
    simp only [hprod, hsq1, hsq2] at hCS
    have hle1 : ‖rightConv F φ g x‖ ≤ ∫ y, ‖φ (x * y)‖ * ‖g y‖ ∂μ := by
      rw [rightConv_apply]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1; funext y; rw [norm_mul]
    have hle2 : ‖rightConv F φ g x‖ ≤
        (∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ) ^ (1 / (2 : ℝ)) * N1 ^ (1 / (2 : ℝ)) :=
      hle1.trans hCS
    have h0 : 0 ≤ ‖rightConv F φ g x‖ := norm_nonneg _
    calc ‖rightConv F φ g x‖ ^ 2
        ≤ ((∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ) ^ (1 / (2 : ℝ)) * N1 ^ (1 / (2 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ h0 hle2 2
      _ = N1 * ∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
            ← Real.rpow_mul (hJ_nonneg x), ← Real.rpow_mul hN1_nonneg]
          norm_num
          ring

  have hmeasF : Measurable fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      ENNReal.ofReal (‖φ (p.1 * p.2)‖ ^ 2 * ‖g p.2‖ * Wr p.1) := by
    refine (Continuous.measurable ?_).ennreal_ofReal
    exact (((hφc.comp continuous_mul).norm.pow 2).mul (hg.comp continuous_snd).norm).mul
      (hWr_cont.comp continuous_fst)
  have hkey : ENNReal.ofReal (∫ x in Φ₀, ‖rightConv F φ g x‖ ^ 2 * Wr x ∂μ) ≤
      ENNReal.ofReal (N1 * N2 * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hQint _ hA.1)
      (ae_of_all _ fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (hWr_nonneg x))]
    calc ∫⁻ x in Φ₀, ENNReal.ofReal (‖rightConv F φ g x‖ ^ 2 * Wr x) ∂μ
        ≤ ∫⁻ x in Φ₀, ENNReal.ofReal (N1 * (∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ) * Wr x) ∂μ :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hpt x) (hWr_nonneg x))
      _ = ∫⁻ x in Φ₀, ENNReal.ofReal N1 *
            ∫⁻ y, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * ‖g y‖ * Wr x) ∂μ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [mul_assoc, ENNReal.ofReal_mul hN1_nonneg, ← integral_mul_const,
            ofReal_integral_eq_lintegral_ofReal ((hJint x).mul_const _)
              (ae_of_all _ fun y => mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) 2)
                (norm_nonneg _)) (hWr_nonneg x))]
      _ = ENNReal.ofReal N1 * ∫⁻ x in Φ₀,
            ∫⁻ y, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * ‖g y‖ * Wr x) ∂μ ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal N1 * ∫⁻ y,
            ∫⁻ x in Φ₀, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * ‖g y‖ * Wr x) ∂μ ∂μ := by
          rw [lintegral_lintegral_swap hmeasF.aemeasurable]
      _ = ENNReal.ofReal N1 * ∫⁻ y, ENNReal.ofReal ‖g y‖ *
            ∫⁻ x in Φ₀, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * Wr x) ∂μ ∂μ := by
          congr 1
          refine lintegral_congr fun y => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (norm_nonneg _)]
          congr 1; ring
      _ = ENNReal.ofReal N1 * ∫⁻ y, ENNReal.ofReal ‖g y‖ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ *
              ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ) ∂μ := by
          congr 1
          refine lintegral_congr fun y => ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hQint _ (htrans y).1)
            (ae_of_all _ fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (hWr_nonneg x)),
            (htrans y).2]
      _ = ENNReal.ofReal N1 * ((∫⁻ y, ENNReal.ofReal (‖g y‖ *
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ) ∂μ) *
            ENNReal.ofReal (∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ)) := by
          congr 1
          rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le σ),
            ENNReal.ofReal_mul (norm_nonneg (g y)), mul_assoc]
      _ = ENNReal.ofReal (N1 * N2 * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hg2_int
            (ae_of_all _ fun y => mul_nonneg (norm_nonneg _)
              (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _)),
            ← ENNReal.ofReal_mul hN2_nonneg, ← ENNReal.ofReal_mul hN1_nonneg, mul_assoc]

  have hQφ_nonneg : 0 ≤ ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ :=
    integral_nonneg fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (hWr_nonneg x)
  have hreal : ∫ x in Φ₀, ‖rightConv F φ g x‖ ^ 2 * Wr x ∂μ ≤
      N1 * N2 * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hN1_nonneg hN2_nonneg) hQφ_nonneg)).mp hkey
  rw [← normsq _ hφg, ← normsq φ hφ.1] at hreal
  have h1 : ‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ =
      Real.sqrt (‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1]
  calc Real.sqrt (‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ^ 2)
      ≤ Real.sqrt (N1 * N2 * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ ^ 2) := Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (N1 * N2) * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ := by
        rw [Real.sqrt_mul (mul_nonneg hN1_nonneg hN2_nonneg), Real.sqrt_sq (norm_nonneg _)]

theorem rightConv_mem_cuspMemberSubmodule
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := by
  obtain ⟨⟨⟨hmemb, hcusp⟩, hKf⟩, hcont⟩ := hφ
  obtain ⟨hLs, hL2⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hmemb
  obtain ⟨hleft, hcentral⟩ := hLs
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  have hRC : ∀ g, rightConv F φ f g = ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
    fun g => rfl

  have hcont' : Continuous (rightConv F φ f) :=
    AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F φ hcont f hfc hfcs

  have hLs' : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ f) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · rw [hRC, hRC]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show φ (globalPoints (𝓞 F) F γ * g * x) * f x = φ (g * x) * f x
      rw [mul_assoc, hleft]
    · rw [hRC, hRC, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g * x) * f x =
        ((ξ z : ℂˣ) : ℂ) * (φ (g * x) * f x)
      rw [mul_assoc, hcentral, mul_assoc]

  have hL2' : MemLp (rightConv F φ f) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    by_cases h0 : φ = 0
    · subst h0
      have : rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) f = 0 := by
        funext g
        rw [hRC]
        simp
      rw [this]
      exact MemLp.zero
    · obtain ⟨σ, hσ⟩ :=
        AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F Φ₀ ξ
          φ hmemb hcont h0
      exact (AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀
        hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ ⟨hleft, hcentral⟩ ⟨hleft, hcentral⟩
        hcont hcont hL2 hL2 f hfc hfcs).1
  have hmemb' : IsAutomorphicFnAt F (fdPins F Φ₀) ξ (rightConv F φ f) :=
    (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ _).mpr ⟨hLs', hL2'⟩

  have hcusp' := AutomorphicForm.isCuspidalFn_rightConv F Φ₀
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) φ
    hcont hcusp f hf
  have hKf' := AutomorphicForm.isKfSmooth_rightConv F φ f hf
  exact ⟨⟨⟨hmemb', hcusp'⟩, hKf'⟩, hcont'⟩

theorem apply_mem_cuspSubcarrier_of_isLift_rightConv
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T)
    (v : Carrier F Φ₀ σ) (hv : v ∈ cuspSubcarrier F hΦ₀ σ ξ) :
    T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
  have _ := hσ
  set M : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hM
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = M.topologicalClosure := rfl

  have hmaps : Set.MapsTo T (M : Set (Carrier F Φ₀ σ)) (M : Set (Carrier F Φ₀ σ)) := by
    rintro w ⟨ψ, hψ, rfl⟩

    have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
    have hcont : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ'.2⟩
    have hcomm := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hmt := hT.mapsTo (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont

    have hcusp : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ :=
      rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf _ hψ'
    have heta : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hcont.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ :=
      Subtype.coe_eta ψ hcont.1
    rw [heta] at hcomm
    refine ⟨⟨rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f, hmt.1⟩, hcusp, ?_⟩
    exact hcomm.symm

  have hv' : v ∈ closure (M : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe, ← hcl]; exact hv
  have := map_mem_closure T.continuous hv' hmaps
  rw [← Submodule.topologicalClosure_coe, ← hcl] at this
  exact this

theorem map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, f (u * x) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T) :
    Submodule.map (T : Carrier F Φ₀ σ →ₗ[ℂ] Carrier F Φ₀ σ) (cuspSubcarrier F hΦ₀ σ ξ) ≤
      cuspLevelSubcarrier F hΦ₀ σ ξ N := by
  set M : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hM
  set MN : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
        (cuspMemberSubmodule F Φ₀ ξ ⊓
          CuspidalConstituent.levelInvariantSubmodule F (fdPins F Φ₀) N)) with hMN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = M.topologicalClosure := rfl
  have hclN : cuspLevelSubcarrier F hΦ₀ σ ξ N = MN.topologicalClosure := rfl

  have hmaps : Set.MapsTo T (M : Set (Carrier F Φ₀ σ)) (MN : Set (Carrier F Φ₀ σ)) := by
    rintro w ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
    have hcont : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ'.2⟩
    have hcomm := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hmt := hT.mapsTo (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hcusp : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ :=
      rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf _ hψ'
    have hlev : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈
        CuspidalConstituent.levelInvariantSubmodule F (fdPins F Φ₀) N := by
      intro g u hu
      rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
      have hfu : (fun y => f (u⁻¹ * y)) = f := funext fun y => hfU y u⁻¹ (Subgroup.inv_mem _ hu)
      rw [hfu]
    have heta : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hcont.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ :=
      Subtype.coe_eta ψ hcont.1
    rw [heta] at hcomm
    refine ⟨⟨rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f, hmt.1⟩, ⟨hcusp, hlev⟩, ?_⟩
    exact hcomm.symm

  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  have hv' : v ∈ closure (M : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe, ← hcl]; exact hv
  have := map_mem_closure T.continuous hv' hmaps
  rw [← Submodule.topologicalClosure_coe, ← hclN] at this
  exact this

end CuspidalSpectrum

end AutomorphicForm
