/-
  The Mellin transform of the theta kernel, the place parametrisation of the cone,
  the archimedean Gamma factors, and the partial Dedekind zeta function.

  This is wave 5 of the `completedDedekindZeta` package.  It lands the Mellin
  integral `∫ τ in Ioi 0, τ ^ (β - 1) * exp (-(a τ))` as `a ^ (-β) * Γ β` and the
  matching identities for Deligne's archimedean factors `Gammaℝ` and `Gammaℂ`; the
  cone parameter `placeParam p w = p.1 * unitPart K p.2 w` together with its product
  formula `∏ w, placeParam K (t, u) w ^ w.mult = t ^ nK K`; the measure-preserving
  parametrisation of the cone (`mkParam_measurePreserving`,
  `lintegral_comp_halflog`, `setLIntegral_mkParam_halflog`) and the Jacobian
  computation (`fderiv_sq`, `hasFDerivAt_sq`, `abs_det_fderiv_sq`,
  `setLIntegral_sq_pos`) that turns the `placeParam` measure into the cone measure
  (`setLIntegral_placeParam`, `placeParam_measure_eq`, `setIntegral_placeParam`);
  the product of Gamma factors `prod_gammaFactor_eq`; and the orbit picture of the
  nonzero elements of a fractional ideal: the quotient
  `nonzeroIdeal K I / (𝓞 K)ˣ`, the induced ideal `orbitToIdeal`, the partial
  Dedekind zeta function `partialDedekindZeta` and the reindexing
  `lintegral_master_reindex` that unfolds the theta integral in wave 6.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:3149–4300`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the first part of the pin's `FLT.Gapsw80T8MellinGammaPartialZeta` block.  The
  pin's obligation prefixes and per-obligation namespaces are dropped; every
  declaration carries the pin's own name and line in the `-- pin:` comment above it
  (playbook §2.3, §4).

  The pin's file-wide `set_option maxHeartbeats 6400000` is not transcribed; the
  port's global cap is `4000000`.  Proofs are adapted to mathlib `v4.34.0`.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.ThetaKernel
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

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
open Asymptotics Filter Set
open scoped Classical
open scoped RealInnerProductSpace
open scoped nonZeroDivisors
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

-- pin: gapsw80_t8_mellin_expNeg_eq_Gamma (S_NumberField_exists_completedDedekindZeta_package.lean:3194)
theorem mellin_expNeg_eq_Gamma {a : ℝ} (ha : 0 < a) {β : ℂ} (hβ : 0 < β.re) :
    ∫ τ in Set.Ioi (0:ℝ), (τ : ℂ) ^ (β - 1) * cexp (-(a * τ : ℝ))
      = ((a : ℝ) : ℂ) ^ (-β) * Complex.Gamma β := by

  have hm := mellin_comp_mul_left (E := ℂ) (fun t ↦ cexp (-(t:ℝ))) β ha
  simp only [mellin, smul_eq_mul] at hm
  calc ∫ τ in Set.Ioi (0:ℝ), (τ : ℂ) ^ (β - 1) * cexp (-(a * τ : ℝ))
      = ((a:ℝ):ℂ) ^ (-β) * ∫ τ in Set.Ioi (0:ℝ), (τ:ℂ) ^ (β-1) * cexp (-(τ:ℝ)) := hm
    _ = ((a:ℝ):ℂ) ^ (-β) * Complex.Gamma β := by
        rw [Complex.Gamma_eq_integral hβ, Complex.GammaIntegral]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        simp only [Complex.ofReal_exp, Complex.ofReal_neg, mul_comm]

-- pin: gapsw80_t8_gammaFactor_isReal (S_NumberField_exists_completedDedekindZeta_package.lean:3208)
theorem gammaFactor_isReal {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((π * a : ℝ) : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)
      = Gammaℝ s * ((a:ℝ):ℂ) ^ (-(s/2)) := by
  rw [Gammaℝ_def, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg ha.le, neg_div]
  ring

-- pin: gapsw80_t8_gammaℂ_norm_const (S_NumberField_exists_completedDedekindZeta_package.lean:3215)
theorem gammaℂ_norm_const (s : ℂ) :
    (2:ℂ) * ((2 * π : ℝ) : ℂ) ^ (-s) * (2:ℂ) ^ (s - 1) = ((π:ℝ):ℂ) ^ (-s) := by
  have h2ne : ((2:ℝ):ℂ) ≠ 0 := by norm_num
  rw [show ((2*π:ℝ):ℂ) = ((2:ℝ):ℂ) * ((π:ℝ):ℂ) from by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_nonneg,
    show (2:ℂ) = ((2:ℝ):ℂ) from by norm_num]
  calc ((2:ℝ):ℂ) * (((2:ℝ):ℂ)^(-s) * ((π:ℝ):ℂ)^(-s)) * ((2:ℝ):ℂ)^(s-1)
      = (((2:ℝ):ℂ)^(s-1) * ((2:ℝ):ℂ)^(-s) * ((2:ℝ):ℂ)) * ((π:ℝ):ℂ)^(-s) := by ring
    _ = ((2:ℝ):ℂ)^(s-1 + -s) * ((2:ℝ):ℂ) * ((π:ℝ):ℂ)^(-s) := by
        rw [Complex.cpow_add _ _ h2ne]
    _ = ((π:ℝ):ℂ)^(-s) := by
        rw [show s - 1 + -s = (-1:ℂ) from by ring, Complex.cpow_neg_one,
          inv_mul_cancel₀ h2ne, one_mul]

-- pin: gapsw80_t8_gammaFactor_isComplex (S_NumberField_exists_completedDedekindZeta_package.lean:3229)
theorem gammaFactor_isComplex {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((π * a : ℝ) : ℂ) ^ (-s) * Complex.Gamma s
      = Gammaℂ s * (2:ℂ) ^ (s - 1) * ((a:ℝ):ℂ) ^ (-s) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg ha.le,
    Gammaℂ_def]
  calc ((π:ℝ):ℂ)^(-s) * ((a:ℝ):ℂ)^(-s) * Complex.Gamma s
      = ((2:ℂ) * ((2*π:ℝ):ℂ)^(-s) * (2:ℂ)^(s-1)) * ((a:ℝ):ℂ)^(-s) * Complex.Gamma s := by
        rw [gammaℂ_norm_const]
    _ = 2 * (2 * (π:ℂ))^(-s) * Complex.Gamma s * (2:ℂ)^(s-1) * ((a:ℝ):ℂ)^(-s) := by
        rw [show ((2*π:ℝ):ℂ) = 2 * (π:ℂ) from by push_cast; ring]; ring

-- pin: gapsw80_t8_ofReal_pow_cpow (S_NumberField_exists_completedDedekindZeta_package.lean:3240)
theorem ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (z : ℂ) :
    (((a : ℝ) : ℂ) ^ n) ^ z = ((a : ℝ) : ℂ) ^ ((n : ℂ) * z) := by
  have harg : (n : ℝ) * Complex.arg ((a:ℝ):ℂ) = 0 := by
    rw [Complex.arg_ofReal_of_nonneg ha, mul_zero]
  exact (Complex.cpow_nat_mul' (x := ((a:ℝ):ℂ)) (n := n)
    (harg ▸ neg_lt_zero.mpr Real.pi_pos) (harg ▸ Real.pi_nonneg) z).symm

-- pin: gapsw80_t8_ofReal_sqrt_cpow (S_NumberField_exists_completedDedekindZeta_package.lean:3247)
theorem ofReal_sqrt_cpow {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    ((Real.sqrt a : ℝ) : ℂ) ^ z = ((a : ℝ) : ℂ) ^ (z / 2) := by
  have key := ofReal_pow_cpow (Real.sqrt_nonneg a) 2 (z / 2)
  rw [show (((Real.sqrt a : ℝ):ℂ))^(2:ℕ) = ((a:ℝ):ℂ) by
        rw [← Complex.ofReal_pow, Real.sq_sqrt ha],
      show ((2:ℕ):ℂ) * (z/2) = z by push_cast; ring] at key
  exact key.symm

-- pin: gapsw80_t8_prod_ofReal_cpow (S_NumberField_exists_completedDedekindZeta_package.lean:3255)
theorem prod_ofReal_cpow {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (z : ℂ) :
    ((∏ i ∈ s, a i : ℝ) : ℂ) ^ z = ∏ i ∈ s, ((a i : ℝ) : ℂ) ^ z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha j (Finset.mem_cons_self j s))
        (Finset.prod_nonneg fun i hi => ha i (Finset.mem_cons_of_mem hi)),
      ih (fun i hi => ha i (Finset.mem_cons_of_mem hi))]

-- pin: gapsw80_t8_placeParam (S_NumberField_exists_completedDedekindZeta_package.lean:3266)
noncomputable def placeParam (p : ℝ × logSpace K) : realSpace K :=
  fun w ↦ p.1 * unitPart K p.2 w

-- pin: gapsw80_t8_placeParam_pos (S_NumberField_exists_completedDedekindZeta_package.lean:3269)
theorem placeParam_pos {p : ℝ × logSpace K} (hp : 0 < p.1) (w : InfinitePlace K) :
    0 < placeParam K p w :=
  mul_pos hp (unitPart_pos K p.2 w)

-- pin: gapsw80_t8_prod_placeParam_pow_mult (S_NumberField_exists_completedDedekindZeta_package.lean:3273)
theorem prod_placeParam_pow_mult {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ∏ w : InfinitePlace K, placeParam K (t, u) w ^ w.mult = t ^ nK K := by
  have key : ∀ w, placeParam K (t, u) w
      = yParam K (mkParam K (Real.log t / 2) u) w := fun w => by
    rw [yParam_mkParam_factor K ht u w]; rfl
  simp_rw [key]
  exact (prod_yParam_mkParam K _ u).trans (exp_half_log_pow_two_n K ht)

-- pin: gapsw80_t8_mkParam_measurePreserving (S_NumberField_exists_completedDedekindZeta_package.lean:3281)
theorem mkParam_measurePreserving :
    MeasurePreserving (fun p : ℝ × logSpace K => mkParam K p.1 p.2)
      volume volume := by

  have heq : (fun p : ℝ × logSpace K => mkParam K p.1 p.2)
      = ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).symm
        ∘ Prod.map
          ⇑(MeasurableEquiv.piUnique (fun _ : {w : InfinitePlace K // w = w₀} => ℝ)).symm
          id := by
    funext p; funext w
    unfold mkParam
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
      MeasurableEquiv.piUnique_symm_apply]
    by_cases hw : w = w₀
    · subst hw; simp only [dite_eq_left]; rfl
    · simp only [dite_eq_right hw]
  rw [heq, Measure.volume_eq_prod ℝ (logSpace K)]
  refine (volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).symm.comp ?_
  have hp := (volume_preserving_piUnique (fun _ : {w : InfinitePlace K // w = w₀} => ℝ)).symm.prod
    (MeasurePreserving.id (volume : Measure (logSpace K)))
  convert hp
  simp only [Measure.volume_eq_prod]
  congr!

-- pin: gapsw80_t8_lintegral_comp_halflog (S_NumberField_exists_completedDedekindZeta_package.lean:3308)
theorem lintegral_comp_halflog {h : ℝ → ENNReal} (hh : Measurable h) :
    ∫⁻ r, h r = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * t)⁻¹ * h (Real.log t / 2) := by
  have := hh
  have himg : (fun t : ℝ => Real.log t / 2) '' Set.Ioi (0:ℝ) = Set.univ :=
    Set.eq_univ_of_forall fun r => ⟨Real.exp (2 * r), Real.exp_pos _, by
      show Real.log (Real.exp (2 * r)) / 2 = r; rw [Real.log_exp]; ring⟩
  have hinj : Set.InjOn (fun t : ℝ => Real.log t / 2) (Set.Ioi 0) := fun t₁ h₁ t₂ h₂ heq => by
    have hlog : Real.log t₁ = Real.log t₂ := by linarith [heq]
    exact (Real.exp_log h₁).symm.trans (hlog ▸ Real.exp_log h₂)
  have hder : ∀ t ∈ Set.Ioi (0:ℝ), HasFDerivWithinAt (fun t => Real.log t / 2)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * t)⁻¹) (Set.Ioi 0) t := fun t ht => by
    have : HasDerivAt (fun t => Real.log t / 2) (2 * t)⁻¹ t := by
      rw [mul_inv, mul_comm, ← div_eq_mul_inv]
      exact (Real.hasDerivAt_log (ne_of_gt ht)).div_const 2
    exact this.hasFDerivAt.hasFDerivWithinAt
  conv_lhs => rw [← setLIntegral_univ, ← himg]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_Ioi hder hinj h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  congr 2
  simp_rw [ContinuousLinearMap.det, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
    abs_of_pos (inv_pos.mpr (mul_pos two_pos ht'))]

-- pin: gapsw80_t8_setLIntegral_mkParam_halflog (S_NumberField_exists_completedDedekindZeta_package.lean:3331)
theorem setLIntegral_mkParam_halflog {G : realSpace K → ENNReal}
    (hG : Measurable G) :
    ∫⁻ c, G c
      = ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
          ENNReal.ofReal (2 * p.1)⁻¹ * G (mkParam K (Real.log p.1 / 2) p.2) := by

  have hGm : Measurable (fun p : ℝ × logSpace K => G (mkParam K p.1 p.2)) :=
    hG.comp (mkParam_measurePreserving K).measurable
  have hGm' : Measurable (fun p : ℝ × logSpace K =>
      ENNReal.ofReal (2 * p.1)⁻¹ * G (mkParam K (Real.log p.1 / 2) p.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_fst).inv).mul
      (hGm.comp (((Real.measurable_log.comp measurable_fst).div_const 2).prodMk measurable_snd))
  have hh : Measurable (fun r : ℝ => ∫⁻ u : logSpace K, G (mkParam K r u)) :=
    hGm.lintegral_prod_right'
  rw [← (mkParam_measurePreserving K).lintegral_comp hG, Measure.volume_eq_prod,
    lintegral_prod _ hGm.aemeasurable, setLIntegral_prod _ hGm'.aemeasurable]
  dsimp only
  rw [lintegral_comp_halflog hh]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [setLIntegral_univ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

-- pin: gapsw80_t8_expMapBasis_image_univ (S_NumberField_exists_completedDedekindZeta_package.lean:3352)
theorem expMapBasis_image_univ :
    expMapBasis '' (Set.univ : Set (realSpace K)) = {τ : realSpace K | ∀ w, 0 < τ w} := by
  ext τ
  refine ⟨fun ⟨c, _, hc⟩ w => hc ▸ expMapBasis_pos c w, fun hτ => ?_⟩

  exact ⟨expMapBasis.symm τ, Set.mem_univ _, expMapBasis.right_inv (Set.mem_univ_pi.mpr hτ)⟩

-- pin: gapsw80_t8_fderiv_sq (S_NumberField_exists_completedDedekindZeta_package.lean:3359)
abbrev fderiv_sq (σ : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * σ w)).comp (.proj w)

-- pin: gapsw80_t8_hasFDerivAt_sq (S_NumberField_exists_completedDedekindZeta_package.lean:3362)
theorem hasFDerivAt_sq (σ : realSpace K) :
    HasFDerivAt (fun σ' : realSpace K => fun w => σ' w ^ 2) (fderiv_sq K σ) σ := by
  simp only [hasFDerivAt_pi', ContinuousLinearMap.proj_pi]
  intro w
  have hd : HasDerivAt (fun x : ℝ => x ^ 2) (2 * σ w) (σ w) := by
    simpa using hasDerivAt_pow 2 (σ w)
  exact hd.hasFDerivAt.comp (f := fun σ' : realSpace K => σ' w) σ (hasFDerivAt_apply w σ)

open _root_.ContinuousLinearMap in
-- pin: gapsw80_t8_abs_det_fderiv_sq (S_NumberField_exists_completedDedekindZeta_package.lean:3371)
theorem abs_det_fderiv_sq (σ : realSpace K) :
    |(fderiv_sq K σ).det|
      = 2 ^ (nrRealPlaces K + nrComplexPlaces K) * ∏ w : InfinitePlace K, |σ w| := by
  simp only [fderiv_sq, ContinuousLinearMap.det, coe_pi]
  erw [LinearMap.det_pi]
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, smulRight_apply,
    one_apply_eq_self, one_smul, Finset.abs_prod, abs_mul, abs_pow, abs_two,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_eq_nrRealPlaces_add_nrComplexPlaces]

-- pin: gapsw80_t8_setLIntegral_sq_pos (S_NumberField_exists_completedDedekindZeta_package.lean:3381)
theorem setLIntegral_sq_pos {g : realSpace K → ENNReal} (hg : Measurable g) :
    ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w}, g τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K) *
        ∫⁻ σ in {σ : realSpace K | ∀ w, 0 < σ w},
          (∏ w : InfinitePlace K, ENNReal.ofReal (σ w)) * g (fun w => σ w ^ 2) := by
  have := hg
  set P : Set (realSpace K) := {σ | ∀ w, 0 < σ w}
  have hPmeas : MeasurableSet P := by
    rw [show P = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from Set.ext fun σ => by
      simp [P]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have himg : (fun σ : realSpace K => fun w => σ w ^ 2) '' P = P := by
    refine Set.ext fun τ => ⟨fun ⟨σ, hσ, hστ⟩ w => hστ ▸ pow_pos (hσ w) 2, fun hτ => ?_⟩
    exact ⟨fun w => Real.sqrt (τ w), fun w => Real.sqrt_pos.mpr (hτ w),
      funext fun w => Real.sq_sqrt (hτ w).le⟩
  have hinj : Set.InjOn (fun σ : realSpace K => fun w => σ w ^ 2) P :=
    fun σ₁ h₁ σ₂ h₂ heq => funext fun w =>
      (pow_left_inj₀ (h₁ w).le (h₂ w).le two_ne_zero).mp (congrFun heq w)
  conv_lhs => rw [show P = (fun σ : realSpace K => fun w => σ w ^ 2) '' P from himg.symm]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hPmeas
      (fun σ _ => (hasFDerivAt_sq K σ).hasFDerivWithinAt) hinj g,
    ← lintegral_const_mul' _ _ (by finiteness)]
  refine setLIntegral_congr_fun hPmeas fun σ hσ => ?_
  rw [abs_det_fderiv_sq, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
    ENNReal.ofReal_prod_of_nonneg fun w _ => abs_nonneg _,
    show (∏ w, ENNReal.ofReal |σ w|) = ∏ w, ENNReal.ofReal (σ w) from
      Finset.prod_congr rfl fun w _ => by rw [abs_of_pos (hσ w)],
    mul_assoc]

-- pin: gapsw80_t8_setLIntegral_placeParam (S_NumberField_exists_completedDedekindZeta_package.lean:3411)
theorem setLIntegral_placeParam {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (placeParam K p)
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ *
        ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ := by

  have hmeB : Measurable (fun c : realSpace K => expMapBasis c) :=
    (continuous_expMapBasis K).measurable
  have hmsq : Measurable (fun σ : realSpace K => fun w => σ w ^ 2) :=
    Measurable.of_eval fun w => (measurable_pi_apply w).pow_const 2

  set H : realSpace K → ENNReal := fun c =>
    ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) with hHdef
  have hH : Measurable H :=
    (ENNReal.measurable_ofReal.comp
        ((Real.measurable_exp.comp (measurable_pi_apply w₀)).pow_const _)).mul (hf.comp (hmsq.comp hmeB))

  have stepL : ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (placeParam K p)
      = (2 : ENNReal) * ∫⁻ c, H c := by
    rw [setLIntegral_mkParam_halflog K hH,
      ← lintegral_const_mul' _ _ (by finiteness)]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
    have ht : (0:ℝ) < p.1 := hp.1
    have hcw : mkParam K (Real.log p.1 / 2) p.2 w₀ = Real.log p.1 / 2 := mkParam_w₀ K _ _
    have hplace : (fun w => (expMapBasis (mkParam K (Real.log p.1 / 2) p.2) w) ^ 2)
        = placeParam K p := funext fun w =>
      yParam_mkParam_factor K ht p.2 w
    have hn : 1 ≤ nK K := Module.finrank_pos
    simp only [hHdef, hcw, hplace, exp_half_log_pow_two_n K ht]
    rw [show (2:ENNReal) = ENNReal.ofReal (2:ℝ) from by simp, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity),
      show (2:ℝ) * (2 * p.1)⁻¹ * p.1 ^ nK K = p.1 ^ (nK K - 1) by
        rw [show p.1 ^ nK K = p.1 * p.1 ^ (nK K - 1) by
          conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']]
        field_simp]

  have stepR : ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2 : ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
        * ∫⁻ c, H c := by
    have hf' : Measurable (fun τ : realSpace K =>
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ) :=
      (Finset.measurable_prod _ fun w _ =>
        ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)).mul hf
    have hσ : Measurable (fun σ : realSpace K =>
        (∏ w, ENNReal.ofReal (σ w)) *
          ((∏ w : {w // IsComplex w}, ENNReal.ofReal (σ w.1 ^ 2)) * f (fun w => σ w ^ 2))) :=
      (Finset.measurable_prod _ fun w _ =>
          ENNReal.measurable_ofReal.comp (measurable_pi_apply w)).mul (hf'.comp hmsq)
    rw [setLIntegral_sq_pos K hf', ← expMapBasis_image_univ K,
      setLIntegral_expMapBasis_image MeasurableSet.univ hσ, setLIntegral_univ, ← mul_assoc]
    congr 1
    refine lintegral_congr fun c => ?_

    have heBpos : ∀ w, (0:ℝ) < expMapBasis c w := fun w => expMapBasis_pos c w
    have hPc0 : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr (heBpos w.1)).ne'
    have hPcT : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ ⊤ :=
      (ENNReal.prod_lt_top fun w _ => ENNReal.ofReal_lt_top).ne

    have hPaPc : (∏ w, ENNReal.ofReal (expMapBasis c w))
          * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
        = ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w).le),
        ← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w.1).le),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (heBpos w).le),
        prod_eq_prod_mul_prod (fun w => expMapBasis c w), mul_assoc, ← sq,
        ← prod_expMapBasis_pow c, prod_eq_prod_mul_prod (fun w => expMapBasis c w ^ w.mult)]
      congr 2
      · exact Finset.prod_congr rfl fun w _ => by rw [mult_isReal w, pow_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun w _ => by rw [mult_isComplex w]

    simp only [hHdef, show (fun w => c w) = c from rfl]
    rw [show (c w₀) * (Module.finrank ℚ K : ℝ) = (nK K : ℝ) * c w₀ from mul_comm _ _,
      Real.exp_nat_mul,
      show (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1 ^ 2))
          = (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) from by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun w _ => by rw [sq, ENNReal.ofReal_mul (heBpos w.1).le],
      show Real.exp (c w₀) ^ (2 * nK K)
          = Real.exp (c w₀) ^ nK K * Real.exp (c w₀) ^ nK K from by rw [two_mul, pow_add],
      ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) _)]

    rw [← mul_assoc _ _ (f _), ← mul_assoc (∏ w, ENNReal.ofReal (expMapBasis c w)),
      ← mul_assoc, ← mul_assoc]
    congr 1

    calc ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
            * ((∏ w, ENNReal.ofReal (expMapBasis c w))
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
        = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * ((∏ w, ENNReal.ofReal (expMapBasis c w))
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
            * ((∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))) := by ring
      _ = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
          rw [hPaPc, ENNReal.inv_mul_cancel hPc0 hPcT, mul_one]

  rw [stepL, stepR, ← mul_assoc]
  congr 1
  have hR : (0:ℝ) < regulator K := regulator_pos K
  have hn : 0 < nK K := Module.finrank_pos
  have hX : (0:ℝ) < (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K :=
    mul_pos (mul_pos (zpow_pos two_pos _) (Nat.cast_pos.mpr hn)) hR
  have h2X : (2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)
      = (2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K := by
    have key : (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * 2 = (2:ℝ) ^ nrRealPlaces K := by
      rw [← zpow_add_one₀ (two_ne_zero (α := ℝ)), sub_add_cancel, zpow_natCast]
    rw [← key]; ring
  have hB : (2:ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
      = ENNReal.ofReal ((2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast,
      show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
      pow_add, mul_assoc ((2:ENNReal) ^ nrRealPlaces K),
      show (2:ENNReal) ^ nrComplexPlaces K * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K
            * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
          = (nK K : ENNReal) * ENNReal.ofReal (regulator K)
            * ((2:ENNReal) * (2:ENNReal)⁻¹) ^ nrComplexPlaces K from by rw [mul_pow]; ring,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, mul_one, ← mul_assoc]
  rw [hB, ← h2X, ← ENNReal.ofReal_mul (inv_nonneg.mpr hX.le),
    show ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)⁻¹
          * ((2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K))
        = (2:ℝ) from by field_simp,
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp]

-- pin: gapsw80_t8_continuous_placeParam (S_NumberField_exists_completedDedekindZeta_package.lean:3547)
theorem continuous_placeParam :
    Continuous (placeParam K) :=
  continuous_pi fun w => continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)

-- pin: gapsw80_t8_placeParam_measure_eq (S_NumberField_exists_completedDedekindZeta_package.lean:3551)
theorem placeParam_measure_eq :
    Measure.map (placeParam K)
        ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
          (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹
        • (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}).withDensity
            (fun τ => ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) := by
  have hφ : Measurable (placeParam K) := (continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hgL : Measurable fun p => f (placeParam K p) := hf.comp hφ
  rw [lintegral_map hf hφ, lintegral_withDensity_eq_lintegral_mul _ hdL hgL,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hdR hf, smul_eq_mul]
  simp only [Pi.mul_apply]
  exact setLIntegral_placeParam K hf

-- pin: gapsw80_t8_setIntegral_placeParam (S_NumberField_exists_completedDedekindZeta_package.lean:3571)
theorem setIntegral_placeParam {G : realSpace K → ℂ}
    (hG : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w})) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (placeParam K p)
      = (((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ) *
        ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ := by
  have hC : (0:ℝ) ≤ ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg
      (mul_nonneg (zpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (regulator_pos K).le)
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} := by
    rw [show {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from
      Set.ext fun τ => by simp]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hφ : Measurable (placeParam K) := (continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)

  have hGmap : AEStronglyMeasurable G (Measure.map (placeParam K)
      ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))) := by
    rw [placeParam_measure_eq]
    exact .mono_ac
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)) hG

  have key := (integral_map hφ.aemeasurable hGmap).symm
  rw [placeParam_measure_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hdR
      (Filter.Eventually.of_forall fun _ => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hdL
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal hC, Complex.real_smul] at key

  have stepL : (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (placeParam K p))
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        (ENNReal.ofReal (p.1 ^ (nK K - 1))).toReal • G (placeParam K p) :=
    setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => by
      rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hp.1) _), Complex.real_smul]
  have stepR : (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)).toReal • G τ)
      = ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ :=
    setIntegral_congr_fun hBmeas fun τ hτ => by
      rw [ENNReal.toReal_prod,
        show (∏ w : {w : InfinitePlace K // IsComplex w}, (ENNReal.ofReal (τ w.1)).toReal)
            = ∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 from
          Finset.prod_congr rfl fun w _ => ENNReal.toReal_ofReal (le_of_lt (hτ w.1)),
        Complex.real_smul]
  rw [stepL, key, stepR, Complex.ofReal_inv]

-- pin: gapsw80_t8_prod_gammaFactor_eq (S_NumberField_exists_completedDedekindZeta_package.lean:3625)
theorem prod_gammaFactor_eq {s : ℂ} (hs : 1 < s.re) {x : mixedSpace K}
    (hx : ∀ w, normAtPlace w x ≠ 0) :
    ∏ w : InfinitePlace K,
        (((π * normAtPlace w x ^ 2 : ℝ) : ℂ) ^ (-(w.mult * s / 2)) * Complex.Gamma (w.mult * s / 2))
      = Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ) ^ (s - 1)) ^ nrComplexPlaces K
        * ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s)) := by
  have := hs
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    (normAtPlace_nonneg w x).lt_of_ne (Ne.symm (hx w))

  have hreal : ∀ w : {w : InfinitePlace K // IsReal w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = Gammaℝ s * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isReal w, Nat.cast_one, one_mul]
    rw [gammaFactor_isReal (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      ofReal_pow_cpow (hpos w.1).le 2 (-(s/2)),
      show ((2:ℕ):ℂ) * -(s/2) = -s from by push_cast; ring]

  have hcplx : ∀ w : {w : InfinitePlace K // IsComplex w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = (Gammaℂ s * (2:ℂ)^(s-1)) * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isComplex w, Nat.cast_ofNat]
    rw [show ((2:ℂ) * s / 2) = s from by ring,
      gammaFactor_isComplex (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      ofReal_pow_cpow (hpos w.1).le 2 (-s),
      show ((2:ℕ):ℂ) * -s = -((2:ℂ)*s) from by push_cast; ring, mul_assoc]
  rw [prod_eq_prod_mul_prod (K := K), prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((normAtPlace w x:ℝ):ℂ) ^ (-((w.mult:ℂ) * s)))]
  simp only [hreal, hcplx, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    nrRealPlaces, nrComplexPlaces]
  ring

-- pin: gapsw80_t8_prod_normAtPlace_cpow (S_NumberField_exists_completedDedekindZeta_package.lean:3658)
theorem prod_normAtPlace_cpow {x : mixedSpace K} (hx : ∀ w, normAtPlace w x ≠ 0)
    (s : ℂ) :
    ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s))
      = ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-s) := by
  have := hx
  rw [mixedEmbedding.norm_apply,
    prod_ofReal_cpow Finset.univ
      (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) (-s)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_pow,
    ofReal_pow_cpow (normAtPlace_nonneg w x) w.mult (-s)]
  congr 1; ring

-- pin: gapsw80_t8_nonzeroIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:3670)
abbrev nonzeroIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type :=
  {a : K // a ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ∧ a ≠ 0}

scoped instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MulAction (𝓞 K)ˣ (nonzeroIdeal K I) where
  smul u x := ⟨(u : 𝓞 K) • (x : K),
    Submodule.smul_mem _ _ x.2.1,
    smul_ne_zero (by exact_mod_cast u.ne_zero) x.2.2⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul u v x := Subtype.ext (mul_smul _ _ _)

-- pin: gapsw80_t8_orbitRepr (S_NumberField_exists_completedDedekindZeta_package.lean:3681)
noncomputable def orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I))) : K :=
  (x.out : K)

-- pin: gapsw80_t8_partialDedekindZeta (S_NumberField_exists_completedDedekindZeta_package.lean:3685)
noncomputable def partialDedekindZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ∑' J : {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = C},
    ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)

-- pin: gapsw80_t8_spanSingleton_mul_inv_le_one (S_NumberField_exists_completedDedekindZeta_package.lean:3689)
theorem spanSingleton_mul_inv_le_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : nonzeroIdeal K I) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * (↑I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * ↑I⁻¹
      ≤ (↑I : FractionalIdeal (𝓞 K)⁰ K) * ↑I⁻¹ :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr x.2.1) _
    _ = 1 := I.mul_inv

-- pin: gapsw80_t8_orbitToIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:3697)
noncomputable def orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : nonzeroIdeal K I) : (Ideal (𝓞 K))⁰ :=
  ⟨(FractionalIdeal.le_one_iff_exists_coeIdeal.mp
      (spanSingleton_mul_inv_le_one K I x)).choose,
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h ↦
      (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.2.2) (Units.ne_zero I⁻¹))
        ((FractionalIdeal.le_one_iff_exists_coeIdeal.mp
            (spanSingleton_mul_inv_le_one K I x)).choose_spec.symm.trans
          (by rw [show (0 : Ideal (𝓞 K)) = ⊥ from rfl] at h
              rw [h, FractionalIdeal.coeIdeal_bot]))⟩

-- pin: gapsw80_t8_coe_orbitToIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:3708)
theorem coe_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : nonzeroIdeal K I) :
    ((orbitToIdeal K I x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * ↑I⁻¹ :=
  (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (spanSingleton_mul_inv_le_one K I x)).choose_spec

-- pin: gapsw80_t8_mk0_orbitToIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:3715)
theorem mk0_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : nonzeroIdeal K I) :
    ClassGroup.mk0 (orbitToIdeal K I x) = (ClassGroup.mk K I)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ClassGroup.mk_mk0 K, ← map_mul, ClassGroup.mk_eq_one_iff]
  refine ⟨⟨(x : K), ?_⟩⟩
  rw [show ((FractionalIdeal.mk0 K (orbitToIdeal K I x) * I :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) from by
    rw [Units.val_mul, FractionalIdeal.coe_mk0, coe_orbitToIdeal,
      mul_assoc, I.inv_mul, mul_one],
    FractionalIdeal.coe_spanSingleton]

-- pin: gapsw80_t8_absNorm_orbitToIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:3727)
theorem absNorm_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : nonzeroIdeal K I) :
    (Ideal.absNorm (orbitToIdeal K I x : Ideal (𝓞 K)) : ℚ)
      * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
      = |Algebra.norm ℚ (x : K)| := by
  have hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun h ↦ (Units.ne_zero I) (FractionalIdeal.absNorm_eq_zero_iff.mp h)
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K), coe_orbitToIdeal, map_mul,
    FractionalIdeal.absNorm_span_singleton, Units.val_inv_eq_inv_val, map_inv₀,
    inv_mul_cancel_right₀ hI]

-- pin: gapsw80_t8_orbitToIdeal_smul (S_NumberField_exists_completedDedekindZeta_package.lean:3738)
theorem orbitToIdeal_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : (𝓞 K)ˣ) (x : nonzeroIdeal K I) :
    orbitToIdeal K I (u • x) = orbitToIdeal K I x := by
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u • x : nonzeroIdeal K I) : K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
    show FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) • (x : K)) = _
    rw [Algebra.smul_def, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top, one_mul]
  exact Subtype.ext <| FractionalIdeal.coeIdeal_injective (K := K) <|
    show ((orbitToIdeal K I (u • x) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((orbitToIdeal K I x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) from by
      rw [coe_orbitToIdeal, coe_orbitToIdeal, hspan]

-- pin: gapsw80_t8_orbitQuotEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:3752)
noncomputable def orbitQuotEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)) ≃
      {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = (ClassGroup.mk K I)⁻¹} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨orbitToIdeal K I x, mk0_orbitToIdeal K I x⟩)
      (fun a b h ↦ Subtype.ext <| by
        obtain ⟨u, rfl⟩ := MulAction.orbitRel_apply.mp h
        exact orbitToIdeal_smul K I u b))
    ⟨fun q₁ q₂ h ↦ by
      induction q₁ using Quotient.inductionOn with | _ a => ?_
      induction q₂ using Quotient.inductionOn with | _ b => ?_
      refine Quotient.sound (MulAction.orbitRel_apply.mpr ?_)
      have hab : orbitToIdeal K I a = orbitToIdeal K I b :=
        congrArg Subtype.val h
      have hc : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) := by
        have := congrArg
          (fun J : (Ideal (𝓞 K))⁰ ↦ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I) hab
        simpa only [coe_orbitToIdeal, mul_assoc, I.inv_mul, mul_one] using this
      obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hc
      refine ⟨u⁻¹, Subtype.ext (show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (b : K) = (a : K) from ?_)⟩
      have hu' : ((u : (𝓞 K)ˣ) : 𝓞 K) • (a : K) = (b : K) := hu
      rw [← hu', ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul],
    fun ⟨J, hJ⟩ ↦ by
      have hJI : ClassGroup.mk K (FractionalIdeal.mk0 K J * I) = 1 := by
        rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
      obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).mp
        (ClassGroup.mk_eq_one_iff.mp hJI)
      have hx0 : x ≠ 0 := fun h0 ↦ Units.ne_zero _
        (hx.trans (by rw [h0, FractionalIdeal.spanSingleton_zero]))
      replace hx : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
        rw [← hx, Units.val_mul, FractionalIdeal.coe_mk0]
      have hxI : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
        FractionalIdeal.spanSingleton_le_iff_mem.mp <|
          calc FractionalIdeal.spanSingleton (𝓞 K)⁰ x
              = ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I := hx.symm
            _ ≤ 1 * ↑I := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
            _ = ↑I := one_mul _
      refine ⟨Quotient.mk _ ⟨x, hxI, hx0⟩, Subtype.ext (Subtype.ext
        (FractionalIdeal.coeIdeal_injective (K := K)
          (show ((orbitToIdeal K I ⟨x, hxI, hx0⟩ : Ideal (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K) = ↑↑J from ?_)))⟩
      rw [coe_orbitToIdeal, ← hx, mul_assoc, I.mul_inv, mul_one]⟩

-- pin: gapsw80_t8_tsum_orbit_normInv_eq (S_NumberField_exists_completedDedekindZeta_package.lean:3798)
theorem tsum_orbit_normInv_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)),
      ((|(Algebra.norm ℚ (orbitRepr K I x) : ℚ)| : ℝ) : ℂ) ^ (-s))
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
        * partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by
  have := hs
  rw [partialDedekindZeta, ← (orbitQuotEquiv K I).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun q ↦ ?_
  unfold orbitRepr
  have hout : ((orbitQuotEquiv K I q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = orbitToIdeal K I q.out := by
    conv_lhs => rw [← q.out_eq]
    rfl
  have hM : (0:ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have hN : (0:ℝ) ≤ (Ideal.absNorm (orbitToIdeal K I q.out : Ideal (𝓞 K)) : ℝ) :=
    Nat.cast_nonneg _
  rw [hout, ← Complex.ofReal_natCast (Ideal.absNorm _),
    ← Complex.mul_cpow_ofReal_nonneg hM hN]
  congr 2
  exact_mod_cast ((absNorm_orbitToIdeal K I q.out).symm.trans (mul_comm _ _))

-- pin: gapsw80_t8_covol_discr_cpow (S_NumberField_exists_completedDedekindZeta_package.lean:3820)
theorem covol_discr_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
      * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
    = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
      * ((2:ℝ) : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
  have hN : (0:ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2i : (0:ℝ) ≤ (2:ℝ)⁻¹ := by norm_num
  have h2r : (0:ℝ) ≤ ((2:ℝ)⁻¹) ^ nrComplexPlaces K := pow_nonneg h2i _
  have hD : (0:ℝ) ≤ |(discr K : ℝ)| := abs_nonneg _
  have hDne : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, abs_eq_zero, Int.cast_eq_zero]
    exact discr_ne_zero K
  have harg2 : Complex.arg ((2:ℝ):ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.pi_ne_zero.symm

  rw [mixedEmbedding.covolume_idealLattice, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg hN h2r) (Real.sqrt_nonneg _),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hN h2r,
    Complex.ofReal_pow, ofReal_pow_cpow h2i (nrComplexPlaces K) (-s),
    ofReal_sqrt_cpow hD (-s),
    show (((2:ℝ)⁻¹ : ℝ) : ℂ) = (((2:ℝ):ℂ))⁻¹ from Complex.ofReal_inv 2,
    Complex.inv_cpow _ _ harg2, ← Complex.cpow_neg,
    show -((nrComplexPlaces K : ℂ) * -s) = (nrComplexPlaces K : ℂ) * s from by ring,
    mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hDne,
    show -s / 2 + s / 2 = (0:ℂ) from by ring, Complex.cpow_zero, mul_one]

-- pin: gapsw80_t8_nonzeroIdealLatticeEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:3848)
noncomputable def nonzeroIdealEquivNonzeroLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    nonzeroIdeal K I
      ≃ {x : mixedEmbedding.idealLattice K I // (x : mixedSpace K) ≠ 0} where
  toFun a := ⟨⟨mixedEmbedding K (a : K),
      (mem_idealLattice K I).mpr ⟨(a : K), a.2.1, rfl⟩⟩,
    fun h => a.2.2 <| (mixedEmbedding_injective K) (h.trans (_root_.map_zero _).symm)⟩
  invFun x := ⟨((mem_idealLattice K I).mp x.1.2).choose,
    ((mem_idealLattice K I).mp x.1.2).choose_spec.1,
    fun ha => x.2 (by
      have := ((mem_idealLattice K I).mp x.1.2).choose_spec.2
      rw [ha, _root_.map_zero] at this; exact this.symm)⟩
  left_inv a := by
    apply Subtype.ext
    have hch := ((mem_idealLattice K I).mp
      ((mem_idealLattice K I).mpr ⟨(a : K), a.2.1, rfl⟩)).choose_spec.2
    exact (mixedEmbedding_injective K) hch
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    exact ((mem_idealLattice K I).mp x.1.2).choose_spec.2

-- pin: gapsw80_t8_zEquivNonzero (S_NumberField_exists_completedDedekindZeta_package.lean:3868)
noncomputable def intVecEquivNonzeroLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {v : Fin (nK K) → ℤ // v ≠ 0}
      ≃ {x : mixedEmbedding.idealLattice K I // (x : mixedSpace K) ≠ 0} where
  toFun v := ⟨idealLatticeEquiv K I v, fun h => v.2 (by
    have : (idealLatticeEquiv K I v : mixedEmbedding.idealLattice K I) = 0 := Subtype.ext h
    simpa using (idealLatticeEquiv K I).injective (this.trans (_root_.map_zero _).symm))⟩
  invFun x := ⟨(idealLatticeEquiv K I).symm x,
    fun h => x.2 (by rw [← (idealLatticeEquiv K I).apply_symm_apply x.1, h, _root_.map_zero]; rfl)⟩
  left_inv v := Subtype.ext ((idealLatticeEquiv K I).symm_apply_apply v)
  right_inv x := Subtype.ext ((idealLatticeEquiv K I).apply_symm_apply x)

-- pin: gapsw80_t8_summable_thetaTerm (S_NumberField_exists_completedDedekindZeta_package.lean:3879)
theorem summable_thetaTerm_scaledGram (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun v : Fin (nK K) → ℤ =>
      cexp ((-(π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v)) : ℝ) : ℂ) := by
  obtain ⟨lam, hlam, hGram⟩ := idealGram_lower_bound K I

  obtain ⟨w₁, -, hw₁⟩ := Finset.exists_min_image
    (Finset.univ : Finset (InfinitePlace K)) y Finset.univ_nonempty
  set c := y w₁ with hc_def
  have hc : 0 < c := hy w₁
  have hcle : ∀ w, c ≤ y w := fun w => hw₁ w (Finset.mem_univ w)
  refine Summable.of_norm ?_
  refine (summable_dom_gaussian K (mul_pos hc hlam)).of_nonneg_of_le
    (fun v => norm_nonneg _) (fun v => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (intCastVec v ⬝ᵥ (idealGram K I) *ᵥ intCastVec v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hcle v) Real.pi_nonneg

-- pin: gapsw80_t8_multiIdealTheta_sub_one (S_NumberField_exists_completedDedekindZeta_package.lean:3903)
theorem multiIdealTheta_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    multiIdealTheta K I y - 1
      = ∑' a : nonzeroIdeal K I,
          cexp ((-(π * ∑ w : InfinitePlace K, y w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by

  set f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (intCastVec v ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec v)) : ℝ) : ℂ) with hf_def
  have hfsum : Summable f := summable_thetaTerm_scaledGram K I hy
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hTheta : multiIdealTheta K I y - 1
      = ∑' v : {v : Fin (nK K) → ℤ // v ≠ 0}, f v := by
    have heq : multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
    refine Eq.symm ((tsum_subtype {v : Fin (nK K) → ℤ | v ≠ 0} f).trans ?_)
    exact tsum_congr fun v => by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, ne_eq, ite_not]
  rw [hTheta]

  rw [← ((intVecEquivNonzeroLattice K I).trans
    (nonzeroIdealEquivNonzeroLattice K I).symm).tsum_eq]
  refine tsum_congr fun a => ?_

  have hcoe : ((idealLatticeEquiv K I) (a : Fin (nK K) → ℤ) : mixedSpace K)
      = mixedEmbedding K
          ((((intVecEquivNonzeroLattice K I).trans
              (nonzeroIdealEquivNonzeroLattice K I).symm) a : nonzeroIdeal K I) : K) := by
    have hch := ((mem_idealLattice K I).mp
      ((intVecEquivNonzeroLattice K I) a).1.2).choose_spec.2
    exact hch.symm
  have hsum : (intCastVec (a : Fin (nK K) → ℤ) ⬝ᵥ (scaledGram K I y) *ᵥ intCastVec (a : Fin (nK K) → ℤ))
      = ∑ w, y w * (w ((((intVecEquivNonzeroLattice K I).trans
          (nonzeroIdealEquivNonzeroLattice K I).symm) a : nonzeroIdeal K I) : K)) ^ 2 :=
    (quadForm_scaledGram K I y a).trans
      (Finset.sum_congr rfl fun w _ => by rw [hcoe, normAtPlace_apply])
  simp only [hf_def, hsum]

-- pin: gapsw80_t8_summable_rexpQ (S_NumberField_exists_completedDedekindZeta_package.lean:3941)
theorem summable_exp_neg_pi_placeParam (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : nonzeroIdeal K I =>
      Real.exp (-(π * ∑ w, y w * (w (a : K)) ^ 2)) := by
  have h : Summable fun a : nonzeroIdeal K I =>
      cexp ((-(π * ∑ w, y w * (w (a : K)) ^ 2) : ℝ) : ℂ) :=
    (Equiv.summable_iff ((intVecEquivNonzeroLattice K I).trans
        (nonzeroIdealEquivNonzeroLattice K I).symm)).mp
      (((summable_thetaTerm_scaledGram K I hy).subtype (fun v : Fin (nK K) → ℤ => v ≠ 0)).congr fun a => by
        simp only [Function.comp_apply]
        have hcoe : ((idealLatticeEquiv K I) (a : Fin (nK K) → ℤ) : mixedSpace K)
            = mixedEmbedding K
                ((((intVecEquivNonzeroLattice K I).trans
                    (nonzeroIdealEquivNonzeroLattice K I).symm) a :
                  nonzeroIdeal K I) : K) :=
          (((mem_idealLattice K I).mp
            ((intVecEquivNonzeroLattice K I) a).1.2).choose_spec.2).symm
        congr 4
        exact (quadForm_scaledGram K I y a).trans
          (Finset.sum_congr rfl fun w _ => by rw [hcoe, normAtPlace_apply]))
  exact h.norm.congr fun a => by rw [Complex.norm_exp, Complex.ofReal_re]

-- pin: gapsw80_t8_heckeKernel_sub_one (S_NumberField_exists_completedDedekindZeta_package.lean:3963)
theorem heckeKernel_sub_one_eq_integral (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    heckeKernel K I t - 1
      = ∫ u in unitBox K,
          (multiIdealTheta K I (placeParam K (t, u)) - 1) ∂volume := by
  have hvol : volume (unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hint1 : IntegrableOn
      (fun u => multiIdealTheta K I (placeParam K (t, u)))
      (unitBox K) volume := by
    have hcont : Continuous
        (fun u => multiIdealTheta K I (placeParam K (t, u))) := by
      have h := continuous_genericKernel_integrand K I (Real.log t / 2) 1 (fun _ => one_pos)
      simp only [one_mul] at h
      exact h.congr fun u => by
        congr 1; funext w; exact yParam_mkParam_factor K ht u w
    have hcompact : IsCompact
        (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hcont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set
      (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  rw [integral_sub hint1 hint2, setIntegral_const]
  have hvol' : volume.real (unitBox K) = 1 := by
    rw [measureReal_def, hvol, ENNReal.toReal_one]
  rw [hvol', one_smul]
  congr 1
  unfold heckeKernel
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w; rw [yParam_mkParam_factor K ht]; rfl

-- pin: gapsw80_t8_integrableOn_theta_sub_one (S_NumberField_exists_completedDedekindZeta_package.lean:3996)
theorem integrableOn_theta_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => multiIdealTheta K I (placeParam K (t, u)) - 1)
      (unitBox K) volume := by
  have hcont : Continuous
      (fun u => multiIdealTheta K I (placeParam K (t, u))) := by
    have h := continuous_genericKernel_integrand K I (Real.log t / 2) 1 (fun _ => one_pos)
    simp only [one_mul] at h
    exact h.congr fun u => by
      congr 1; funext w; exact yParam_mkParam_factor K ht u w
  have hcompact : IsCompact
      (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (((hcont.sub continuous_const).locallyIntegrable.integrableOn_isCompact hcompact).mono_set
    (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self))

-- pin: gapsw80_t8_placeParam_add_single (S_NumberField_exists_completedDedekindZeta_package.lean:4012)
theorem placeParam_add_single {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (w : InfinitePlace K) :
    placeParam K (t, u + Pi.single i 1) w
      = placeParam K (t, u) w
        * unitSqScale K (fundSystem K (equivFinRank.symm i)) w := by
  have key : ∀ v, placeParam K (t, v) w
      = yParam K (mkParam K (Real.log t / 2) v) w := fun v => by
    rw [yParam_mkParam_factor K ht v w]; rfl
  rw [key, key, mkParam_add_single, yParam_add_single K i.2, Pi.mul_apply, mul_comm]

-- pin: gapsw80_t8_quadForm_unit_smul (S_NumberField_exists_completedDedekindZeta_package.lean:4022)
theorem quadForm_unit_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℝ × logSpace K) (η : (𝓞 K)ˣ) (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K, placeParam K p w * (w ((η • a : nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K,
          placeParam K p w * unitSqScale K η w * (w (a : K)) ^ 2 := by
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcoe : ((η • a : nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
  rw [hcoe, Algebra.smul_def, map_mul, mul_pow, unitSqScale,
    show ((algebraMap (𝓞 K) K) (η : 𝓞 K) : K) = ((η : 𝓞 K) : K) from rfl]
  ring

-- pin: gapsw80_t8_quadForm_torsion_invariant (S_NumberField_exists_completedDedekindZeta_package.lean:4033)
theorem quadForm_torsion_invariant (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℝ × logSpace K) (ζ : torsion K) (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        placeParam K p w * (w (((ζ : (𝓞 K)ˣ) • a : nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, placeParam K p w * (w (a : K)) ^ 2 := by
  rw [quadForm_unit_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [unitSqScale, (mem_torsion K).mp ζ.2 w, one_pow, mul_one]

-- pin: gapsw80_t8_quadForm_shift_single (S_NumberField_exists_completedDedekindZeta_package.lean:4042)
theorem quadForm_shift_single (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) (u : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀})
    (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        placeParam K (t, u + Pi.single i 1) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          placeParam K (t, u) w
            * (w (((fundSystem K (equivFinRank.symm i)) • a : nonzeroIdeal K I) : K)) ^ 2 := by
  rw [quadForm_unit_smul]
  exact Finset.sum_congr rfl fun w _ => by rw [placeParam_add_single K ht]

-- pin: gapsw80_t8_dutEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:4053)
noncomputable def dirichletUnitEquiv : torsion K × (Fin (rank K) → ℤ) ≃ (𝓞 K)ˣ :=
  Equiv.ofBijective (fun p => (p.1 : (𝓞 K)ˣ) * ∏ i, fundSystem K i ^ p.2 i)
    (Function.bijective_iff_existsUnique _ |>.mpr fun x => by
      obtain ⟨ζe, he, huniq⟩ := exist_unique_eq_mul_prod K x
      exact ⟨ζe, he.symm, fun ζe' he' => huniq ζe' he'.symm⟩)

-- pin: gapsw80_t8_stabilizer_eq_bot (S_NumberField_exists_completedDedekindZeta_package.lean:4059)
theorem stabilizer_eq_bot (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : nonzeroIdeal K I) :
    MulAction.stabilizer (𝓞 K)ˣ a = ⊥ := by
  rw [eq_bot_iff]
  intro η hη
  have hstab : ((η • a : nonzeroIdeal K I) : K) = (a : K) :=
    Subtype.ext_iff.mp (MulAction.mem_stabilizer_iff.mp hη)
  have hcoe : algebraMap (𝓞 K) K (η : 𝓞 K) * (a : K) = (a : K) := by
    have hunf : ((η • a : nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
    rw [hunf, Algebra.smul_def] at hstab; exact hstab
  have hη1 : algebraMap (𝓞 K) K (η : 𝓞 K) = 1 := (mul_eq_right₀ a.2.2).mp hcoe
  have hη𝓞 : (η : 𝓞 K) = 1 :=
    (IsFractionRing.injective (𝓞 K) K) (hη1.trans (map_one _).symm)
  exact Subgroup.mem_bot.mpr (Units.ext (hη𝓞.trans Units.val_one.symm))

-- pin: gapsw80_t8_orbitGroupEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:4074)
noncomputable def orbitGroupEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I))) :
    (𝓞 K)ˣ ≃ MulAction.orbit (𝓞 K)ˣ ω.out :=
  ((MulAction.orbitEquivQuotientStabilizer (𝓞 K)ˣ ω.out).trans
    ((Subgroup.quotientEquivOfEq (stabilizer_eq_bot K I ω.out)).trans
      (QuotientGroup.quotientBot.toEquiv))).symm

-- pin: gapsw80_t8_orbitGroupEquiv_apply (S_NumberField_exists_completedDedekindZeta_package.lean:4081)
theorem orbitGroupEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)))
    (η : (𝓞 K)ˣ) :
    ((orbitGroupEquiv K I ω η : nonzeroIdeal K I) : K)
      = ((η • ω.out : nonzeroIdeal K I) : K) := by
  have h := MulAction.orbitEquivQuotientStabilizer_symm_apply (G := (𝓞 K)ˣ) ω.out η
  show ((((MulAction.orbitEquivQuotientStabilizer (𝓞 K)ˣ ω.out).trans
      ((Subgroup.quotientEquivOfEq (stabilizer_eq_bot K I ω.out)).trans
        QuotientGroup.quotientBot.toEquiv)).symm η : nonzeroIdeal K I) : K)
    = ((η • ω.out : nonzeroIdeal K I) : K)
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    show ((QuotientGroup.quotientBot (G := (𝓞 K)ˣ)).toEquiv.symm η : (𝓞 K)ˣ ⧸ (⊥ : Subgroup (𝓞 K)ˣ))
        = QuotientGroup.mk η from rfl,
    show ((Subgroup.quotientEquivOfEq (stabilizer_eq_bot K I ω.out)).symm
          (QuotientGroup.mk η) : (𝓞 K)ˣ ⧸ MulAction.stabilizer (𝓞 K)ˣ ω.out)
        = QuotientGroup.mk η from rfl]
  exact congrArg (fun x : nonzeroIdeal K I => (x : K)) h

-- pin: gapsw80_t8_orbitSigmaEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:4099)
noncomputable def orbitSigmaEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)), (𝓞 K)ˣ)
      ≃ nonzeroIdeal K I :=
  (Equiv.sigmaCongrRight fun ω => orbitGroupEquiv K I ω).trans
    (MulAction.selfEquivSigmaOrbits (𝓞 K)ˣ (nonzeroIdeal K I)).symm

-- pin: gapsw80_t8_orbitSigmaEquiv_apply (S_NumberField_exists_completedDedekindZeta_package.lean:4105)
theorem orbitSigmaEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)))
    (η : (𝓞 K)ˣ) :
    ((orbitSigmaEquiv K I ⟨ω, η⟩ : nonzeroIdeal K I) : K)
      = ((η • ω.out : nonzeroIdeal K I) : K) :=
  orbitGroupEquiv_apply K I ω η

-- pin: gapsw80_t8_spanEquiv (S_NumberField_exists_completedDedekindZeta_package.lean:4112)
noncomputable def spanEquiv :
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      ≃ ({w : InfinitePlace K // w ≠ w₀} → ℤ) where
  toFun g := fun i =>
    ((Basis.mem_span_iff_repr_mem ℤ _ _).mp g.2 i).choose
  invFun m := ⟨fun i => (m i : ℝ), by
    rw [Basis.mem_span_iff_repr_mem]
    exact fun i => ⟨m i, by simp⟩⟩
  left_inv g := by
    apply Subtype.ext; funext i
    have := ((Basis.mem_span_iff_repr_mem ℤ _ _).mp g.2 i).choose_spec
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
    exact this
  right_inv m := by
    funext i
    refine Int.cast_injective (α := ℝ) ?_
    have hmem : (fun j => (m j : ℝ))
        ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) := by
      rw [Basis.mem_span_iff_repr_mem]; exact fun j => ⟨m j, by simp⟩
    have := ((Basis.mem_span_iff_repr_mem ℤ _ _).mp hmem i).choose_spec
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
    exact this

-- pin: gapsw80_t8_spanEquiv_symm_apply_coe (S_NumberField_exists_completedDedekindZeta_package.lean:4135)
theorem spanEquiv_symm_apply_coe (m : {w : InfinitePlace K // w ≠ w₀} → ℤ)
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    ((spanEquiv K).symm m : logSpace K) i = (m i : ℝ) := rfl

-- pin: gapsw80_t8_quadForm_shift_span (S_NumberField_exists_completedDedekindZeta_package.lean:4139)
theorem quadForm_shift_span (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          placeParam K (t, u) w
            * (w (((∏ i, fundSystem K (equivFinRank.symm i) ^ (spanEquiv K g i))
                • a : nonzeroIdeal K I) : K)) ^ 2 := by
  set m := spanEquiv K g with hm_def
  have hg : (g : logSpace K) = ∑ i, (m i : ℝ) • Pi.single i (1:ℝ) := by
    have : g = (spanEquiv K).symm m := ((spanEquiv K).symm_apply_apply g).symm
    rw [this]
    funext j
    simp only [spanEquiv_symm_apply_coe, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hg]

  have hstep : ∀ (v : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ),
      ∀ (b : nonzeroIdeal K I),
      ∑ w, placeParam K (t, v + (k : ℝ) • Pi.single i 1) w * (w (b : K)) ^ 2
        = ∑ w, placeParam K (t, v) w
            * (w (((fundSystem K (equivFinRank.symm i) ^ k) • b : nonzeroIdeal K I)
                : K)) ^ 2 := by
    intro v i k
    induction k using Int.induction_on with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [show (((n:ℤ)+1:ℤ):ℝ) • Pi.single i (1:ℝ)
              = ((n:ℤ):ℝ) • Pi.single i 1 + Pi.single i 1 from by
            push_cast; rw [add_smul, one_smul],
        ← add_assoc, quadForm_shift_single K I ht,
        ih (fundSystem K (equivFinRank.symm i) • b), ← mul_smul, ← _root_.zpow_add_one,
        show ((n:ℤ)+1 : ℤ) = (((n:ℕ)+1:ℕ):ℤ) from by push_cast; ring]
    | pred n ih =>
      intro b
      have key := (quadForm_shift_single K I ht
        (v + ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i 1) i
        ((fundSystem K (equivFinRank.symm i))⁻¹ • b)).symm
      rw [← mul_smul, mul_inv_cancel, one_smul, add_assoc,
        show ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i (1:ℝ) + Pi.single i 1
            = ((-(n:ℤ):ℤ):ℝ) • Pi.single i 1 from by
          rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, sub_add_cancel]] at key
      rw [key, ih ((fundSystem K (equivFinRank.symm i))⁻¹ • b), ← mul_smul,
        show fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)) * (fundSystem K (equivFinRank.symm i))⁻¹
            = fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)-1) from by group]

  suffices ∀ (s : Finset {w : InfinitePlace K // w ≠ w₀}) (a' : nonzeroIdeal K I),
      ∑ w, placeParam K (t, u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) w
          * (w (a' : K)) ^ 2
        = ∑ w, placeParam K (t, u) w
            * (w (((∏ i ∈ s, fundSystem K (equivFinRank.symm i) ^ (m i)) • a'
                : nonzeroIdeal K I) : K)) ^ 2 from this Finset.univ a
  intro s
  induction s using Finset.induction with
  | empty => intro a'; simp
  | insert j s hj ih =>
    intro a'
    rw [Finset.sum_insert hj, add_comm ((m j : ℝ) • Pi.single j 1), ← add_assoc,
      hstep (u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) j (m j) a',
      ih ((fundSystem K (equivFinRank.symm j) ^ (m j)) • a'),
      Finset.prod_insert hj, mul_smul, smul_comm]

-- pin: gapsw80_t8_countable_nonzeroIdeal (S_NumberField_exists_completedDedekindZeta_package.lean:4205)
scoped instance countable_nonzeroIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Countable (nonzeroIdeal K I) :=
  ((nonzeroIdealEquivNonzeroLattice K I).trans
    (intVecEquivNonzeroLattice K I).symm).countable_iff.mpr Subtype.countable

local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun _ _ _ => measure_preimage_add _ _ _⟩

local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) :=
  (spanEquiv K).countable_iff.mpr inferInstance

noncomputable local instance instSpanProdAddAction : AddAction
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) where
  vadd g p := (p.1, g +ᵥ p.2)
  zero_vadd p := Prod.ext rfl (zero_vadd _ p.2)
  add_vadd g h p := Prod.ext rfl (add_vadd g h p.2)

local instance instSpanProdMeasurableConstVAdd : MeasurableConstVAdd
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) :=
  ⟨fun g => measurable_fst.prodMk ((measurable_const_vadd g).comp measurable_snd)⟩

local instance instSpanProdVAddInvariant : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) :=
  ⟨fun g _ hs =>
    ((MeasurePreserving.id _).prod (measurePreserving_vadd g volume)).measure_preimage
      hs.nullMeasurableSet⟩

-- pin: gapsw80_t8_continuous_cexpQ (S_NumberField_exists_completedDedekindZeta_package.lean:4238)
theorem continuous_cexp_placeParam (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finsetSum _ fun w _ => ?_)
  exact (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)).mul continuous_const

-- pin: gapsw80_t8_lintegral_master_reindex (S_NumberField_exists_completedDedekindZeta_package.lean:4246)
theorem lintegral_master_reindex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σre : ℝ) :
    ∑' a : nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, placeParam K p w * (w (a : K)) ^ 2)) * p.1 ^ (σre - 1))
      = (torsionOrder K : ENNReal) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)),
          ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            ENNReal.ofReal (Real.exp
                (-(π * ∑ w, placeParam K p w * (w (orbitRepr K I ω)) ^ 2))
              * p.1 ^ (σre - 1)) := by
  set GE : nonzeroIdeal K I → ℝ × logSpace K → ENNReal := fun a p =>
    ENNReal.ofReal (Real.exp (-(π * ∑ w, placeParam K p w * (w (a : K)) ^ 2))
      * p.1 ^ (σre - 1)) with hGE_def
  have hGE_orbitSigma : ∀ ω η p, GE (orbitSigmaEquiv K I ⟨ω, η⟩) p
      = GE (η • ω.out) p := fun ω η p => by unfold GE; congr 4

  rw [← (orbitSigmaEquiv K I).tsum_eq fun a =>
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), GE a p,
    ENNReal.tsum_sigma']
  refine (tsum_congr fun ω => ?_).trans ENNReal.tsum_mul_left

  have hstep6a : ∀ p' : torsion K × (Fin (rank K) → ℤ), ∀ p : ℝ × logSpace K,
      GE (orbitSigmaEquiv K I ⟨ω, dirichletUnitEquiv K p'⟩) p
        = GE ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p => by
    rw [hGE_orbitSigma,
      show dirichletUnitEquiv K p' • ω.out
          = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
        rw [← mul_smul]; rfl]
    unfold GE; congr 5
    exact quadForm_torsion_invariant K I p p'.1 _
  rw [← (dirichletUnitEquiv K).tsum_eq,
    tsum_congr fun p' => lintegral_congr fun p => hstep6a p' p]

  rw [ENNReal.tsum_prod']
  dsimp only
  rw [ENNReal.tsum_const,
    show (ENat.card (torsion K) : ENNReal) = (torsionOrder K : ENNReal) from by
      rw [ENat.card_eq_coe_natCard]; rfl]
  congr 1

  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (spanEquiv K).symm with hefr_def
  have hefr_prod : ∀ g,
      (∏ j, fundSystem K j ^ efr.symm g j)
        = ∏ i, fundSystem K (equivFinRank.symm i) ^ spanEquiv K g i := fun g => by
    have hefrs : ∀ j, efr.symm g j = spanEquiv K g (equivFinRank j) := fun j => by
      simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
        Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
        id_eq]
    exact Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
      fun j => by rw [hefrs j, Equiv.symm_apply_apply]
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [hefr_prod g]]

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σre - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σre - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a, Measurable (GE a) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)
  have hGE_slice_meas : ∀ a,
      Measurable fun t : ℝ => ∫⁻ u in unitBox K, GE a (t, u) ∂volume := fun a =>
    (hGE_meas a).lintegral_prod_right' (ν := volume.restrict (unitBox K))
  have hGE_repr : (fun p => ENNReal.ofReal (Real.exp
          (-(π * ∑ w, placeParam K p w * (w (orbitRepr K I ω)) ^ 2))
        * p.1 ^ (σre - 1))) = GE ω.out := rfl
  simp_rw [hGE_repr, Measure.volume_eq_prod (ℝ) (logSpace K),
    ← Measure.prod_restrict, lintegral_prod _ (hGE_meas _).aemeasurable, setLIntegral_univ]
  rw [← lintegral_tsum fun g => (hGE_slice_meas _).aemeasurable.restrict]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [(unitBox_isAddFundamentalDomain K).lintegral_eq_tsum''
    (fun u => GE ω.out (t, u))]
  exact tsum_congr fun g => setLIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => by
      unfold GE; congr 5
      rw [show (g +ᵥ u : logSpace K) = u + (g : logSpace K) from by
            rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
      exact (quadForm_shift_span K I ht u g ω.out).symm

end

end NumberField.CompletedDedekindZeta
