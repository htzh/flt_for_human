/-
  Unfolding the theta integral to the completed partial zeta function.

  This is wave 6 of the `completedDedekindZeta` package, and the analytic heart of
  the development.  It unfolds the orbit integral of the theta kernel: the
  Rankin--Selberg step `rankinSelberg_unfold` exchanges the `p`-integral with the
  `tsum` over the orbits of `nonzeroIdeal K I`, the per-orbit integral
  `perOrbit_integral_eq` evaluates that orbit integral as the archimedean Gamma
  factors times a norm power, and `heckeLambda_eq_completedPartialZeta` assembles
  the completed partial zeta function at `nK K * s / 2` out of
  `partialDedekindZeta`.  The `…_weighted` (`c`-weighted quadratic form) variants
  carry the same computation for the symmetric square, and
  `symmLambda_eq_completedPartialZeta` is the dual statement for the trace-dual
  ideal; `covolume_mul_covolume_traceDualIdeal` closes the covolume product.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:4301–5418`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the second part of the pin's `FLT.Gapsw80T8MellinGammaPartialZeta` block.  The
  pin's obligation prefixes and per-obligation namespaces are dropped; every
  declaration carries the pin's own name and line in the `-- pin:` comment above it
  (playbook §2.3, §4).

  The pin's file-wide `set_option maxHeartbeats 6400000` is not transcribed; the
  port's global cap is `4000000`.  Proofs are adapted to mathlib `v4.34.0`.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Mellin
import Mathlib.Algebra.Module.ZLattice.Basic
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

/-! ### The translation action of the unit lattice on `ℝ × logSpace K`

The pin declares these file-scoped instances once, immediately before the
declarations of this wave; the port's wave-5 module holds the copies its own
proofs need, so wave 6 carries its own. -/

local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun _ _ _ => measure_preimage_add _ _ _⟩

local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) :=
  (spanEquiv K).countable_iff.mpr inferInstance

noncomputable local instance instSpanProdAddAction' : AddAction
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) where
  vadd g p := (p.1, g +ᵥ p.2)
  zero_vadd p := Prod.ext rfl (zero_vadd _ p.2)
  add_vadd _g _h p := Prod.ext rfl (add_vadd _ _ p.2)

local instance instSpanProdMeasurableConstVAdd' : MeasurableConstVAdd
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) :=
  ⟨fun g => measurable_fst.prodMk ((measurable_const_vadd g).comp measurable_snd)⟩

local instance instSpanProdVAddInvariant' : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) :=
  ⟨fun g _ hs =>
    ((MeasurePreserving.id _).prod (measurePreserving_vadd g volume)).measure_preimage
      hs.nullMeasurableSet⟩

-- pin: gapsw80_t8_enorm_integrand_eq (S_NumberField_exists_completedDedekindZeta_package.lean:4333)
theorem enorm_integrand_eq (σ : ℂ) (x : K) {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  have hn : ‖cexp ((-(π * ∑ w, placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖
      = Real.exp (-(π * ∑ w, placeParam K p w * (w x) ^ 2))
        * p.1 ^ (σ.re - 1) := by
    rw [norm_mul, Complex.norm_exp, Complex.ofReal_re,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
      Complex.sub_re, Complex.one_re]
  rw [← hn, ← ofReal_norm]

-- pin: gapsw80_t8_master_finite (S_NumberField_exists_completedDedekindZeta_package.lean:4348)
theorem lintegral_master_ne_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((heckeWeakFEPair K I).k : ℝ) < σ.re) :
    (∑' a : nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by

  have hMC : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (σ - 1) • ((heckeWeakFEPair K I).f t
        - (heckeWeakFEPair K I).f₀)) (Set.Ioi 0) volume :=
    ((heckeWeakFEPair K I).hasMellin hσ).1
  suffices heq : (∑' a : nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          ‖(t : ℂ) ^ (σ - 1) • ((heckeWeakFEPair K I).f t
            - (heckeWeakFEPair K I).f₀)‖ₑ by
    rw [heq]; exact hMC.2.ne

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σ.re - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σ.re - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a : nonzeroIdeal K I,
      Measurable fun p : ℝ × logSpace K =>
        ENNReal.ofReal (Real.exp (-(π * ∑ w, placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)

  rw [← lintegral_tsum fun a => (hGE_meas a).aemeasurable.restrict,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (Measurable.tsum hGE_meas).aemeasurable]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  have hrpow_nn : (0:ℝ) ≤ t ^ (σ.re - 1) := Real.rpow_nonneg ht'.le _
  have hy : ∀ u : logSpace K, ∀ w, 0 < placeParam K (t, u) w :=
    fun u w => placeParam_pos K ht' (p := (t, u)) w

  have hΘ_real : ∀ u : logSpace K,
      multiIdealTheta K I (placeParam K (t, u)) - 1
        = ((∑' a : nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, placeParam K (t, u) w * (w (a : K)) ^ 2)) : ℝ)
          : ℂ) := fun u => by
    rw [multiIdealTheta_sub_one K I (hy u), Complex.ofReal_tsum]
    exact tsum_congr fun a => (Complex.ofReal_exp _).symm
  have hΘ_norm : ∀ u : logSpace K,
      ‖multiIdealTheta K I (placeParam K (t, u)) - 1‖
        = ∑' a : nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, placeParam K (t, u) w * (w (a : K)) ^ 2)) := fun u => by
    rw [hΘ_real u, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le)]
  have hintΘ := integrableOn_theta_sub_one K I ht'
  calc (∫⁻ u in unitBox K,
          ∑' a : nonzeroIdeal K I,
            ENNReal.ofReal (Real.exp (-(π * ∑ w, placeParam K (t, u) w
                * (w (a : K)) ^ 2)) * t ^ (σ.re - 1)) ∂volume)

      = ENNReal.ofReal (t ^ (σ.re - 1)) * ∫⁻ u in unitBox K,
            ‖multiIdealTheta K I (placeParam K (t, u)) - 1‖ₑ ∂volume := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun
          (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
        rw [tsum_congr fun a => by rw [mul_comm, ENNReal.ofReal_mul hrpow_nn],
          ENNReal.tsum_mul_left,
          ← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
            (summable_exp_neg_pi_placeParam K I (hy u)),
          ← ofReal_norm, hΘ_norm u]

    _ = ENNReal.ofReal (t ^ (σ.re - 1) * ∫ u in unitBox K,
            ‖multiIdealTheta K I (placeParam K (t, u)) - 1‖ ∂volume) := by
        rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            fun u _ => (ofReal_norm _).symm,
          ← ofReal_integral_eq_lintegral_ofReal hintΘ.norm (ae_of_all _ fun u => norm_nonneg _),
          ENNReal.ofReal_mul hrpow_nn]

    _ = _ := by
        rw [← ofReal_norm, smul_eq_mul, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.one_re,
          show (heckeWeakFEPair K I).f = heckeKernel K I from rfl,
          show ((heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl,
          heckeKernel_sub_one_eq_integral K I ht',
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_real u),
          integral_complex_ofReal, Complex.norm_real,
          Real.norm_of_nonneg (integral_nonneg fun u => tsum_nonneg fun _ => (Real.exp_pos _).le),
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_norm u)]

-- pin: gapsw80_t8_integrableOn_orbitRepr (S_NumberField_exists_completedDedekindZeta_package.lean:4443)
theorem integrableOn_orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((heckeWeakFEPair K I).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, placeParam K p w
            * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, placeParam K p w
          * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (continuous_cexp_placeParam K I ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
      fun p hp => enorm_integrand_eq K σ (orbitRepr K I ω) (p := p) hp.1]
  refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (lintegral_master_ne_top K I hσ))
  rw [lintegral_master_reindex K I σ.re]
  exact le_trans
    (ENNReal.le_tsum (f := fun ω' : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)) =>
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (Real.exp (-(π * ∑ w, placeParam K p w * (w (orbitRepr K I ω')) ^ 2))
          * p.1 ^ (σ.re - 1))) ω)
    (le_mul_of_one_le_left' (by exact_mod_cast torsionOrder_pos K))

-- pin: gapsw80_t8_quadForm_unit_smul_c (S_NumberField_exists_completedDedekindZeta_package.lean:4469)
theorem quadForm_unit_smul_weighted (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (η : (𝓞 K)ˣ) (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * placeParam K p w * (w ((η • a : nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * placeParam K p w * unitSqScale K η w * (w (a : K)) ^ 2 := by
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcoe : ((η • a : nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
  rw [hcoe, Algebra.smul_def, map_mul, mul_pow, unitSqScale,
    show ((algebraMap (𝓞 K) K) (η : 𝓞 K) : K) = ((η : 𝓞 K) : K) from rfl]
  ring

-- pin: gapsw80_t8_quadForm_torsion_invariant_c (S_NumberField_exists_completedDedekindZeta_package.lean:4481)
theorem quadForm_torsion_invariant_weighted (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (ζ : torsion K) (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * placeParam K p w
          * (w (((ζ : (𝓞 K)ˣ) • a : nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, c w * placeParam K p w * (w (a : K)) ^ 2 := by
  rw [quadForm_unit_smul_weighted]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [unitSqScale, (mem_torsion K).mp ζ.2 w, one_pow, mul_one]

-- pin: gapsw80_t8_quadForm_shift_single_c (S_NumberField_exists_completedDedekindZeta_package.lean:4491)
theorem quadForm_shift_single_weighted (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * placeParam K (t, u + Pi.single i 1) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * placeParam K (t, u) w
            * (w (((fundSystem K (equivFinRank.symm i)) • a : nonzeroIdeal K I) : K)) ^ 2 := by
  rw [quadForm_unit_smul_weighted]
  exact Finset.sum_congr rfl fun w _ => by rw [placeParam_add_single K ht]; ring

-- pin: gapsw80_t8_quadForm_shift_span_c (S_NumberField_exists_completedDedekindZeta_package.lean:4502)
theorem quadForm_shift_span_weighted (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * placeParam K (t, u) w
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
      ∑ w, c w * placeParam K (t, v + (k : ℝ) • Pi.single i 1) w * (w (b : K)) ^ 2
        = ∑ w, c w * placeParam K (t, v) w
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
        ← add_assoc, quadForm_shift_single_weighted K I c ht,
        ih (fundSystem K (equivFinRank.symm i) • b), ← mul_smul, ← _root_.zpow_add_one,
        show ((n:ℤ)+1 : ℤ) = (((n:ℕ)+1:ℕ):ℤ) from by push_cast; ring]
    | pred n ih =>
      intro b
      have key := (quadForm_shift_single_weighted K I c ht
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
      ∑ w, c w * placeParam K (t, u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) w
          * (w (a' : K)) ^ 2
        = ∑ w, c w * placeParam K (t, u) w
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

-- pin: gapsw80_t8_continuous_cexpQ_c (S_NumberField_exists_completedDedekindZeta_package.lean:4566)
theorem continuous_cexp_placeParam_weighted (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (a : nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, c w * placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finsetSum _ fun w _ => ?_)
  exact (continuous_const.mul
    (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd))).mul continuous_const

-- pin: gapsw80_t8_enorm_integrand_eq_c (S_NumberField_exists_completedDedekindZeta_package.lean:4575)
theorem enorm_integrand_eq_weighted (c : realSpace K) (σ : ℂ) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, c w * placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, c w * placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  rw [← ofReal_norm, norm_mul, Complex.norm_exp, Complex.ofReal_re,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
    Complex.sub_re, Complex.one_re]

-- pin: gapsw80_t8_rankinSelberg_unfold_c (S_NumberField_exists_completedDedekindZeta_package.lean:4586)
theorem rankinSelberg_unfold (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (σ : ℂ)
    (hMaster : (∑' a : nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, c w * placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤)
    (hIntω : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, c w * placeParam K p w
              * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume) :
    (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
        * ∫ u in unitBox K,
            (∑' a : nonzeroIdeal K I,
              cexp ((-(π * ∑ w, c w * placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
            ∂volume)
      = (torsionOrder K : ℂ) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K, c w * placeParam K p w
                * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ (σ - 1) := by

  set F : nonzeroIdeal K I → ℝ × logSpace K → ℂ := fun a p =>
    cexp ((-(π * ∑ w, c w * placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ)
      * ((p.1 : ℝ) : ℂ) ^ (σ - 1) with hF_def
  have hF_sm : ∀ a, AEStronglyMeasurable (F a)
      (volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (unitBox K))) := fun a =>
    ((continuous_cexp_placeParam_weighted K I c a).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt).aestronglyMeasurable
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
  have hF_enorm : ∀ a, ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
      ‖F a p‖ₑ = ENNReal.ofReal
        (Real.exp (-(π * ∑ w, c w * placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a p hp =>
    enorm_integrand_eq_weighted K c σ (a : K) (p := p) hp.1
  have hMaster' : (∑' a, ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), ‖F a p‖ₑ) ≠ ⊤ := by
    refine (tsum_congr fun a => setLIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      (hF_enorm a)).symm ▸ hMaster

  have hFsum_int : IntegrableOn (fun p => ∑' a, F a p)
      ((Set.Ioi (0:ℝ)) ×ˢ (unitBox K)) volume := by
    refine ⟨AEStronglyMeasurable.tsum hF_sm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hMaster')
    rw [← lintegral_tsum fun a => (hF_sm a).enorm]
    exact lintegral_mono fun p => enorm_tsum_le_tsum_enorm
  rw [show (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in unitBox K,
              (∑' a : nonzeroIdeal K I,
                cexp ((-(π * ∑ w, c w * placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume)
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), ∑' a, F a p from by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hFsum_int]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
      fun u _ => by rw [tsum_mul_right, mul_comm]]

  rw [integral_tsum (fun a => hF_sm a) hMaster']

  have hSsum : Summable fun a => ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), F a p := by
    refine .of_norm (.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
      (ENNReal.summable_toReal hMaster'))
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
    exact ENNReal.toReal_mono
      (ne_top_of_le_ne_top hMaster'
        (ENNReal.le_tsum (f := fun a =>
          ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), ‖F a p‖ₑ) a))
      (enorm_integral_le_lintegral_enorm _)
  have hF_Q : ∀ (a b : nonzeroIdeal K I) (p : ℝ × logSpace K),
      (∑ w, c w * placeParam K p w * (w (a : K)) ^ 2)
        = ∑ w, c w * placeParam K p w * (w (b : K)) ^ 2 →
      F a p = F b p := fun a b p hQ => by unfold F; rw [hQ]
  have hSsumSig : Summable fun p :
        Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)), (𝓞 K)ˣ =>
      ∫ q in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), F (orbitSigmaEquiv K I p) q :=
    (orbitSigmaEquiv K I).summable_iff.mpr hSsum
  rw [((orbitSigmaEquiv K I).tsum_eq _).symm.trans hSsumSig.tsum_sigma,
    ← tsum_mul_left]
  refine tsum_congr fun ω => ?_
  have hstep6a : ∀ (p' : torsion K × (Fin (rank K) → ℤ)) (p : ℝ × logSpace K),
      F (orbitSigmaEquiv K I ⟨ω, dirichletUnitEquiv K p'⟩) p
        = F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p =>
    hF_Q _ _ p (by
      rw [show ((orbitSigmaEquiv K I ⟨ω, dirichletUnitEquiv K p'⟩ :
            nonzeroIdeal K I) : K)
          = ((dirichletUnitEquiv K p' • ω.out : nonzeroIdeal K I) : K) from
        orbitSigmaEquiv_apply K I ω _,
        show dirichletUnitEquiv K p' • ω.out
            = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
          rw [← mul_smul]; rfl]
      exact quadForm_torsion_invariant_weighted K I c p p'.1 _)
  rw [← (dirichletUnitEquiv K).tsum_eq,
    tsum_congr fun p' => setIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      fun p _ => hstep6a p' p]
  have hSsumPr : Summable fun p' : torsion K × (Fin (rank K) → ℤ) =>
      ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
        F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p :=
    ((hSsumSig.sigma_factor ω).comp_injective (i := dirichletUnitEquiv K)
      (dirichletUnitEquiv K).injective).congr
      fun p' => setIntegral_congr_fun
        (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
        fun p _ => hstep6a p' p
  rw [hSsumPr.tsum_prod]
  dsimp only
  rw [tsum_const, nsmul_eq_mul,
    show ((torsionOrder K : ℕ) : ℂ) = (Nat.card (torsion K) : ℂ) from rfl]
  congr 1
  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (spanEquiv K).symm with hefr_def
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [show (∏ j, fundSystem K j ^ efr.symm g j)
        = (∏ i, fundSystem K (equivFinRank.symm i) ^ spanEquiv K g i) from
      Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
        fun j => by
          simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
            Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
            Equiv.symm_apply_apply, id_eq]]]

  have hInt_ω : IntegrableOn (F ω.out)
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := hIntω ω
  have hInt_box : ∀ b : nonzeroIdeal K I,
      IntegrableOn (F b) ((Set.Ioi (0:ℝ)) ×ˢ (unitBox K)) volume := fun b =>
    ⟨hF_sm b, hasFiniteIntegral_iff_enorm.mpr
      (lt_of_le_of_lt
        (ENNReal.le_tsum (f := fun b =>
          ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), ‖F b p‖ₑ) b)
        (lt_top_iff_ne_top.mpr hMaster'))⟩
  set ν : Measure (ℝ × logSpace K) :=
    ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume with hν_def
  have hν_eq : (volume : Measure (ℝ × logSpace K)).restrict
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) = ν := by
    rw [hν_def, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hν_box : (volume : Measure (ℝ × logSpace K)).restrict
        ((Set.Ioi (0:ℝ)) ×ˢ (unitBox K))
      = ν.restrict (Prod.snd ⁻¹' unitBox K) := by
    rw [hν_def, show (Prod.snd ⁻¹' unitBox K : Set (ℝ × logSpace K))
          = Set.univ ×ˢ unitBox K from Set.univ_prod.symm,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict]
  have hInt_ω' : Integrable (F ω.out) ν := by rw [← hν_eq]; exact hInt_ω
  have hFD_prod : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (Prod.snd ⁻¹' unitBox K) ν :=
    (unitBox_isAddFundamentalDomain K).preimage_of_equiv
      (f := Prod.snd) Measure.quasiMeasurePreserving_snd Function.bijective_id (fun _ _ => rfl)
  rw [show (fun p : ℝ × logSpace K =>
          cexp ((-(π * ∑ w, c w * placeParam K p w
                * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1)) = F ω.out from rfl,
    show (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)), F ω.out p)
        = ∫ p, F ω.out p ∂ν from by rw [← hν_eq],
    hFD_prod.integral_eq_tsum'' (F ω.out) hInt_ω']
  refine tsum_congr fun g => ?_
  rw [show (∫ p in Prod.snd ⁻¹' unitBox K, F ω.out (g +ᵥ p) ∂ν)
        = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K), F ω.out (g +ᵥ p) from by
    show (∫ p, _ ∂(ν.restrict _)) = ∫ p, _ ∂(volume.restrict _); rw [hν_box]]
  refine setIntegral_congr_fun
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
    fun p hp => ?_
  show F _ p = F ω.out (p.1, g +ᵥ p.2)
  unfold F
  congr 5
  rw [show (g +ᵥ p.2 : logSpace K) = p.2 + (g : logSpace K) from by
        rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
  exact (quadForm_shift_span_weighted K I c hp.1 p.2 g ω.out).symm

-- pin: gapsw80_t8_heckeLambda_unfold_eq (S_NumberField_exists_completedDedekindZeta_package.lean:4758)
theorem heckeLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                placeParam K p w *
                (w (orbitRepr K I x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def

  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((heckeWeakFEPair K I).k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hMellin := ((heckeWeakFEPair K I).hasMellin hσ_re).2
  rw [← hMellin]

  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((heckeWeakFEPair K I).f t
          - (heckeWeakFEPair K I).f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in unitBox K,
              (∑' a : nonzeroIdeal K I,
                cexp ((-(π * ∑ w, placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (heckeWeakFEPair K I).f = heckeKernel K I from rfl,
      show ((heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      heckeKernel_sub_one_eq_integral K I ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    exact multiIdealTheta_sub_one K I (fun w => placeParam_pos K ht' w)
  rw [show mellin (fun t => (heckeWeakFEPair K I).f t
        - (heckeWeakFEPair K I).f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in unitBox K,
              (∑' a : nonzeroIdeal K I,
                cexp ((-(π * ∑ w, placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  have hMaster1 : (∑' a : nonzeroIdeal K I,
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
        ENNReal.ofReal
          (Real.exp (-(π * ∑ w, (1:realSpace K) w * placeParam K p w * (w (a : K)) ^ 2))
            * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
    simp only [Pi.one_apply, one_mul]; exact lintegral_master_ne_top K I hσ_re
  have hIntω1 : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, (1:realSpace K) w * placeParam K p w
              * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := fun ω => by
    simp only [Pi.one_apply, one_mul]; exact integrableOn_orbitRepr K I hσ_re ω
  have hRS := rankinSelberg_unfold K I 1 σ hMaster1 hIntω1
  simp only [Pi.one_apply, one_mul] at hRS
  exact hRS

-- pin: gapsw80_t8_perOrbit_integral_eq (S_NumberField_exists_completedDedekindZeta_package.lean:4825)
theorem perOrbit_integral_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K I))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            placeParam K p w * (w (orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = (((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
        * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
          * ((|(Algebra.norm ℚ (orbitRepr K I ω) : ℚ)| : ℝ) : ℂ) ^ (-s)) := by
  set a : K := orbitRepr K I ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring

  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finsetSum _ fun w _ =>
          (continuous_apply w).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finsetProd _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    setIntegral_placeParam K hG_sm]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]

    rw [show cexp ((-(π * ∑ w, τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K, cexp ((-(π * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,

      prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]

    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*(w a)^2*τ w):ℝ):ℂ) * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)),

      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    ·
      rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    ·
      rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]

  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact mellin_expNeg_eq_Gamma
          (mul_pos Real.pi_pos (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  rw [show (∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = ∏ w : InfinitePlace K,
            (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by rw [normAtPlace_apply],
    prod_gammaFactor_eq K hs hx_nz,
    prod_normAtPlace_cpow K hx_nz s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

-- pin: gapsw80_t8_heckeLambda_eq_completedPartialZeta (S_NumberField_exists_completedDedekindZeta_package.lean:4965)
theorem heckeLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by

  rw [heckeLambda_unfold_eq K I hs,
    tsum_congr (perOrbit_integral_eq K I hs), tsum_mul_left, tsum_mul_left,
    tsum_orbit_normInv_eq K I hs, mul_pow (Gammaℂ s), div_eq_mul_inv, mul_inv, mul_inv]

  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K I):ℝ):ℂ)^(-s) with hCcov
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2) with hCdisc
  set CabsN : ℂ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s) with hCabsN
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) with hC2rs
  have hcd : Ccov * Cdisc = CabsN * C2rs := covol_discr_cpow K I s

  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h1 := card_add_two_mul_card_eq_rank K
    have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hconst : (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * C2rs := by
    have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
        = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * C2rs := by
      rw [hC2rs, Complex.ofReal_ofNat,
        ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
        ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
        ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
        ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
      congr 1
      push_cast [Nat.cast_sub hr₁]; ring
    rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zpow, Complex.ofReal_ofNat]
    linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow
  linear_combination (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s) * hcd

omit [NumberField K] in
-- pin: gapsw80_t8_one_le_multSq (S_NumberField_exists_completedDedekindZeta_package.lean:5016)
theorem one_le_multSq (w : InfinitePlace K) : (1:ℝ) ≤ multSq K w :=
  one_le_pow₀ (Nat.one_le_cast.mpr mult_pos)

-- pin: gapsw80_t8_multHeckeKernel_sub_one (S_NumberField_exists_completedDedekindZeta_package.lean:5019)
theorem multHeckeKernel_sub_one_eq_integral (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    multHeckeKernel K J t - 1
      = ∫ u in unitBox K,
          (multiIdealTheta K J
            (fun w => multSq K w * placeParam K (t, u) w) - 1) ∂volume := by
  have hvol : volume (unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hcont : Continuous
      (fun u => multiIdealTheta K J
        (fun w => multSq K w * placeParam K (t, u) w)) := by
    have h := continuous_genericKernel_integrand K J (Real.log t / 2)
      (multSq K) (fun w => multSq_pos K w)
    exact h.congr fun u => by
      congr 1; funext w
      rw [Pi.mul_apply, yParam_mkParam_factor K ht]; rfl
  have hint1 : IntegrableOn
      (fun u => multiIdealTheta K J
        (fun w => multSq K w * placeParam K (t, u) w))
      (unitBox K) volume := by
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
  unfold multHeckeKernel multHeckeIntegrand
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w
  rw [Pi.mul_apply, yParam_mkParam_factor K ht]; rfl

-- pin: gapsw80_t8_rexpQ_c_le (S_NumberField_exists_completedDedekindZeta_package.lean:5057)
theorem exp_neg_pi_placeParam_le_of_one_le {c : realSpace K} (hc : ∀ w, 1 ≤ c w) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    Real.exp (-(π * ∑ w, c w * placeParam K p w * (w x) ^ 2))
      ≤ Real.exp (-(π * ∑ w, placeParam K p w * (w x) ^ 2)) := by
  refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le))
  refine Finset.sum_le_sum fun w _ => ?_
  have hpp := (placeParam_pos K hp w).le
  have hwx := sq_nonneg (w x)
  nlinarith [hc w, mul_nonneg hpp hwx]

-- pin: gapsw80_t8_master_finite_mult (S_NumberField_exists_completedDedekindZeta_package.lean:5067)
theorem lintegral_master_multSq_ne_top (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((heckeWeakFEPair K J).k : ℝ) < σ.re) :
    (∑' a : nonzeroIdeal K J,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, multSq K w * placeParam K p w
                * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (lintegral_master_ne_top K J hσ) ?_
  refine ENNReal.tsum_le_tsum fun a => ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))] with p hp
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (exp_neg_pi_placeParam_le_of_one_le K (one_le_multSq K) (a : K) hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

-- pin: gapsw80_t8_integrableOn_orbitRepr_mult (S_NumberField_exists_completedDedekindZeta_package.lean:5084)
theorem integrableOn_orbitRepr_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((heckeWeakFEPair K J).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K J))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, multSq K w * placeParam K p w
            * (w (orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  set a : K := orbitRepr K J ω
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, multSq K w * placeParam K p w
          * (w a) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (continuous_cexp_placeParam_weighted K J (multSq K) ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound := (integrableOn_orbitRepr K J hσ ω).2
  rw [hasFiniteIntegral_iff_enorm] at hbound
  refine lt_of_le_of_lt ?_ hbound
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  rw [enorm_integrand_eq_weighted K (multSq K) σ a hp.1,
    enorm_integrand_eq K σ a hp.1]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (exp_neg_pi_placeParam_le_of_one_le K (one_le_multSq K) a hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

-- pin: gapsw80_t8_symmLambda_unfold_eq (S_NumberField_exists_completedDedekindZeta_package.lean:5115)
theorem symmLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ)
            (nonzeroIdeal K (traceDualIdeal K I))),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                multSq K w * placeParam K p w *
                (w (orbitRepr K (traceDualIdeal K I) x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := traceDualIdeal K I with hJ_def
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def
  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((heckeWeakFEPair K I).symm.k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hσ_reJ : ((heckeWeakFEPair K J).k : ℝ) < σ.re := hσ_re

  have hMellin := ((heckeWeakFEPair K I).symm.hasMellin hσ_re).2
  rw [← hMellin]

  have hy : ∀ {t : ℝ} (_ : 0 < t) (u : logSpace K), ∀ w,
      0 < multSq K w * placeParam K (t, u) w := fun ht u w =>
    mul_pos (multSq_pos K w) (placeParam_pos K ht w)
  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((heckeWeakFEPair K I).symm.f t
          - (heckeWeakFEPair K I).symm.f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in unitBox K,
              (∑' a : nonzeroIdeal K J,
                cexp ((-(π * ∑ w, multSq K w * placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (heckeWeakFEPair K I).symm.f
          = multHeckeKernel K J from rfl,
      show ((heckeWeakFEPair K I).symm.f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      multHeckeKernel_sub_one_eq_integral K J ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    have := multiIdealTheta_sub_one K J (y := fun w =>
        multSq K w * placeParam K (t, u) w) (hy ht' u)
    simpa only [mul_assoc] using this
  rw [show mellin (fun t => (heckeWeakFEPair K I).symm.f t
        - (heckeWeakFEPair K I).symm.f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in unitBox K,
              (∑' a : nonzeroIdeal K J,
                cexp ((-(π * ∑ w, multSq K w * placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  exact rankinSelberg_unfold K J (multSq K) σ
    (lintegral_master_multSq_ne_top K J hσ_reJ)
    (integrableOn_orbitRepr_mult K J hσ_reJ)

-- pin: gapsw80_t8_perOrbit_integral_eq_mult (S_NumberField_exists_completedDedekindZeta_package.lean:5180)
theorem perOrbit_integral_eq_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (nonzeroIdeal K J))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            multSq K w * placeParam K p w
              * (w (orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
            * ((|(Algebra.norm ℚ (orbitRepr K J ω) : ℚ)| : ℝ) : ℂ) ^ (-s))) := by
  set a : K := orbitRepr K J ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, multSq K w * τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, multSq K w * placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring
  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finsetSum _ fun w _ =>
          (continuous_const.mul (continuous_apply w)).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finsetProd _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    setIntegral_placeParam K hG_sm]
  rw [show ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K:ℂ)*s)
        * ((((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s)))
      = (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
        * (((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s))) from by ring]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * multSq K w * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]
    rw [show cexp ((-(π * ∑ w, multSq K w * τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K,
              cexp ((-(π * multSq K w * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,
      prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*multSq K w*(w a)^2*τ w):ℝ):ℂ)
          * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
          * cexp ((-(π*multSq K w*(w a)^2*τ w):ℝ):ℂ)),
      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    · rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    · rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*multSq K w*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*multSq K w*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]
  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
              * cexp ((-(π*multSq K w*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact mellin_expNeg_eq_Gamma
          (mul_pos (mul_pos Real.pi_pos (multSq_pos K w)) (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  have hsplit : ∀ w : InfinitePlace K,
      ((π * multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
        = ((multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
          * ((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) := fun w => by
    rw [show π * multSq K w * (w a)^2
          = multSq K w * (π * (w a)^2) from by ring,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (multSq_pos K w).le
        (mul_nonneg Real.pi_pos.le (sq_nonneg _))]
  rw [show (∏ w : InfinitePlace K,
            (((π * multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = (∏ w : InfinitePlace K, ((multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))
          * ∏ w : InfinitePlace K,
              (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
                * Complex.Gamma ((w.mult:ℂ)*s/2)) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [hsplit w, normAtPlace_apply]; ring,
    prod_gammaFactor_eq K hs hx_nz,
    prod_normAtPlace_cpow K hx_nz s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

  congr 1
  rw [prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))]
  have hreal : (∏ w : {w : InfinitePlace K // IsReal w},
      ((multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2))) = 1 :=
    Finset.prod_eq_one fun w _ => by
      rw [show multSq K w.1 = 1 from by
        simp [multSq, mult_isReal w], Complex.ofReal_one, Complex.one_cpow]
  have hcplx : (∏ w : {w : InfinitePlace K // IsComplex w},
        ((multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
      = ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) := by
    rw [show (∏ w : {w : InfinitePlace K // IsComplex w},
            ((multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
          = ∏ _w : {w : InfinitePlace K // IsComplex w}, ((4:ℝ):ℂ)^(-s) from
        Finset.prod_congr rfl fun w _ => by
          rw [show multSq K w.1 = 4 from by
            simp [multSq, mult_isComplex w]; norm_num,
            mult_isComplex w]
          congr 1; push_cast; ring,
      Finset.prod_const, ← Complex.cpow_nat_mul, Finset.card_univ,
      show Fintype.card {w : InfinitePlace K // IsComplex w} = nrComplexPlaces K from rfl]
    congr 1; ring
  rw [hreal, one_mul, hcplx]

-- pin: gapsw80_t8_symmLambda_eq_completedPartialZeta (S_NumberField_exists_completedDedekindZeta_package.lean:5363)
theorem symmLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K
            (traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * partialDedekindZeta K (ClassGroup.mk K (traceDualIdeal K I))⁻¹ s := by
  set J := traceDualIdeal K I with hJ_def

  rw [symmLambda_unfold_eq K I hs,
    tsum_congr (perOrbit_integral_eq_mult K J hs), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, tsum_orbit_normInv_eq K J hs, mul_pow (Gammaℂ s),
    div_eq_mul_inv, mul_inv, mul_inv]

  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K J):ℝ):ℂ)^(-s) with hCcov
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2) with hCdisc
  set CabsN : ℂ := ((FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s) with hCabsN
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) with hC2rs
  set C4rs : ℂ := ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) with hC4rs
  have hcd : Ccov * Cdisc = CabsN * C2rs := covol_discr_cpow K J s
  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h1 := card_add_two_mul_card_eq_rank K
    have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hconst : (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * C2rs := by
    have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
        = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * C2rs := by
      rw [hC2rs, Complex.ofReal_ofNat,
        ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
        ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
        ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
        ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
      congr 1
      push_cast [Nat.cast_sub hr₁]; ring
    rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zpow, Complex.ofReal_ofNat]
    linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow
  linear_combination C4rs * (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - C4rs * ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s) * hcd

-- pin: gapsw80_t8_sat_covol_prod (S_NumberField_exists_completedDedekindZeta_package.lean:5418)
theorem covolume_mul_covolume_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * ZLattice.covolume (mixedEmbedding.idealLattice K (traceDualIdeal K I))
      = (4 : ℝ)⁻¹ ^ nrComplexPlaces K := by
  have h4 : ((4:ℝ) ^ nrComplexPlaces K) ≠ 0 := (pow_pos (by norm_num) _).ne'
  have hdet : |(bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (traceDualIdeal K I)) := by
    rw [bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, abs_det_Phi]
  have h1 : ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * (4 : ℝ) ^ nrComplexPlaces K
        * ZLattice.covolume (mixedEmbedding.idealLattice K (traceDualIdeal K I))
      = 1 := hdet ▸ abs_det_bridgeMatrix K I
  rw [inv_pow]; field_simp
  linear_combination h1

end

end NumberField.CompletedDedekindZeta
