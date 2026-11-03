/-
  The archimedean atom's integral: its value, its limit at `s = 1/2`, and a uniform bound.

  The pin's real and complex atoms are

    `atom σ x = ((x - I) / sqrt (1 + x^2)) ^ k * (1 + x^2) ^ (-(σ + 1/2))`  (real place),
    `atom σ z = z ^ a * conj z ^ b * (1 + ‖z‖ ^ 2) ^ (-(2σ+1) - m/2)`       (complex place),

  and this module carries the four facts about their integrals that the local intertwining operator
  needs, all in the half-plane `re s > 0`:

  * `integral_one_add_sq_cpow_neg_eq_GammaReal_div` — the real evaluation
    `∫ x, (1 + x^2) ^ (-(s + 1/2)) = Gammaℝ (2s) / Gammaℝ (2s + 1)`;
  * `integral_one_add_norm_sq_cpow_neg_eq_pi_div` — the complex evaluation
    `∫ z, (1 + ‖z‖ ^ 2) ^ (-(2s+1)) = π / (2s)`;
  * `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` and its real twin
    `tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` — the integral of the
    `σ`-dependent Möbius factor `((‖c'z+d'‖^2) ^ (2σ-1) - 1)` against the atom tends to `0` as
    `σ ↓ 1/2`, so the endpoint `s = 1/2` is continuous;
  * `exists_bound_norm_integral_mixedSpace_archAtom_prod` — the product of the archimedean atoms over
    all infinite places is uniformly bounded on the strip `1/2 < σ ≤ 1`, by a constant depending on the
    data only.

  Transcribed from five pin `S_` files (pinned `aa2d8b3`), whose `Theorems/` wrappers carry the
  headlines' statements:

  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.lean`

  The pin's file-level labels (`M4aP2DGK.ArchReal`, `M4aP2DGK.ArchComplex`, `ARCHA4C`, `ARCHA4R`,
  `W4ARCH`) are proof-search artefacts and are replaced by subject namespaces. Four of the five pin
  files import `Mathlib`; this module names the mathlib modules they need instead. The two `atom`
  definitions are a same-name pair with different statements (one over `ℂ`, one over `ℝ`) and are kept
  as two declarations in the two sub-namespaces, not merged.

  **Visibility.** The two evaluations and the two limits are flat public surfaces in the pin, and are
  public here; the mixed-space bound's prelude is `private` there and stays `private` here.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the five `Theorems/` wrappers and
  the five `S_` files are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.lean
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open NumberField NumberField.InfinitePlace

namespace AutomorphicForm
namespace LocalIntertwining

/-! ### Two helpers of the `σ ↓ 1/2` rows, written once

The pin proves `one_add_sq_pos` in both `ARCHA4C` and `ARCHA4R` and `rpow_le_max` in both as well. Both
are the same mathematics at the two places, so they are written **once**, publicly, at the pin's names
(the real-place spellings), and used from both rows (§2.2 "port once"). The complex-place reading is the
same statement at `‖z‖`. -/

theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

theorem rpow_le_max (K t : ℝ) (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : K ^ t ≤ max 1 K := by
  rcases le_or_gt K 1 with h | h
  · exact (Real.rpow_le_one hK h ht0).trans (le_max_left _ _)
  · refine (Real.rpow_le_rpow_of_exponent_le h.le ht1).trans ?_
    rw [Real.rpow_one]; exact le_max_right _ _

/-! ### The real evaluation: `∫ x, (1 + x^2) ^ (-(s + 1/2)) = Γ_ℝ(2s) / Γ_ℝ(2s+1)` -/
namespace GammaReal

open MeasureTheory Set Complex

theorem scaledGammaIntegral {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
      = ((r : ℝ) : ℂ) ^ (-a) * Complex.Gamma a := by
  have hsub := integral_deriv_smul_comp_Ioi
    (f := fun t : ℝ => r * t) (f' := fun _ : ℝ => r)
    (g := fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) (a := 0)
    (by fun_prop)
    (Filter.tendsto_id.const_mul_atTop hr)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul r).hasDerivWithinAt)
    ?_ ?_ ?_
  ·
    simp only [Function.comp_def, mul_zero] at hsub
    have hΓ : (∫ u in Ioi (0 : ℝ), ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1))
        = Complex.Gamma a := (Complex.Gamma_eq_integral ha).symm
    rw [hΓ] at hsub

    have hpt : ∀ t ∈ Ioi (0 : ℝ),
        (r : ℝ) • (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
          = ((r : ℝ) : ℂ) ^ a *
            (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)) := by
      intro t ht
      rw [real_smul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hr.le (le_of_lt ht)]
      have hrne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      rw [show ((r : ℝ) : ℂ) ^ (a - 1) = ((r : ℝ) : ℂ) ^ a / ((r : ℝ) : ℂ) ^ (1 : ℂ) from
        Complex.cpow_sub _ _ hrne, Complex.cpow_one]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
    have hrpow : ((r : ℝ) : ℂ) ^ a ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
    calc ∫ t in Ioi (0 : ℝ), ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
        = (((r : ℝ) : ℂ) ^ a)⁻¹ * (((r : ℝ) : ℂ) ^ a *
            ∫ t in Ioi (0 : ℝ), ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hrpow, one_mul]
      _ = (((r : ℝ) : ℂ) ^ a)⁻¹ * Complex.Gamma a := by rw [hsub]
      _ = ((r : ℝ) : ℂ) ^ (-a) * Complex.Gamma a := by
          rw [Complex.cpow_neg]
  ·
    have himg : (fun t : ℝ => r * t) '' Ioi 0 ⊆ Ioi (0 : ℝ) := by
      rintro u ⟨t, ht, rfl⟩
      exact mul_pos hr ht
    refine ContinuousOn.mono ?_ himg
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).continuousOn.mul
      (ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn)
        (fun u hu => Or.inl (by exact_mod_cast hu)))
  ·
    have hIci : IntegrableOn
        (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact Complex.GammaIntegral_convergent ha
    refine hIci.mono_set ?_
    rintro u ⟨t, ht, rfl⟩
    exact mul_nonneg hr.le ht
  ·
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hcomp : IntegrableOn
        (fun t : ℝ => ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
        (Ioi 0) := by
      exact (integrableOn_Ioi_comp_mul_left_iff
        (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) 0 hr).mpr
        (by simpa using Complex.GammaIntegral_convergent ha)
    exact hcomp.smul r

theorem cpow_neg_eq_gamma_inv_mul_integral {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-a)
      = (Complex.Gamma a)⁻¹ *
        ∫ t in Ioi (0 : ℝ), ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ)
          * ((t : ℝ) : ℂ) ^ (a - 1) := by
  have hx : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [scaledGammaIntegral ha hx, mul_comm (((1 + x ^ 2 : ℝ) : ℂ) ^ (-a)) (Complex.Gamma a),
    ← mul_assoc, inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos ha), one_mul]

theorem integrableOn_scaledGamma {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
      (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
      (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) 0 hr).mpr
      (by simpa using Complex.GammaIntegral_convergent ha)
  refine IntegrableOn.congr_fun
    (Integrable.const_mul hbase (((r : ℝ) : ℂ) ^ ((1 : ℂ) - a))) ?_ measurableSet_Ioi
  intro t ht
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  show ((r : ℝ) : ℂ) ^ ((1 : ℂ) - a)
      * (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
    = ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
  have hsplit : ((r * t : ℝ) : ℂ) ^ (a - 1)
      = ((r : ℝ) : ℂ) ^ (a - 1) * ((t : ℝ) : ℂ) ^ (a - 1) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (le_of_lt ht)]
  rw [hsplit,
    show ((r : ℝ) : ℂ) ^ ((1 : ℂ) - a)
        * (((Real.exp (-(r * t)) : ℝ) : ℂ)
          * (((r : ℝ) : ℂ) ^ (a - 1) * ((t : ℝ) : ℂ) ^ (a - 1)))
      = ((r : ℝ) : ℂ) ^ ((1 : ℂ) - a) * ((r : ℝ) : ℂ) ^ (a - 1)
        * (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)) by ring,
    ← Complex.cpow_add _ _ hrne,
    show ((1 : ℂ) - a) + (a - 1) = 0 by ring, Complex.cpow_zero, one_mul]

theorem integrable_one_add_sq_rpow_neg {c : ℝ} (hc : 1 / 2 < c) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-c)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * c)
    (by rw [Module.finrank_self]; push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

theorem integrable_uncurry_kernel {a : ℂ} (ha : 1 / 2 < a.re) :
    Integrable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
        ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict (Ioi 0))) := by
  have ha0 : 0 < a.re := by linarith
  have hpt : ∀ x : ℝ, (0 : ℝ) < 1 + x ^ 2 := fun x => by positivity
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
      ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ ?_
    · exact Complex.measurable_ofReal.comp
        ((Real.continuous_exp.measurable).comp
          ((((continuous_const.add (continuous_pow 2)).comp continuous_fst).mul
            continuous_snd).neg.measurable))
    · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  ·
    refine Filter.Eventually.of_forall fun x => ?_
    have h__af := integrableOn_scaledGamma ha0 (hpt x)
    simp at h__af ⊢
    exact h__af
  ·
    have hnorm : ∀ x : ℝ, (fun t : ℝ => ‖((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ)
        * ((t : ℝ) : ℂ) ^ (a - 1)‖) =ᵐ[MeasureTheory.volume.restrict (Ioi 0)]
        fun t : ℝ => t ^ (a.re - 1) * Real.exp (-((1 + x ^ 2) * t)) := by
      intro x
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp [mul_comm]
    have hval : ∀ x : ℝ, (∫ t in Ioi (0 : ℝ),
        ‖((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)‖)
        = (1 / (1 + x ^ 2)) ^ a.re * Real.Gamma a.re := by
      intro x
      rw [MeasureTheory.integral_congr_ae (hnorm x)]
      have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a.re) (r := 1 + x ^ 2)
        ha0 (hpt x)
      simpa [sub_re, one_re] using this
    refine MeasureTheory.Integrable.congr
      ((integrable_one_add_sq_rpow_neg ha).const_mul (Real.Gamma a.re)) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    show Real.Gamma a.re * (1 + x ^ 2) ^ (-a.re)
      = ∫ t in Ioi (0 : ℝ), ‖((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ)
          * ((t : ℝ) : ℂ) ^ (a - 1)‖
    rw [hval x, one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (hpt x).le,
      neg_one_mul, mul_comm]

theorem integral_cpow_neg_one_add_sq {a : ℂ} (ha : 1 / 2 < a.re) :
    ∫ x : ℝ, (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-a)
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.Gamma (a - 1 / 2) / Complex.Gamma a := by
  have ha0 : 0 < a.re := by linarith
  have ha12 : 0 < (a - 1 / 2).re := by
    rw [Complex.sub_re]
    norm_num
    linarith
  have hpt : ∀ x : ℝ, (0 : ℝ) < 1 + x ^ 2 := fun x => by positivity
  have hΓne : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0

  have h1 : ∫ x : ℝ, (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-a)
      = (Complex.Gamma a)⁻¹ * ∫ x : ℝ, ∫ t in Ioi (0 : ℝ),
          ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simpa using cpow_neg_eq_gamma_inv_mul_integral ha0 x)

  have h2 : ∫ x : ℝ, ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
      = ∫ t in Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1) :=
    MeasureTheory.integral_integral_swap (integrable_uncurry_kernel ha)

  have h3 : ∀ t ∈ Ioi (0 : ℝ),
      (∫ x : ℝ, ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
        = ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
          * ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ) := by
    intro t ht
    have htC : (0 : ℝ) < t := ht
    have hsplit : ∀ x : ℝ,
        ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
          = (((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
            * Complex.exp (-((t : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ 2) := by
      intro x
      have hexp : Real.exp (-((1 + x ^ 2) * t)) = Real.exp (-t) * Real.exp (-(t * x ^ 2)) := by
        rw [← Real.exp_add]
        ring_nf
      rw [hexp, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
      MeasureTheory.integral_const_mul, integral_gaussian_complex (by simpa using htC)]

  have h4 : ∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
        * ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.Gamma (a - 1 / 2) := by
    have hptw : ∀ t ∈ Ioi (0 : ℝ),
        ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
          * ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
        = (Real.pi : ℂ) ^ (1 / 2 : ℂ)
          * (((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1 / 2 - 1)) := by
      intro t ht
      have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      have hdiv : ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (((t : ℝ) : ℂ) ^ (1 / 2 : ℂ))⁻¹ := by
        rw [div_eq_mul_inv, ← Complex.ofReal_inv,
          Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (inv_nonneg.mpr (le_of_lt ht)),
          Complex.ofReal_inv,
          Complex.inv_cpow _ _ (by
            rw [Complex.arg_ofReal_of_nonneg (le_of_lt ht)]
            exact fun h => Real.pi_ne_zero h.symm)]
      rw [hdiv, ← Complex.cpow_neg]
      rw [show ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
            * ((Real.pi : ℂ) ^ (1 / 2 : ℂ) * ((t : ℝ) : ℂ) ^ (-(1 / 2) : ℂ))
          = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (((Real.exp (-t) : ℝ) : ℂ)
            * (((t : ℝ) : ℂ) ^ (a - 1) * ((t : ℝ) : ℂ) ^ (-(1 / 2) : ℂ))) by ring,
        ← Complex.cpow_add _ _ htne,
        show (a - 1) + (-(1 / 2) : ℂ) = a - 1 / 2 - 1 by ring]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hptw,
      MeasureTheory.integral_const_mul]
    congr 1
    exact (Complex.Gamma_eq_integral ha12).symm

  rw [h1, h2, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h3, h4]
  field_simp

theorem arch_integral_value {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-(s + 1 / 2))
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.Gamma s / Complex.Gamma (s + 1 / 2) := by
  have ha : 1 / 2 < (s + 1 / 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  rw [integral_cpow_neg_one_add_sq ha,
    show (s + 1 / 2 - 1 / 2 : ℂ) = s by ring]

theorem gammaR_two_mul (s : ℂ) :
    Gammaℝ (2 * s) = (Real.pi : ℂ) ^ (-s) * Complex.Gamma s := by
  rw [Gammaℝ]
  congr 1
  · congr 1; ring
  · congr 1; ring

theorem gammaR_two_mul_add_one (s : ℂ) :
    Gammaℝ (2 * s + 1) = (Real.pi : ℂ) ^ (-s - 1/2) * Complex.Gamma (s + 1/2) := by
  rw [Gammaℝ]
  congr 1
  · congr 1; ring
  · congr 1; ring

theorem sqrtpi_gamma_mul_gammaR : ∀ s : ℂ,
    (Real.pi : ℂ) ^ (1/2 : ℂ) * Complex.Gamma s * Gammaℝ (2 * s + 1)
      = Complex.Gamma (s + 1/2) * Gammaℝ (2 * s) := by
  intro s
  rw [gammaR_two_mul, gammaR_two_mul_add_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hfold : (Real.pi : ℂ) ^ (1/2 : ℂ) * (Real.pi : ℂ) ^ (-s - 1/2)
      = (Real.pi : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hπ]
    congr 1
    ring
  calc (Real.pi : ℂ) ^ (1/2 : ℂ) * Complex.Gamma s
        * ((Real.pi : ℂ) ^ (-s - 1/2) * Complex.Gamma (s + 1/2))
      = ((Real.pi : ℂ) ^ (1/2 : ℂ) * (Real.pi : ℂ) ^ (-s - 1/2))
        * (Complex.Gamma s * Complex.Gamma (s + 1/2)) := by ring
    _ = (Real.pi : ℂ) ^ (-s) * (Complex.Gamma s * Complex.Gamma (s + 1/2)) := by
        rw [hfold]
    _ = Complex.Gamma (s + 1/2) * ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) := by ring

theorem integral_value_gammaR {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) := by
  rw [arch_integral_value hs]
  have hΓ : Complex.Gamma (s + 1 / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.add_re]
    norm_num
    linarith
  have hR : Complex.Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  rw [div_eq_div_iff hΓ hR, mul_comm (Complex.Gammaℝ (2 * s)) (Complex.Gamma (s + 1 / 2))]
  exact sqrtpi_gamma_mul_gammaR s

end GammaReal

theorem integral_one_add_sq_cpow_neg_eq_GammaReal_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) :=
  GammaReal.integral_value_gammaR hs

/-! ### The complex evaluation: `∫ z, (1 + ‖z‖^2) ^ (-(2s+1)) = π / (2s)` -/
namespace PiDiv

open MeasureTheory Set

theorem setIntegral_Ioi_comp_one_add (h : ℝ → ℂ) :
    ∫ y in Ioi (0 : ℝ), h (1 + y) = ∫ t in Ioi (1 : ℝ), h t := by
  have hfun : (fun y => (Ioi (0 : ℝ)).indicator (fun y => h (1 + y)) y)
      = fun y => (Ioi (1 : ℝ)).indicator h (1 + y) := by
    funext y
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy),
        Set.indicator_of_mem (show 1 + y ∈ Ioi (1 : ℝ) from by rw [Set.mem_Ioi]; linarith)]
    · rw [Set.indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),
        Set.indicator_of_notMem (show 1 + y ∉ Ioi (1 : ℝ) from by rw [Set.mem_Ioi]; linarith)]
  calc ∫ y in Ioi (0 : ℝ), h (1 + y)
      = ∫ y, (Ioi (0 : ℝ)).indicator (fun y => h (1 + y)) y := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ y, (Ioi (1 : ℝ)).indicator h (1 + y) := congrArg (fun F : ℝ → ℂ => ∫ y, F y) hfun
    _ = ∫ t, (Ioi (1 : ℝ)).indicator h t :=
        integral_add_left_eq_self (fun t => (Ioi (1 : ℝ)).indicator h t) 1
    _ = ∫ t in Ioi (1 : ℝ), h t := integral_indicator measurableSet_Ioi

theorem integral_one_add_cpow_neg {a : ℂ} (ha : 1 < a.re) :
    ∫ y in Ioi (0 : ℝ), ((1 + y : ℝ) : ℂ) ^ (-a) = 1 / (a - 1) := by
  have h1 : ∫ y in Ioi (0 : ℝ), ((1 + y : ℝ) : ℂ) ^ (-a) = ∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-a) :=
    setIntegral_Ioi_comp_one_add (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-a))
  rw [h1, integral_Ioi_cpow_of_lt (by rw [Complex.neg_re]; linarith) zero_lt_one, Complex.ofReal_one,
    Complex.one_cpow, show (-a + 1 : ℂ) = -(a - 1) by ring, div_neg, neg_div, neg_neg]

theorem integral_radial {a : ℂ} (ha : 1 < a.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-a) = 1 / (2 * (a - 1)) := by
  have hsub : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • ((1 + x ^ (2 : ℝ) : ℝ) : ℂ) ^ (-a)
      = ∫ y in Ioi (0 : ℝ), ((1 + y : ℝ) : ℂ) ^ (-a) :=
    integral_comp_rpow_Ioi (fun y : ℝ => ((1 + y : ℝ) : ℂ) ^ (-a)) two_ne_zero
  have hL : EqOn (fun x : ℝ => (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • ((1 + x ^ (2 : ℝ) : ℝ) : ℂ) ^ (-a))
      (fun x : ℝ => (2 : ℂ) * ((x : ℂ) * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-a))) (Ioi (0 : ℝ)) := by
    intro x _
    simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, abs_two, Complex.real_smul]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hL, integral_const_mul, integral_one_add_cpow_neg ha] at hsub

  have hI : (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-a))
      = (2 : ℂ)⁻¹ * (2 * ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-a)) := by ring
  rw [hI, hsub, one_div, one_div, ← mul_inv]

theorem integral_value {s : ℂ} (hs : 0 < s.re) :
    ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) = (Real.pi : ℂ) / (2 * s) := by
  have ha : 1 < (2 * s + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
    linarith

  have hprod : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) * (1 : ℂ) ∂((volume : Measure ℝ).prod volume))
      = (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))
          * ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℂ) :=
    setIntegral_prod_mul (fun r : ℝ => (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))
      (fun _ : ℝ => (1 : ℂ)) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
  calc ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))
      = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((1 + ‖Complex.polarCoord.symm p‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) :=
        (Complex.integral_comp_polarCoord_symm
          (fun z : ℂ => ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))).symm
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          (p.1 : ℂ) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) * (1 : ℂ)
            ∂((volume : Measure ℝ).prod volume) := by
        rw [Measure.volume_eq_prod]
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p _ => ?_
        rw [Complex.norm_polarCoord_symm, sq_abs, Complex.real_smul, mul_one]
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))
          * ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := hprod
    _ = 1 / (2 * (2 * s + 1 - 1)) * ((2 * Real.pi : ℝ) : ℂ) := by
        rw [integral_radial ha, setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
          Complex.real_smul, mul_one]
        congr 1
        push_cast
        ring
    _ = (Real.pi : ℂ) / (2 * s) := by
        push_cast
        rw [div_mul_eq_mul_div, one_mul, show (2 : ℂ) * (2 * s + 1 - 1) = 2 * (2 * s) by ring,
          mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0)]

end PiDiv

theorem integral_one_add_norm_sq_cpow_neg_eq_pi_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) = (Real.pi : ℂ) / (2 * s) :=
  PiDiv.integral_value hs

/-! ### The complex place: the Möbius factor's integral vanishes at `σ ↓ 1/2` -/
namespace ComplexAtomLimit

def atom (a b m : ℕ) (σ : ℝ) (z : ℂ) : ℂ :=
  z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)

theorem exponent_cast (σ : ℝ) (m : ℕ) :
    (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2) = (((-(2 * σ + 1) - (m : ℝ) / 2 : ℝ)) : ℂ) := by
  push_cast; ring

theorem norm_atom (a b m : ℕ) (σ : ℝ) (z : ℂ) :
    ‖atom a b m σ z‖ = ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2) := by
  rw [atom, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add, exponent_cast,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos ‖z‖), Complex.ofReal_re]

theorem norm_pow_le (z : ℂ) (n : ℕ) : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
  have h : ‖z‖ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖z‖])
  calc ‖z‖ ^ n ≤ (Real.sqrt (1 + ‖z‖ ^ 2)) ^ n := pow_le_pow_left₀ (norm_nonneg _) h n
    _ = (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; ring

theorem norm_atom_le (a b m : ℕ) (habm : a + b ≤ m) (σ : ℝ) (z : ℂ) :
    ‖atom a b m σ z‖ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by
  have hX : 0 < 1 + ‖z‖ ^ 2 := one_add_sq_pos ‖z‖
  have hX1 : 1 ≤ 1 + ‖z‖ ^ 2 := by linarith [sq_nonneg ‖z‖]
  rw [norm_atom]
  have h1 : ‖z‖ ^ (a + b) ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
    refine (norm_pow_le z (a + b)).trans (Real.rpow_le_rpow_of_exponent_le hX1 ?_)
    have : ((a + b : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast habm
    linarith
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2)
      ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hX.le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by
        rw [← Real.rpow_add hX]; congr 1; ring

theorem continuous_atom (a b m : ℕ) (σ : ℝ) : Continuous (atom a b m σ) := by
  unfold atom
  refine Continuous.mul (by fun_prop) ?_
  refine Continuous.cpow (by fun_prop) continuous_const fun z => ?_
  exact_mod_cast Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos ‖z‖)

theorem normSq_le (c' d' z : ℂ) : ‖c' * z + d'‖ ^ 2 ≤ (‖c'‖ ^ 2 + ‖d'‖ ^ 2) * (1 + ‖z‖ ^ 2) := by
  have h1 : ‖c' * z + d'‖ ≤ ‖c'‖ * ‖z‖ + ‖d'‖ := by
    refine (norm_add_le _ _).trans ?_; rw [norm_mul]
  have h2 : 0 ≤ ‖c'‖ * ‖z‖ + ‖d'‖ := by positivity
  calc ‖c' * z + d'‖ ^ 2 ≤ (‖c'‖ * ‖z‖ + ‖d'‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (‖c'‖ ^ 2 + ‖d'‖ ^ 2) * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (‖c'‖ - ‖d'‖ * ‖z‖)]

theorem norm_F_le {c' d' : ℂ} (a b m : ℕ) (habm : a + b ≤ m) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (z : ℂ) :
    ‖((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ) * atom a b m σ z‖
      ≤ (max 1 (‖c'‖ ^ 2 + ‖d'‖ ^ 2) + 1) * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by
  set t : ℝ := 2 * σ - 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  set K : ℝ := ‖c'‖ ^ 2 + ‖d'‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hX : 0 < 1 + ‖z‖ ^ 2 := one_add_sq_pos ‖z‖
  rw [norm_mul, Complex.norm_real]
  have hA := norm_atom_le a b m habm σ z
  have hWt : (‖c' * z + d'‖ ^ 2) ^ t ≤ max 1 K * (1 + ‖z‖ ^ 2) ^ t := by
    calc (‖c' * z + d'‖ ^ 2) ^ t ≤ (K * (1 + ‖z‖ ^ 2)) ^ t := Real.rpow_le_rpow (sq_nonneg _) (normSq_le c' d' z) ht0
      _ = K ^ t * (1 + ‖z‖ ^ 2) ^ t := Real.mul_rpow hK0 hX.le
      _ ≤ max 1 K * (1 + ‖z‖ ^ 2) ^ t :=
          mul_le_mul_of_nonneg_right (rpow_le_max K t hK0 ht0 ht1) (Real.rpow_nonneg hX.le _)
  have habs : ‖(‖c' * z + d'‖ ^ 2) ^ t - 1‖ ≤ (‖c' * z + d'‖ ^ 2) ^ t + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), norm_one]
  have h1 : (1 + ‖z‖ ^ 2) ^ t * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) = (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hX]; congr 1; rw [ht]; ring
  have h2 : (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) ≤ (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖z‖]) (by linarith)
  have hpos : 0 ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := Real.rpow_nonneg hX.le _
  have hM0 : 0 ≤ max 1 K := le_trans zero_le_one (le_max_left _ _)
  calc ‖(‖c' * z + d'‖ ^ 2) ^ t - 1‖ * ‖atom a b m σ z‖
      ≤ (max 1 K * (1 + ‖z‖ ^ 2) ^ t + 1) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) :=
        mul_le_mul (habs.trans (by linarith [hWt])) hA (norm_nonneg _) (by positivity)
    _ = max 1 K * ((1 + ‖z‖ ^ 2) ^ t * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1))) + (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by ring
    _ ≤ max 1 K * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) + (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by rw [h1]; linarith [h2]
    _ = (max 1 K + 1) * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by ring

theorem tendsto_F {c' d' : ℂ} (a b m : ℕ) (habm : a + b ≤ m) {z : ℂ} (hz : c' * z + d' ≠ 0) :
    Tendsto (fun σ : ℝ => ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ) * atom a b m σ z)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hW : ‖c' * z + d'‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h1 : Tendsto (fun σ : ℝ => (‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => (‖c' * z + d'‖ ^ 2) ^ t) 0 := Real.continuousAt_const_rpow hW
    have h2 : Tendsto (fun σ : ℝ => 2 * σ - 1) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
      have hcont : Continuous (fun σ : ℝ => 2 * σ - 1) := by fun_prop
      have := hcont.tendsto (1 / 2 : ℝ)
      rw [show (2 * (1 / 2 : ℝ) - 1) = 0 by norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := hc.tendsto.comp h2
    rw [Real.rpow_zero] at h3
    exact h3
  have h4 : Tendsto (fun σ : ℝ => ‖((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)‖) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    have := (tendsto_sub_nhds_zero_iff.mpr h1).norm
    rwa [norm_zero] at this
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [norm_mul, Complex.norm_real]
  refine mul_le_of_le_one_right (norm_nonneg _) ((norm_atom_le a b m habm σ z).trans ?_)
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg ‖z‖]) (by linarith)

theorem integrable_bound (C : ℝ) : Integrable fun z : ℂ => C * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (this.congr (ae_of_all _ fun z => ?_)).const_mul C
  norm_num

theorem main (c' d' : ℂ) (h : c' ≠ 0 ∨ d' ≠ 0) (a b m : ℕ) (habm : a + b ≤ m) :
    Tendsto (fun σ : ℝ =>
        ∫ z : ℂ, ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ) * atom a b m σ z)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hIoc : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), σ ∈ Set.Ioc (1 / 2 : ℝ) 1 := Ioc_mem_nhdsGT (by norm_num)
  have hae : ∀ᵐ z : ℂ, c' * z + d' ≠ 0 := by
    rcases eq_or_ne c' 0 with hc | hc
    · refine ae_of_all _ fun z => ?_
      rw [hc, zero_mul, zero_add]
      exact h.resolve_left (not_not.mpr hc)
    · have hsub : {z : ℂ | ¬(c' * z + d' ≠ 0)} ⊆ {-d' / c'} := fun z hz => by
        simp only [Set.mem_ofPred_eq, not_not] at hz
        rw [Set.mem_singleton_iff, eq_div_iff hc]
        linear_combination hz
      exact ae_iff.2 (measure_mono_null hsub (measure_singleton _))
  rw [show (0 : ℂ) = ∫ _ : ℂ, (0 : ℂ) by simp]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => (max 1 (‖c'‖ ^ 2 + ‖d'‖ ^ 2) + 1) * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ))) ?_ ?_ ?_ ?_
  · filter_upwards [hIoc] with σ hσ
    have ht0 : 0 ≤ 2 * σ - 1 := by linarith [hσ.1]
    exact (Continuous.mul (Complex.continuous_ofReal.comp
      ((Continuous.rpow_const (by fun_prop) fun z => Or.inr ht0).sub continuous_const))
      (continuous_atom a b m σ)).aestronglyMeasurable
  · filter_upwards [hIoc] with σ hσ
    exact ae_of_all _ fun z => norm_F_le a b m habm hσ.1 hσ.2 z
  · exact integrable_bound _
  · filter_upwards [hae] with z hz
    exact tendsto_F a b m habm hz

end ComplexAtomLimit

theorem tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
    (c' d' : ℂ) (_h : c' ≠ 0 ∨ d' ≠ 0) (a b m : ℕ) (_habm : a + b ≤ m) :
    Tendsto (fun σ : ℝ =>
        ∫ z : ℂ, ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
          * (z ^ a * (starRingEnd ℂ) z ^ b
              * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) :=
  ComplexAtomLimit.main c' d' _h a b m _habm

/-! ### The real place: the same limit -/
namespace RealAtomLimit

def atom (k : ℤ) (σ x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))

theorem norm_phase (x : ℝ) : ‖(((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have h1 : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp; ring
  have h2 : Real.sqrt (1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'
  rw [norm_div, h1, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self h2]

theorem norm_atom (k : ℤ) (σ x : ℝ) : ‖atom k σ x‖ = (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
  rw [atom, norm_mul, norm_zpow, norm_phase, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  congr 1
  simp

theorem continuous_phase : Continuous fun x : ℝ => (((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'

theorem continuous_atom (k : ℤ) (σ : ℝ) : Continuous (atom k σ) := by
  unfold atom
  refine Continuous.mul (continuous_phase.zpow₀ k fun x => Or.inl ?_) ?_
  · intro h
    have := norm_phase x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · refine Continuous.cpow (by fun_prop) continuous_const fun x => ?_
    exact_mod_cast Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

theorem sq_le (c' d' x : ℝ) : (c' * x + d') ^ 2 ≤ (c' ^ 2 + d' ^ 2) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (c' - d' * x)]

theorem norm_F_le {c' d' : ℝ} (k : ℤ) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (x : ℝ) :
    ‖((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x‖
      ≤ (max 1 (c' ^ 2 + d' ^ 2) + 1) * (1 + x ^ 2)⁻¹ := by
  set t : ℝ := σ - 1 / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  set K : ℝ := c' ^ 2 + d' ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hX : 0 < 1 + x ^ 2 := one_add_sq_pos x
  rw [norm_mul, Complex.norm_real, norm_atom]
  have hWt : ((c' * x + d') ^ 2) ^ t ≤ max 1 K * (1 + x ^ 2) ^ t := by
    calc ((c' * x + d') ^ 2) ^ t ≤ (K * (1 + x ^ 2)) ^ t := Real.rpow_le_rpow (sq_nonneg _) (sq_le c' d' x) ht0
      _ = K ^ t * (1 + x ^ 2) ^ t := Real.mul_rpow hK0 hX.le
      _ ≤ max 1 K * (1 + x ^ 2) ^ t :=
          mul_le_mul_of_nonneg_right (rpow_le_max K t hK0 ht0 ht1) (Real.rpow_nonneg hX.le _)
  have habs : ‖((c' * x + d') ^ 2) ^ t - 1‖ ≤ ((c' * x + d') ^ 2) ^ t + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), norm_one]
  have h1 : (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) = (1 + x ^ 2)⁻¹ := by
    rw [← Real.rpow_add hX, ← Real.rpow_neg_one]; congr 1; rw [ht]; ring
  have h2 : (1 + x ^ 2) ^ (-(σ + 1 / 2)) ≤ (1 + x ^ 2)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (by linarith)
  have hpos : 0 ≤ (1 + x ^ 2) ^ (-(σ + 1 / 2)) := Real.rpow_nonneg hX.le _
  have hM0 : 0 ≤ max 1 K := le_trans zero_le_one (le_max_left _ _)
  calc ‖((c' * x + d') ^ 2) ^ t - 1‖ * (1 + x ^ 2) ^ (-(σ + 1 / 2))
      ≤ (max 1 K * (1 + x ^ 2) ^ t + 1) * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
        mul_le_mul_of_nonneg_right (habs.trans (by linarith [hWt])) hpos
    _ = max 1 K * ((1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2))) + (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by ring
    _ ≤ max 1 K * (1 + x ^ 2)⁻¹ + (1 + x ^ 2)⁻¹ := by rw [h1]; linarith [h2]
    _ = (max 1 K + 1) * (1 + x ^ 2)⁻¹ := by ring

theorem tendsto_F {c' d' : ℝ} (k : ℤ) {x : ℝ} (hx : c' * x + d' ≠ 0) :
    Tendsto (fun σ : ℝ => ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hW : (c' * x + d') ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h1 : Tendsto (fun σ : ℝ => ((c' * x + d') ^ 2) ^ (σ - 1 / 2)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => ((c' * x + d') ^ 2) ^ t) 0 := Real.continuousAt_const_rpow hW
    have h2 : Tendsto (fun σ : ℝ => σ - 1 / 2) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun σ : ℝ => σ - 1 / 2) (𝓝 (1 / 2 : ℝ)) (𝓝 ((1 / 2 : ℝ) - 1 / 2)) := tendsto_id.sub_const _
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := hc.tendsto.comp h2
    rw [Real.rpow_zero] at h3
    exact h3
  have h4 : Tendsto (fun σ : ℝ => ‖(((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ)‖) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    have := (tendsto_sub_nhds_zero_iff.mpr h1).norm
    rwa [norm_zero] at this
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [norm_mul, Complex.norm_real, norm_atom]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)

theorem main (c' d' : ℝ) (h : c' ≠ 0 ∨ d' ≠ 0) (k : ℤ) :
    Tendsto (fun σ : ℝ =>
        ∫ x : ℝ, ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hIoc : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), σ ∈ Set.Ioc (1 / 2 : ℝ) 1 := Ioc_mem_nhdsGT (by norm_num)
  have hae : ∀ᵐ x : ℝ, c' * x + d' ≠ 0 := by
    rcases eq_or_ne c' 0 with hc | hc
    · refine ae_of_all _ fun x => ?_
      rw [hc, zero_mul, zero_add]
      exact h.resolve_left (not_not.mpr hc)
    · have hsub : {x : ℝ | ¬(c' * x + d' ≠ 0)} ⊆ {-d' / c'} := fun x hx => by
        simp only [Set.mem_ofPred_eq, not_not] at hx
        rw [Set.mem_singleton_iff, eq_div_iff hc]
        linarith
      exact ae_iff.2 (measure_mono_null hsub (measure_singleton _))
  rw [show (0 : ℂ) = ∫ _ : ℝ, (0 : ℂ) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (max 1 (c' ^ 2 + d' ^ 2) + 1) * (1 + x ^ 2)⁻¹)
    ?_ ?_ ?_ ?_
  · filter_upwards [hIoc] with σ hσ
    have ht0 : 0 ≤ σ - 1 / 2 := by linarith [hσ.1]
    exact (Continuous.mul (Complex.continuous_ofReal.comp
      ((Continuous.rpow_const (by fun_prop) fun x => Or.inr ht0).sub continuous_const)) (continuous_atom k σ)).aestronglyMeasurable
  · filter_upwards [hIoc] with σ hσ
    exact ae_of_all _ fun x => norm_F_le k hσ.1 hσ.2 x
  · exact integrable_inv_one_add_sq.const_mul _
  · filter_upwards [hae] with x hx
    exact tendsto_F k hx

end RealAtomLimit

theorem tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
    (c' d' : ℝ) (_h : c' ≠ 0 ∨ d' ≠ 0) (k : ℤ) :
    Tendsto (fun σ : ℝ =>
        ∫ x : ℝ, ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
          * (((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
              * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) :=
  RealAtomLimit.main c' d' _h k

/-! ### The product bound on the strip `1/2 < σ ≤ 1` -/
namespace MixedSpaceBound

open scoped Classical

private theorem real_bound (σ : ℝ) (hσ : 1 / 2 < σ) (k : ℤ) (x : ℝ) :
    ‖((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))‖
      ≤ (1 + ‖x‖ ^ 2) ^ (-(2 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : Real.sqrt (1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hunit : ‖(((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hn : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
      have h2 : ‖((x : ℝ) : ℂ) - Complex.I‖ ^ 2 = 1 + x ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      rw [← Real.sqrt_sq (norm_nonneg _), h2]
    rw [hn, div_self hsq]
  rw [norm_mul, norm_zpow, hunit, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-((σ : ℂ) + 1 / 2)).re = -(σ + 1 / 2) := by simp
  rw [hre, Real.norm_eq_abs, sq_abs]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg x]) (by linarith)

private theorem cx_bound (σ : ℝ) (hσ : 1 / 2 < σ) (a b m : ℕ) (h : a + b ≤ m) (z : ℂ) :
    ‖z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)‖
      ≤ (1 + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hge : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := by linarith [sq_nonneg ‖z‖]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-(2 * (σ : ℂ) + 1) - (m : ℂ) / 2).re = -(2 * σ + 1) - (m : ℝ) / 2 := by simp
  rw [hre, ← pow_add]

  have h1 : ‖z‖ ^ (a + b) ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
    have hz : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (norm_nonneg _) hpos.le]; linarith
    calc ‖z‖ ^ (a + b) ≤ ((1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ = (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; congr 1; ring
      _ ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hge (by gcongr)
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2)
      ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpos.le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by rw [← Real.rpow_add hpos]; congr 1; ring
    _ ≤ (1 + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hge (by linarith)

private theorem int_real : Integrable (fun t : ℝ => (1 + ‖t‖ ^ 2) ^ (-(2 : ℝ) / 2)) (volume : Measure ℝ) :=
  integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2) (by rw [Module.finrank_self]; norm_num)

private theorem int_cx : Integrable (fun t : ℂ => (1 + ‖t‖ ^ 2) ^ (-(4 : ℝ) / 2)) (volume : Measure ℂ) :=
  integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4) (by rw [Complex.finrank_real_complex]; norm_num)

private def maj (F : Type) [Field F] [NumberField F] (y : mixedEmbedding.mixedSpace F) : ℝ :=
  (∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖y.1 i‖ ^ 2) ^ (-(2 : ℝ) / 2)) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + ‖y.2 w‖ ^ 2) ^ (-(4 : ℝ) / 2)

private theorem integrable_maj (F : Type) [Field F] [NumberField F] :
    Integrable (maj F) ((volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)).prod
      (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ))) := by
  have h1 := Integrable.fintype_prod (ι := {w : InfinitePlace F // w.IsReal}) (μ := fun _ => (volume : Measure ℝ))
    (f := fun (_ : {w : InfinitePlace F // w.IsReal}) (t : ℝ) => (1 + ‖t‖ ^ 2) ^ (-(2 : ℝ) / 2)) (fun _ => int_real)
  have h2 := Integrable.fintype_prod (ι := {w : InfinitePlace F // w.IsComplex}) (μ := fun _ => (volume : Measure ℂ))
    (f := fun (_ : {w : InfinitePlace F // w.IsComplex}) (t : ℂ) => (1 + ‖t‖ ^ 2) ^ (-(4 : ℝ) / 2)) (fun _ => int_cx)
  have h := Integrable.mul_prod h1 h2
  unfold maj
  exact h

theorem main (F : Type) [Field F] [NumberField F]
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
      ‖∫ y : mixedEmbedding.mixedSpace F,
          (∏ i : {w : InfinitePlace F // w.IsReal},
              ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
                * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
                * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((abm w).2.2 : ℂ) / 2))‖ ≤ C := by
  refine ⟨∫ y, maj F y, fun σ hσ _ => ?_⟩
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (integrable_maj F) (Filter.Eventually.of_forall fun y => ?_))
  dsimp only
  rw [norm_mul, norm_prod, norm_prod]
  unfold maj
  refine mul_le_mul (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => real_bound σ hσ (kdat i) (y.1 i))
    (Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) fun w _ => cx_bound σ hσ _ _ _ (habm w) (y.2 w))
    (Finset.prod_nonneg fun w _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _)

end MixedSpaceBound

open scoped Classical in
theorem exists_bound_norm_integral_mixedSpace_archAtom_prod
    (F : Type) [Field F] [NumberField F]
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (_habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
      ‖∫ y : mixedEmbedding.mixedSpace F,
          (∏ i : {w : InfinitePlace F // w.IsReal},
              ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
                * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
                * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((abm w).2.2 : ℂ) / 2))‖ ≤ C :=
  MixedSpaceBound.main F kdat abm _habm

end LocalIntertwining
end AutomorphicForm
