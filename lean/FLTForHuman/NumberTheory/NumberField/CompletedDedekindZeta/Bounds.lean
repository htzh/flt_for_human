/-
  The effective bounds, and the assembled package.

  This is wave 9, the last development module of the `completedDedekindZeta`
  package.  It carries the growth estimates behind the two `Prop` obligations left
  open by waves 7 and 8, and the package headline itself:

  * `t16`, the right-half-plane bound on `ξ`: the majorant `zetaMajorant` of the
    Dedekind zeta series at `3/2`, the Gamma growth constant `gammaGrowthConstant`,
    the discriminant constant `discrGrowthConstant` and their assembly
    `xiRightHalfBoundConstant`, giving `xiRightHalfBound_holds` and, composed with
    wave 8's strip bound, `xiOrderOneHadamard_holds`;
  * `t43`, the superlinearity `completedDedekindZeta_realSuperlinear`: the Stirling
    lower bound (`stirlingConstant`, `stirling_le_log_factorial`), the Gamma lower
    bounds `log_norm_Gammaℝ_ge`/`log_norm_Gammaℂ_ge`, the non-vanishing
    `one_le_norm_dedekindZeta_ofReal` of the Dedekind zeta function on `(1, ∞)`,
    and the assembly `completedDedekindZeta_realSuperlinear_holds`;
  * `exists_completedDedekindZeta_package`, the pin's `solution`: the composition of
    the five obligations, and the statement the façade exposes.

  Transcribed from
  `P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean:6934–7555`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean),
  the pin's `FLT.Gapsw80T16XiRightHalfBoundProof` and
  `FLT.Gapsw80T43CompletedZetaRealSuperlinearProof` blocks.  The pin's obligation
  prefixes and per-obligation namespaces are dropped; every declaration carries the
  pin's own name and line in the `-- pin:` comment above it (playbook §2.3, §4).

  The pin's file-wide `set_option maxHeartbeats 6400000` and its per-declaration
  `set_option maxHeartbeats 16000000 in` before `gapsw80_t43_SL_closed` are not
  transcribed; the port's global cap is `4000000`.  Proofs are adapted to mathlib
  `v4.34.0`.  The pin's `solution` is named `exists_completedDedekindZeta_package`
  here; the façade `FLTForHuman/NumberTheory/NumberField/CompletedDedekindZeta.lean`
  states it at the pin wrapper's name.
-/
import FLTForHuman.NumberTheory.NumberField.CompletedDedekindZeta.Hadamard
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.InfiniteSum.Order

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


-- pin: gapsw80_t16_re_div_two (S_NumberField_exists_completedDedekindZeta_package.lean:6934)
theorem re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]; simp [Complex.normSq_ofNat]; ring

-- pin: gapsw80_t16_one_le_abs_discr (S_NumberField_exists_completedDedekindZeta_package.lean:6937)
theorem one_le_abs_discr : (1:ℝ) ≤ |(discr K : ℝ)| := by
  have h : (0:ℤ) < |discr K| := abs_pos.mpr (NumberField.discr_ne_zero K)
  have h1 : (1:ℤ) ≤ |discr K| := h
  calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_cast
    _ ≤ (|discr K| : ℝ) := by exact_mod_cast h1
    _ = |(discr K : ℝ)| := by rfl

-- pin: gapsw80_t16_Gammaℂ_ne_zero (S_NumberField_exists_completedDedekindZeta_package.lean:6944)
theorem Gammaℂ_ne_zero {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
    (Complex.Gamma_ne_zero (fun m hm => by
      have : s.re = (-(m:ℂ)).re := by rw [hm]
      simp at this; linarith))
  refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
  exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

-- pin: gapsw80_t16_zetaCoeff (S_NumberField_exists_completedDedekindZeta_package.lean:6954)
noncomputable def dedekindZetaCoeff (n : ℕ) : ℂ :=
  (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)

-- pin: gapsw80_t16_Mzeta (S_NumberField_exists_completedDedekindZeta_package.lean:6957)
noncomputable def zetaMajorant : ℝ :=
  ∑' n, ‖LSeries.term (dedekindZetaCoeff K) ((3/2 : ℝ) : ℂ) n‖

-- pin: gapsw80_t16_Mzeta_summable (S_NumberField_exists_completedDedekindZeta_package.lean:6960)
theorem summable_zetaMajorant :
    Summable (fun n => ‖LSeries.term (dedekindZetaCoeff K) ((3/2 : ℝ) : ℂ) n‖) :=
  (LSeriesSummable_dedekindZeta K
    (s := ((3/2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num)).norm

-- pin: gapsw80_t16_term_norm_le (S_NumberField_exists_completedDedekindZeta_package.lean:6965)
theorem term_norm_le_zetaMajorant {s : ℂ} (hs : 3/2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (dedekindZetaCoeff K) s n‖
      ≤ ‖LSeries.term (dedekindZetaCoeff K) ((3/2 : ℝ) : ℂ) n‖ := by
  have _em := Classical.em
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [LSeries.term_zero]
  · have hn1 : 1 ≤ (n:ℝ) := Nat.one_le_cast.mpr hpos
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hpos.ne', ite_eq_right hpos.ne',
      Complex.ofReal_re]
    exact div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos (by exact_mod_cast hpos) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)

-- pin: gapsw80_t16_norm_sum_partialZeta_le (S_NumberField_exists_completedDedekindZeta_package.lean:6978)
theorem norm_sum_partialDedekindZeta_le_zetaMajorant {s : ℂ} (hs : 3/2 ≤ s.re) :
    ‖∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s‖
      ≤ zetaMajorant K := by
  have _em := Classical.em
  have h1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [sum_partialDedekindZeta_eq_dedekindZeta K h1]

  have hsum := (summable_zetaMajorant K).of_nonneg_of_le
    (fun _ => norm_nonneg _) (term_norm_le_zetaMajorant K hs)
  unfold NumberField.dedekindZeta
  calc ‖LSeries _ s‖
      ≤ ∑' n, ‖LSeries.term (dedekindZetaCoeff K) s n‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ zetaMajorant K :=
        hasSum_le (term_norm_le_zetaMajorant K hs) hsum.hasSum
          (summable_zetaMajorant K).hasSum

-- pin: gapsw80_t16_log_norm_Gamma_half_le (S_NumberField_exists_completedDedekindZeta_package.lean:6995)
theorem log_norm_Gamma_div_two_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gamma (s / 2)‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hns
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := one_le_norm_mul_log_norm hns
  have hshalf_norm : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [norm_div]; simp
  rcases le_or_gt 2 s.re with hge2 | hlt2
  ·
    have hre : 1 ≤ (s / 2).re := by
      rw [re_div_two]; linarith
    have hstep := log_norm_Gamma_le_norm_mul_log_norm hre
    refine hstep.trans ?_
    rw [hshalf_norm]
    have hhalf : ‖s‖ / 2 ≤ ‖s‖ := by linarith
    have hh1 : 1 ≤ ‖s‖ / 2 := by linarith
    exact monotoneOn_mul_log (Set.mem_Ici.mpr hh1)
      (Set.mem_Ici.mpr (by linarith)) hhalf
  ·
    have hshalf_ne : s / 2 ≠ 0 := by
      intro h; rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact (ne_zero_and_ne_one_of_two_le_norm hns).1 h
      · exact two_ne_zero h
    have hshift : Complex.Gamma (s / 2) = Complex.Gamma (s / 2 + 1) / (s / 2) := by
      rw [eq_div_iff hshalf_ne, mul_comm (Complex.Gamma (s/2)) (s/2),
          Complex.Gamma_add_one (s / 2) hshalf_ne]
    have hre1 : 1 ≤ (s / 2 + 1).re := by
      rw [Complex.add_re, Complex.one_re, re_div_two]; linarith
    have hnorm1 : ‖s / 2 + 1‖ ≤ ‖s‖ := by
      calc ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by
            have := norm_add_le (s/2) 1; rwa [norm_one] at this
        _ = ‖s‖ / 2 + 1 := by rw [hshalf_norm]
        _ ≤ ‖s‖ := by linarith
    have h1le1 : 1 ≤ ‖s / 2 + 1‖ :=
      le_trans (by exact_mod_cast hre1) (Complex.re_le_norm _)
    have hlogG1 : Real.log ‖Complex.Gamma (s / 2 + 1)‖
        ≤ ‖s / 2 + 1‖ * Real.log ‖s / 2 + 1‖ :=
      log_norm_Gamma_le_norm_mul_log_norm hre1
    have hlogG1' : Real.log ‖Complex.Gamma (s / 2 + 1)‖ ≤ ‖s‖ * Real.log ‖s‖ :=
      hlogG1.trans (monotoneOn_mul_log (Set.mem_Ici.mpr h1le1)
        (Set.mem_Ici.mpr (by linarith)) hnorm1)

    have h1shalf : (1:ℝ) ≤ ‖s / 2‖ := by rw [hshalf_norm]; linarith
    have hlogs2 : -Real.log ‖s / 2‖ ≤ 0 :=
      neg_nonpos_of_nonneg (Real.log_nonneg h1shalf)
    rw [hshift, norm_div, Real.log_div
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => by
        have : (s/2+1).re = (-(m:ℂ)).re := by rw [hm]
        simp at this; linarith)))
      (by rw [hshalf_norm]; positivity)]
    linarith [hlogG1', hlogs2]

-- pin: gapsw80_t16_log_norm_Gammaℝ_le (S_NumberField_exists_completedDedekindZeta_package.lean:7049)
theorem log_norm_Gammaℝ_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gammaℝ s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      re_div_two, Complex.neg_re]
  have hπle : Real.log ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 0 := by
    rw [hπ, Real.log_rpow Real.pi_pos]
    have hlogπ : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (one_le_two.trans Real.two_le_pi)
    nlinarith
  rw [Complex.Gammaℝ_def, norm_mul,
    Real.log_mul (by rw [hπ]; positivity)
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => by
        have : (s/2).re = (-(m:ℂ)).re := by rw [hm]
        simp at this; linarith)))]
  linarith [log_norm_Gamma_div_two_le h32 hns, hπle]

-- pin: gapsw80_t16_log_norm_Gammaℂ_le (S_NumberField_exists_completedDedekindZeta_package.lean:7068)
theorem log_norm_Gammaℂ_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gammaℂ s‖ ≤ 2 * (‖s‖ * Real.log ‖s‖) := by
  have _em := Classical.em
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := one_le_norm_mul_log_norm hns
  have hre1 : 1 ≤ s.re := by linarith
  have hΓ := log_norm_Gamma_le_norm_mul_log_norm hre1
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have hpow : ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-s.re) := by
    have : ((2 * (↑Real.pi : ℂ)) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.neg_re]
  have hpow_le : Real.log ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ ≤ 0 := by
    rw [hpow, Real.log_rpow h2πpos]
    have hlog2π : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.two_le_pi])
    nlinarith
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m hm => by
    have : s.re = (-(m:ℂ)).re := by rw [hm]
    simp at this; linarith)
  have hpow_ne : ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ ≠ 0 := by rw [hpow]; positivity
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (by simp) hpow_ne) (norm_ne_zero_iff.mpr hΓne),
    Real.log_mul (by simp) hpow_ne]
  have hlog2' : Real.log ‖(2:ℂ)‖ = Real.log 2 := by simp
  linarith [hΓ, hpow_le, h1nml, hlog2]

-- pin: gapsw80_t16_CGamma (S_NumberField_exists_completedDedekindZeta_package.lean:7095)
noncomputable def gammaGrowthConstant : ℝ :=
  (nrRealPlaces K : ℝ) + 2 * (nrComplexPlaces K : ℝ)

-- pin: gapsw80_t16_log_norm_gammaFactor_le (S_NumberField_exists_completedDedekindZeta_package.lean:7098)
theorem log_norm_gammaFactor_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖gammaFactor K s‖
      ≤ gammaGrowthConstant K * (‖s‖ * Real.log ‖s‖) := by
  have _em := Classical.em
  have hnml : 0 ≤ ‖s‖ * Real.log ‖s‖ := norm_mul_log_norm_nonneg hns
  have hRne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hCne : Complex.Gammaℂ s ≠ 0 := Gammaℂ_ne_zero (by linarith)
  unfold gammaFactor gammaGrowthConstant
  rw [norm_mul, norm_pow, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hRne))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hCne)),
    Real.log_pow, Real.log_pow]
  have hR := log_norm_Gammaℝ_le h32 hns
  have hC := log_norm_Gammaℂ_le h32 hns
  have hRn : (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ s‖
      ≤ (nrRealPlaces K : ℝ) * (‖s‖ * Real.log ‖s‖) :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  have hCn : (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ s‖
      ≤ (nrComplexPlaces K : ℝ) * (2 * (‖s‖ * Real.log ‖s‖)) :=
    mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
  linarith

-- pin: gapsw80_t16_CDisc (S_NumberField_exists_completedDedekindZeta_package.lean:7121)
noncomputable def discrGrowthConstant : ℝ :=
  Real.log |(discr K : ℝ)| / (2 * Real.log 2)

-- pin: gapsw80_t16_log_norm_discrPow_le (S_NumberField_exists_completedDedekindZeta_package.lean:7124)
theorem log_norm_discrPow_le {s : ℂ} (hns : 2 ≤ ‖s‖) :
    Real.log ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖
      ≤ discrGrowthConstant K * (‖s‖ * Real.log ‖s‖) := by
  have _em := Classical.em
  have hD1 : (1:ℝ) ≤ |(discr K : ℝ)| := one_le_abs_discr K
  have hDpos : (0:ℝ) < |(discr K : ℝ)| := lt_of_lt_of_le one_pos hD1
  have hlogD : 0 ≤ Real.log |(discr K : ℝ)| := Real.log_nonneg hD1
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlogn2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hns
  have hsre : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hnspos : (0:ℝ) ≤ ‖s‖ := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hDpos),
    Real.log_rpow (by exact_mod_cast hDpos), re_div_two]
  unfold discrGrowthConstant
  have hkey : s.re * Real.log 2 * Real.log |(discr K : ℝ)|
      ≤ Real.log |(discr K : ℝ)| * (‖s‖ * Real.log ‖s‖) := by
    have := mul_le_mul hsre hlogn2 hlog2.le hnspos
    nlinarith
  calc s.re / 2 * Real.log |(discr K : ℝ)|
      = s.re * Real.log 2 * Real.log |(discr K : ℝ)| / (2 * Real.log 2) := by
        field_simp
  _ ≤ Real.log |(discr K : ℝ)| * (‖s‖ * Real.log ‖s‖) / (2 * Real.log 2) := by
        gcongr
  _ = Real.log |(discr K : ℝ)| / (2 * Real.log 2) * (‖s‖ * Real.log ‖s‖) := by ring

-- pin: gapsw80_t16_Cassem (S_NumberField_exists_completedDedekindZeta_package.lean:7149)
noncomputable def xiRightHalfBoundConstant : ℝ :=
  max (2 + discrGrowthConstant K + gammaGrowthConstant K
    + max (Real.log (zetaMajorant K)) 0) 0

-- pin: gapsw80_t16_Cassem_nonneg (S_NumberField_exists_completedDedekindZeta_package.lean:7153)
theorem xiRightHalfBoundConstant_nonneg : 0 ≤ xiRightHalfBoundConstant K := le_max_right _ _

-- pin: gapsw80_t16_xiRightHalfBound_proved (S_NumberField_exists_completedDedekindZeta_package.lean:7155)
theorem xiRightHalfBound_holds : xiRightHalfBound := by
  have _em := Classical.em
  intro K _ _
  refine ⟨xiRightHalfBoundConstant K, fun s h32 hns => ?_⟩
  have hnml : 0 ≤ ‖s‖ * Real.log ‖s‖ := norm_mul_log_norm_nonneg hns
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := one_le_norm_mul_log_norm hns
  have hCnn : 0 ≤ xiRightHalfBoundConstant K := xiRightHalfBoundConstant_nonneg K

  by_cases hξ0 : xi K s = 0
  · rw [hξ0, norm_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg hCnn (by linarith)) (Real.log_nonneg (by linarith))

  have h1 : 1 < s.re := lt_of_lt_of_le (by norm_num) h32
  obtain ⟨hs0, hs1⟩ := ne_zero_and_ne_one_of_two_le_norm hns
  rw [xi_eq K hs0 hs1, completedDedekindZeta_classSum_eq_sum K h1]

  have hsumne : ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s ≠ 0 := by
    intro habs
    apply hξ0
    rw [xi_eq K hs0 hs1, completedDedekindZeta_classSum_eq_sum K h1, habs]
    ring
  have hpoly_pos : (0:ℝ) < ‖s * (s - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.mpr hs0) (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))
  have hD1 : (1:ℝ) ≤ |(discr K : ℝ)| := one_le_abs_discr K
  have hDpow_pos : (0:ℝ) < ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast lt_of_lt_of_le one_pos hD1)]
    positivity
  have hGamma_pos : (0:ℝ) < ‖gammaFactor K s‖ := by
    unfold gammaFactor
    rw [norm_mul, norm_pow, norm_pow]
    refine mul_pos (pow_pos ?_ _) (pow_pos ?_ _)
    · exact norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    · exact norm_pos_iff.mpr (Gammaℂ_ne_zero (by linarith))
  have hsum_pos : (0:ℝ) < ‖∑ C, partialDedekindZeta K C s‖ :=
    norm_pos_iff.mpr hsumne

  rw [show s * (s - 1) * (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * gammaFactor K s
        * ∑ C, partialDedekindZeta K C s)
      = (s * (s - 1)) * (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2))
        * (gammaFactor K s)
        * (∑ C, partialDedekindZeta K C s) from by ring,
    norm_mul, norm_mul, norm_mul,
    Real.log_mul (by positivity) hsum_pos.ne',
    Real.log_mul (by positivity) hGamma_pos.ne',
    Real.log_mul hpoly_pos.ne' hDpow_pos.ne']

  have bPoly := log_norm_mul_sub_one_le_two_mul_norm_mul_log s hns
  have bDisc := log_norm_discrPow_le K hns
  have bGamma := log_norm_gammaFactor_le K h32 hns
  have bZeta : Real.log ‖∑ C, partialDedekindZeta K C s‖
      ≤ max (Real.log (zetaMajorant K)) 0 * (‖s‖ * Real.log ‖s‖) := by
    have h := norm_sum_partialDedekindZeta_le_zetaMajorant K h32
    calc Real.log ‖∑ C, partialDedekindZeta K C s‖
        ≤ Real.log (zetaMajorant K) :=
          Real.log_le_log hsum_pos h
      _ ≤ max (Real.log (zetaMajorant K)) 0 := le_max_left _ _
      _ = max (Real.log (zetaMajorant K)) 0 * 1 := (mul_one _).symm
      _ ≤ max (Real.log (zetaMajorant K)) 0 * (‖s‖ * Real.log ‖s‖) :=
          mul_le_mul_of_nonneg_left h1nml (le_max_right _ _)
  have hCexp : xiRightHalfBoundConstant K
      ≥ 2 + discrGrowthConstant K + gammaGrowthConstant K
        + max (Real.log (zetaMajorant K)) 0 := le_max_left _ _
  calc Real.log ‖s * (s - 1)‖ + Real.log ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖
        + Real.log ‖gammaFactor K s‖
        + Real.log ‖∑ C, partialDedekindZeta K C s‖
      ≤ 2 * ‖s‖ * Real.log ‖s‖
        + discrGrowthConstant K * (‖s‖ * Real.log ‖s‖)
        + gammaGrowthConstant K * (‖s‖ * Real.log ‖s‖)
        + max (Real.log (zetaMajorant K)) 0 * (‖s‖ * Real.log ‖s‖) := by
        linarith [bPoly, bDisc, bGamma, bZeta]
    _ = (2 + discrGrowthConstant K + gammaGrowthConstant K
          + max (Real.log (zetaMajorant K)) 0) * (‖s‖ * Real.log ‖s‖) := by ring
    _ ≤ xiRightHalfBoundConstant K * (‖s‖ * Real.log ‖s‖) :=
        mul_le_mul_of_nonneg_right hCexp hnml
    _ = xiRightHalfBoundConstant K * ‖s‖ * Real.log ‖s‖ := by ring

-- pin: gapsw80_t16_B1_closed (S_NumberField_exists_completedDedekindZeta_package.lean:7233)
theorem xiOrderOneHadamard_holds : xiOrderOneHadamard :=
  xiOrderOneHadamard_of_xiRightHalfBound xiRightHalfBound_holds

-- pin: gapsw80_t43_L₀ (S_NumberField_exists_completedDedekindZeta_package.lean:7263)
noncomputable def stirlingConstant : ℝ := 1 + 2 * Real.log (2 * Real.pi)

-- pin: gapsw80_t43_one_le_norm_discrPow (S_NumberField_exists_completedDedekindZeta_package.lean:7265)
theorem one_le_norm_discrPow (K : Type) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ := by
  rw [discr_coercion,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le one_pos (one_le_abs_discr K))]
  have hre : ((σ:ℂ) / 2).re = σ / 2 := by
    simp
  rw [hre]
  exact Real.one_le_rpow (one_le_abs_discr K) (by linarith)

-- pin: gapsw80_t43_norm_Gamma_nat_succ (S_NumberField_exists_completedDedekindZeta_package.lean:7276)
theorem norm_Gamma_natCast_succ (n : ℕ) :
    ‖Complex.Gamma ((n + 1 : ℕ) : ℂ)‖ = (n ! : ℝ) := by
  rw [show (((n + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  exact abs_of_pos (by exact_mod_cast n.factorial_pos)

-- pin: gapsw80_t43_one_le_norm_dedekindZeta_ofReal (S_NumberField_exists_completedDedekindZeta_package.lean:7284)
theorem one_le_norm_dedekindZeta_ofReal (K : Type) [Field K]
    [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ := by
  have hre : 1 < (σ:ℂ).re := by rwa [Complex.ofReal_re]
  have hsum : LSeriesSummable
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ:ℂ) :=
    LSeriesSummable_dedekindZeta K hre

  have hterm_re_nonneg : ∀ n,
      0 ≤ (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hcpow : (n:ℂ)^(σ:ℂ) = (((n:ℝ)^σ : ℝ):ℂ) := by
        rw [show ((n:ℕ):ℂ) = (((n:ℕ):ℝ):ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcpow, show ((Nat.card _ : ℕ):ℂ) = (((Nat.card _ : ℕ):ℝ):ℂ) from
          (Complex.ofReal_natCast _).symm, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity

  have hterm1_re :
      (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) 1).re = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp only [Nat.cast_one, Complex.one_cpow, div_one]
    have : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
      simp [Ideal.absNorm_eq_one_iff]
    rw [this]; simp

  have hHS_re : HasSum
      (fun n => (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re)
      (dedekindZeta K (σ:ℂ)).re :=
    Complex.hasSum_re hsum.hasSum
  calc (1:ℝ)
      = (LSeries.term _ (σ:ℂ) 1).re := hterm1_re.symm
    _ ≤ (dedekindZeta K (σ:ℂ)).re :=
        le_hasSum hHS_re 1 (fun n _ => hterm_re_nonneg n)
    _ ≤ ‖dedekindZeta K (σ:ℂ)‖ := Complex.re_le_norm _

-- pin: gapsw80_t43_log_pi_le (S_NumberField_exists_completedDedekindZeta_package.lean:7328)
theorem log_pi_le_two_mul_log_two_mul_pi : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := by
  have h1 : Real.log Real.pi ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_pos])
  have h2 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

-- pin: gapsw80_t43_stirling_core (S_NumberField_exists_completedDedekindZeta_package.lean:7335)
theorem stirling_le_log_factorial {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) := by
  have hlog_m : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have h2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have key := Stirling.le_log_factorial_stirling (Nat.one_le_iff_ne_zero.mp hm)
  linarith

-- pin: gapsw80_t43_log_norm_Gammaℝ_ge (S_NumberField_exists_completedDedekindZeta_package.lean:7344)
theorem log_norm_Gammaℝ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - stirlingConstant * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℝ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσ2 : σ / 2 = (m:ℝ) + 1 := by rw [hσ]; ring
  have hm1pos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have harg : ((σ:ℂ)/2) = ((m + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℝ (σ:ℂ)‖
      = Real.pi ^ (-((m:ℝ)+1)) * (m ! : ℝ) := by
    rw [Complex.Gammaℝ_def, norm_mul,
      show (-(σ:ℂ)/2) = -((σ:ℂ)/2) from by ring, harg,
      norm_Gamma_natCast_succ m,
      show (-((m+1:ℕ):ℂ)) = ((-((m:ℝ)+1) : ℝ):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re]
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast m.factorial_pos.ne'),
    Real.log_rpow Real.pi_pos]
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    stirling_le_log_factorial hm
  have hπ : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := log_pi_le_two_mul_log_two_mul_pi
  unfold stirlingConstant
  nlinarith [hm1pos]

-- pin: gapsw80_t43_log_norm_Gammaℂ_ge (S_NumberField_exists_completedDedekindZeta_package.lean:7368)
theorem log_norm_Gammaℂ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - stirlingConstant * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℂ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσnat : σ = ((2*m+1 : ℕ):ℝ) + 1 := by push_cast; rw [hσ]; ring
  have h2πpos : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have harg : ((σ:ℝ):ℂ) = (((2*m+1) + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℂ (σ:ℂ)‖
      = 2 * (2*Real.pi) ^ (-σ) * ((2*m+1)! : ℝ) := by
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul, harg,
      norm_Gamma_natCast_succ (2*m+1),
      show (-(((2*m+1)+1:ℕ):ℂ)) = (((-σ):ℝ):ℂ) from by rw [hσ]; push_cast; ring,
      show ((2:ℂ)*(Real.pi:ℂ)) = (((2*Real.pi:ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.ofReal_re]
    norm_num
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast (2*m+1).factorial_pos.ne'),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow h2πpos]

  have hfac_le : (m ! : ℝ) ≤ ((2*m+1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hlogfac : Real.log (m ! : ℝ) ≤ Real.log ((2*m+1)! : ℝ) :=
    Real.log_le_log (by exact_mod_cast m.factorial_pos) hfac_le
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    stirling_le_log_factorial hm
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  unfold stirlingConstant
  nlinarith

-- pin: gapsw80_t43_one_le_nrPlaces_sum (S_NumberField_exists_completedDedekindZeta_package.lean:7398)
theorem one_le_nrPlaces_sum (K : Type) [Field K] [NumberField K] :
    1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have hk : 1 ≤ nrRealPlaces K + 2 * nrComplexPlaces K := by
    rw [card_add_two_mul_card_eq_rank]; exact Module.finrank_pos
  omega

-- pin: gapsw80_t43_exists_m_superlinear (S_NumberField_exists_completedDedekindZeta_package.lean:7404)
theorem exists_mul_log_gt_mul (D : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ D * ((m:ℝ) + 1) < (m:ℝ) * Real.log m := by
  set D' := max D 0 with hD'
  have hD'0 : 0 ≤ D' := le_max_right _ _
  have hlog : ∀ᶠ m : ℕ in atTop, 2 * D' < Real.log (m:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (2*D')
  obtain ⟨m, hmD, hm2⟩ := (hlog.and (eventually_ge_atTop 2)).exists
  refine ⟨m, hm2, ?_⟩
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  calc D * ((m:ℝ) + 1)
      ≤ D' * ((m:ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ D' * (2 * (m:ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD'0
        have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        linarith
    _ = (2 * D') * (m:ℝ) := by ring
    _ < Real.log (m:ℝ) * (m:ℝ) := mul_lt_mul_of_pos_right hmD hm0
    _ = (m:ℝ) * Real.log m := by ring

-- pin: gapsw80_t43_SL_closed (S_NumberField_exists_completedDedekindZeta_package.lean:7426)
theorem completedDedekindZeta_realSuperlinear_holds : completedDedekindZeta_realSuperlinear := by
  have _em := Classical.em
  intro K _ _ C
  obtain ⟨m, hm2, hmD⟩ := exists_mul_log_gt_mul (2 * |C| + stirlingConstant)
  have hm1 : 1 ≤ m := by omega
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσdef
  have hσ4 : (4:ℝ) ≤ σ := by
    have : (2:ℝ) ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm1
    rw [hσdef]; linarith
  have hσ1 : (1:ℝ) < σ := by linarith
  have hσ0 : (0:ℝ) < σ := by linarith
  have hnorm_s : ‖(σ:ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos hσ0

  refine ⟨(σ:ℂ), ?_, ?_, ?_, ?_⟩
  · rw [hnorm_s]; linarith
  · exact_mod_cast hσ0.ne'
  · intro h; rw [Complex.ofReal_eq_one] at h; linarith

  have hre : (1:ℝ) < (σ:ℂ).re := by rwa [Complex.ofReal_re]

  set L : ℝ := (m:ℝ) * Real.log m - stirlingConstant * ((m:ℝ) + 1) with hLdef
  have hL_pos : 0 ≤ L := by
    have h2C : 0 ≤ 2 * |C| * ((m:ℝ)+1) := by positivity
    rw [hLdef]; linarith [hmD]
  have hCL : C * σ < L := by
    rw [hσdef, hLdef]
    have habs : C * (2 * ((m:ℝ)+1)) ≤ |C| * (2 * ((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith [hmD]

  rw [hnorm_s, completedDedekindZeta_classSum_eq_completedDedekindZeta K hre,
    completedDedekindZeta]
  refine lt_of_lt_of_le hCL ?_

  have hDge1 : (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    one_le_norm_discrPow K hσ0.le
  have hZge1 : (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ :=
    one_le_norm_dedekindZeta_ofReal K hσ1
  have hGRne : Complex.Gammaℝ (σ:ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; exact hσ0)
  have hGCne : Complex.Gammaℂ (σ:ℂ) ≠ 0 :=
    Gammaℂ_ne_zero (by rw [Complex.ofReal_re]; exact hσ0)
  have hGRpos : (0:ℝ) < ‖Complex.Gammaℝ (σ:ℂ)‖ := norm_pos_iff.mpr hGRne
  have hGCpos : (0:ℝ) < ‖Complex.Gammaℂ (σ:ℂ)‖ := norm_pos_iff.mpr hGCne
  have hGRL : L ≤ Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ := by
    rw [hLdef]; exact log_norm_Gammaℝ_ge hm1
  have hGCL : L ≤ Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ := by
    rw [hLdef]; exact log_norm_Gammaℂ_ge hm1
  have hs1 : ‖(σ:ℂ) - 1‖ = σ - 1 := by
    rw [show ((σ:ℂ) - 1) = (((σ - 1 : ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)

  simp only [norm_mul, norm_pow, hnorm_s, hs1]

  have hall_pos :
      (0:ℝ) < σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖) := by
    have : (0:ℝ) < σ - 1 := by linarith
    positivity

  rw [show σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖)
      = (σ * (σ - 1)) * ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖ by ring,
    Real.log_mul (by positivity) (by linarith [hZge1]),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by linarith [hDge1]),
    Real.log_pow, Real.log_pow]

  have hlog_ss1 : 0 ≤ Real.log (σ * (σ - 1)) :=
    Real.log_nonneg (by nlinarith)
  have hlogD : 0 ≤ Real.log ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    Real.log_nonneg hDge1
  have hlogZ : 0 ≤ Real.log ‖dedekindZeta K (σ:ℂ)‖ := Real.log_nonneg hZge1

  have hr1 : (nrRealPlaces K : ℝ) * L
      ≤ (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGRL (Nat.cast_nonneg _)
  have hr2 : (nrComplexPlaces K : ℝ) * L
      ≤ (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGCL (Nat.cast_nonneg _)
  have hrsum : (1:ℝ) ≤ (nrRealPlaces K : ℝ) + (nrComplexPlaces K : ℝ) := by
    exact_mod_cast one_le_nrPlaces_sum K
  nlinarith [mul_nonneg (Nat.cast_nonneg (nrRealPlaces K)) hL_pos,
    mul_nonneg (Nat.cast_nonneg (nrComplexPlaces K)) hL_pos]

-- pin: solution (S_NumberField_exists_completedDedekindZeta_package.lean:7532)
theorem exists_completedDedekindZeta_package (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) := by
  refine ⟨completedDedekindZeta_classSum K, ?_, ?_, ?_, xiOrderOneHadamard_holds K,
    xi_endpointNonvanishing_holds K, completedDedekindZeta_realSuperlinear_holds K⟩
  · exact differentiableOn_completedDedekindZeta_classSum K
  · exact fun s hs0 hs1 => completedDedekindZeta_classSum_functionalEquation K hs0 hs1
  · intro s hs
    rw [completedDedekindZeta_classSum_eq_completedDedekindZeta K hs]
    rfl


end

end NumberField.CompletedDedekindZeta
