/-
  The ideal-sum analytic block of the Frobenius-density input (S7-II): finiteness
  of `idealSum K s` for `1 < s` and the residue test
  `(s - 1) * idealSum K s → dedekindZeta_residue K` as `s → 1⁺`.

  The Dedekind-zeta comparison chain (`zetaTerm_nonneg`,
  `tendsto_sum_idealCount_div`, `isBigO_sum_of_tendsto_div`,
  `LSeriesSummable_idealCount`, `term_eq_ofReal_zetaTerm`, `summable_zetaTerm`,
  `NormFiber`, `normFiberEquiv`, `tsum_normFiber`, `tsum_equiv'`,
  `idealSum_eq_tsum_zetaTerm`) is imported from the H1 `Basic.lean`; only the two
  `toReal`/`dedekindZeta` bridges `dedekindZeta_eq_ofReal_tsum` and
  `idealSum_toReal_eq` are added here.

  Transcribed from the pinned FLT solution files (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean`,
  `P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean`).
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta

set_option autoImplicit false

open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
open scoped ENNReal Topology

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

private lemma dedekindZeta_eq_ofReal_tsum (s : ℝ) :
    dedekindZeta K s = ((∑' n, zetaTerm K s n : ℝ) : ℂ) := by
  rw [dedekindZeta, LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => term_eq_ofReal_zetaTerm K s n

private lemma idealSum_toReal_eq {s : ℝ} (hs : 1 < s) :
    (idealSum K s).toReal = ∑' n, zetaTerm K s n := by
  rw [idealSum_eq_tsum_zetaTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (zetaTerm_nonneg K s) (summable_zetaTerm K hs),
    ENNReal.toReal_ofReal]
  exact tsum_nonneg (zetaTerm_nonneg K s)

theorem idealSum_ne_top (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by
  rw [FrobeniusDensity.idealSum_eq_tsum_zetaTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (FrobeniusDensity.zetaTerm_nonneg K s)
      (FrobeniusDensity.summable_zetaTerm K hs)]
  exact ENNReal.ofReal_ne_top

theorem tendsto_sub_one_mul_idealSum_test (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by
  rw [← Filter.tendsto_ofReal_iff]
  refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [idealSum_toReal_eq K hs, dedekindZeta_eq_ofReal_tsum K s]
  push_cast
  ring

end FrobeniusDensity
