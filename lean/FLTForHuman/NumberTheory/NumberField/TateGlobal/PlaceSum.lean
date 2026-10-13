/-
  The place sum: the ideal `underZ v = v.asIdeal.under ℤ`, its absolute norm,
  the bound `card_filter_underZ_le` on the fibres of `underZ` over a fixed
  rational ideal, the identification `int_ideal_eq_span_absNorm` of a rational
  ideal with the span of its absolute norm, and the convergence
  `summable_absNorm_rpow_neg` for `σ > 1`.

  Transcribed from the pin's `Fold_PlaceSum` section (`NumberField.TateGlobal`
  block), declared lines 4741-4826 of file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped.  No file-wide option
  beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.EulerBookkeeping
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.RamificationInertia.Basic

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_PlaceSum

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type*} [Field F] [NumberField F]

-- pin: underZ (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4741)
abbrev underZ (v : HeightOneSpectrum (𝓞 F)) : Ideal ℤ := v.asIdeal.under ℤ

-- pin: absNorm_ne_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4743)
theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

-- pin: underZ_ne_bot (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4747)
theorem underZ_ne_bot (v : HeightOneSpectrum (𝓞 F)) : underZ v ≠ ⊥ := by
  intro h
  have hmem : ((Ideal.absNorm v.asIdeal : ℤ)) ∈ underZ v := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem v.asIdeal
  rw [h, Ideal.mem_bot] at hmem
  exact absNorm_ne_zero v (by exact_mod_cast hmem)

-- pin: absNorm_underZ_dvd (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4755)
theorem absNorm_underZ_dvd (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (underZ v) ∣ Ideal.absNorm v.asIdeal := by
  have hinj : Function.Injective (Ideal.quotientMap v.asIdeal (algebraMap ℤ (𝓞 F)) le_rfl) :=
    Ideal.quotientMap_injective
  have h := AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap v.asIdeal (algebraMap ℤ (𝓞 F)) le_rfl).toAddMonoidHom hinj
  rwa [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]

-- pin: absNorm_underZ_pos (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4763)
theorem absNorm_underZ_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm (underZ v) := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact underZ_ne_bot v

-- pin: absNorm_underZ_le (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4767)
theorem absNorm_underZ_le (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm (underZ v) ≤ Ideal.absNorm v.asIdeal :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_ne_zero v)) (absNorm_underZ_dvd v)

set_option linter.style.haveILetI false in
-- The `haveI` on `q.IsMaximal` is load-bearing: it is the `IsPrime` instance
-- for the ramification/inertia degree terms and for
-- `IsDedekindDomain.mem_primesOverFinset_iff`, so the style linter is disabled
-- for this declaration only.
-- pin: card_filter_underZ_le (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4770)
theorem card_filter_underZ_le [DecidableEq (Ideal ℤ)] (U : Finset (HeightOneSpectrum (𝓞 F))) (q : Ideal ℤ)
    (hq : ∃ v ∈ U, underZ v = q) :
    (U.filter fun v => underZ v = q).card ≤ Module.finrank ℚ F := by
  obtain ⟨v₀, _, hv₀⟩ := hq
  haveI : v₀.asIdeal.IsMaximal := v₀.isPrime.isMaximal v₀.ne_bot
  haveI : q.IsMaximal := hv₀ ▸ (Ideal.IsMaximal.under ℤ v₀.asIdeal)
  have hq0 : q ≠ ⊥ := hv₀ ▸ underZ_ne_bot v₀
  -- `Ideal.card_primesOverFinset_le_finrank` is deprecated in v4.34.0; the bound is
  -- re-derived from `Ideal.sum_ramification_inertia_eq_finrank`, whose terms are `≥ 1`.
  have hcard : (IsDedekindDomain.primesOverFinset q (𝓞 F)).card
      = Fintype.card (q.primesOver (𝓞 F)) := by
    rw [← Set.ncard_coe_finset (IsDedekindDomain.primesOverFinset q (𝓞 F)),
      IsDedekindDomain.coe_primesOverFinset (p := q) hq0 (𝓞 F), Set.fintypeCard_eq_ncard]
  have hbound : (IsDedekindDomain.primesOverFinset q (𝓞 F)).card ≤ Module.finrank ℚ F := by
    rw [hcard, ← RingOfIntegers.rank (K := F)]
    calc Fintype.card (q.primesOver (𝓞 F))
        = ∑ _ : q.primesOver (𝓞 F), 1 := by simp
      _ ≤ ∑ Q : q.primesOver (𝓞 F), Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ := by
          refine Finset.sum_le_sum fun Q _ => ?_
          exact Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero (Ideal.ramificationIdx_pos (q := Q.1) (R := ℤ)).ne'
              (Ideal.inertiaDeg_pos (q := Q.1) (R := ℤ)).ne')
      _ = Module.finrank ℤ (𝓞 F) :=
          Ideal.sum_ramification_inertia_eq_finrank (p := q) (S := 𝓞 F)
  refine le_trans ?_ hbound
  refine Finset.card_le_card_of_injOn (fun v => v.asIdeal) (fun v hv => ?_) ?_
  · rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
    exact ⟨v.isPrime, ⟨hv.2.symm⟩⟩
  · intro v _ w _ h
    exact HeightOneSpectrum.ext h

-- pin: int_ideal_eq_span_absNorm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4785)
theorem int_ideal_eq_span_absNorm (q : Ideal ℤ) : q = Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)} := by
  set g : ℤ := Submodule.IsPrincipal.generator q with hg
  have hq : q = Ideal.span {g} := (Submodule.IsPrincipal.span_singleton_generator q).symm
  rw [hq, Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply, Int.span_natAbs]

-- pin: summable_absNorm_rpow_neg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4790)
theorem summable_absNorm_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  classical
  set g : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hgs : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hdecay : ∀ v : HeightOneSpectrum (𝓞 F),
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ g (Ideal.absNorm (underZ v)) := by
    intro v
    refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith)
    · exact_mod_cast absNorm_underZ_pos v
    · exact_mod_cast absNorm_underZ_le v
  refine summable_of_sum_le (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c := Module.finrank ℚ F * ∑' n, g n)
    fun U => ?_
  set key : HeightOneSpectrum (𝓞 F) → Ideal ℤ := underZ with hkey
  calc ∑ v ∈ U, (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)
      ≤ ∑ v ∈ U, g (Ideal.absNorm (key v)) := Finset.sum_le_sum fun v _ => hdecay v
    _ = ∑ q ∈ U.image key, ((U.filter fun v => key v = q).card : ℝ) * g (Ideal.absNorm q) := by
        rw [Finset.sum_comp (fun q : Ideal ℤ => g (Ideal.absNorm q)) key]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [nsmul_eq_mul]
    _ ≤ ∑ q ∈ U.image key, (Module.finrank ℚ F : ℝ) * g (Ideal.absNorm q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_underZ_le U q ⟨v, hv, hvq⟩) (hg0 _)
    _ = (Module.finrank ℚ F : ℝ) * ∑ q ∈ U.image key, g (Ideal.absNorm q) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑ n ∈ (U.image key).image Ideal.absNorm, g n := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hinj : Set.InjOn (fun q : Ideal ℤ => Ideal.absNorm q) ↑(U.image key) := by
          intro q _ q' _ h
          rw [int_ideal_eq_span_absNorm q, int_ideal_eq_span_absNorm q']
          simp only at h
          rw [h]
        exact le_of_eq (Finset.sum_image hinj).symm
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑' n, g n :=
        mul_le_mul_of_nonneg_left (hgs.sum_le_tsum _ fun n _ => hg0 n) (Nat.cast_nonneg _)

end NumberField.TateGlobal

end

end Fold_PlaceSum
