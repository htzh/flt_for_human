/-
  The degree-one asymptotic chain of the Frobenius-density input (S7-II):
  summability of the degree-one terms `summable_degOne_term` and the
  log-pole asymptotic `degOneSum_add_log_isBigO`, obtained from
  `primeSum_toReal_add_log_isBigO` by subtracting the finite cut sum and the
  non-degree-one tail.

  Imported rather than re-proved: `primeSum_le_idealSum` (H1 `Basic.lean`),
  `toReal_term` (H1 `Basic.lean`), `one_le_cast_absNorm` and `primeSum_ne_top`
  (`PrimeSumAsymptotic.lean`), and `degOneSum_ne_top` (`PrimeSumSplit.lean`,
  the H1-deferred block ported once).

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_degOneSum_add_log_isBigO.lean`).
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeSumAsymptotic
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeSumSplit
import FLTForHuman.NumberTheory.FrobeniusDensity.IdealSum
import Mathlib.NumberTheory.RamificationInertia.Basic

set_option autoImplicit false

open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
open scoped ENNReal Topology

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

/-- `degOneSum_ne_top` is public in `PrimeSumSplit`; this is the pin-local
`primeSum_ne_top` restated against `1 < s` on top of the public form. -/
private lemma primeSum_ne_top_of_one_lt {s : ℝ} (hs : 1 < s) : primeSum K s ≠ ⊤ :=
  primeSum_ne_top (idealSum_ne_top K hs)

private lemma cutSum_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) : cutSum K S₀ s ≠ ⊤ := by
  have h1 : cutSum K S₀ s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K S₀ s]
    exact le_add_self.trans (self_le_add_right _ _)
  exact (h1.trans_lt ((primeSum_ne_top_of_one_lt K hs).lt_top)).ne

private lemma tailSum_ne_top {s : ℝ} (hs : 1 < s) : tailSum K s ≠ ⊤ := by
  have h1 : tailSum K s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K ∅ s]
    exact le_add_self
  exact (h1.trans_lt ((primeSum_ne_top_of_one_lt K hs).lt_top)).ne

private theorem tailConst_ne_top : tailConst ≠ ⊤ := by
  have hsummable : Summable (fun ℓ : ℕ => if ℓ.Prime then (((ℓ : ℝ) ^ 2)⁻¹) else 0) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
      (Real.summable_nat_pow_inv.mpr one_lt_two)
    · split <;> positivity
    · split
      · exact le_rfl
      · positivity
  have hpt : ∀ ℓ : ℕ, (if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0)
      = ENNReal.ofReal (if ℓ.Prime then (((ℓ : ℝ) ^ 2)⁻¹) else 0) := by
    intro ℓ
    by_cases hℓ : ℓ.Prime
    · have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
      rw [ite_eq_left hℓ, ite_eq_left hℓ, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow hℓ0.le, ENNReal.ofReal_natCast]
    · rw [ite_eq_right hℓ, ite_eq_right hℓ, ENNReal.ofReal_zero]
  rw [tailConst, tsum_congr hpt,
    ← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => by split <;> positivity) hsummable]
  exact ENNReal.ofReal_ne_top

private theorem absNorm_eq_pow_inertiaDeg_ratBelow (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm v.asIdeal
      = ratBelow v ^ ((ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal) :=
  Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal (ratBelow_prime v)

private theorem sq_ratBelow_le_absNorm (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ratBelow v ^ 2 ≤ Ideal.absNorm v.asIdeal := by
  have : Fact (ratBelow v).Prime := ⟨ratBelow_prime v⟩
  have h1 : 0 < (ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal :=
    Ideal.inertiaDeg'_pos (ratPrimeIdeal (ratBelow v)) v.asIdeal
  have h2 : (ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal ≠ 1 := by
    intro h
    rw [absNorm_eq_pow_inertiaDeg_ratBelow K v, h, pow_one] at hv
    exact hv (ratBelow_prime v)
  calc ratBelow v ^ 2
      ≤ ratBelow v ^ ((ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal) :=
        Nat.pow_le_pow_right (ratBelow_prime v).pos (by omega)
    _ = Ideal.absNorm v.asIdeal := (absNorm_eq_pow_inertiaDeg_ratBelow K v).symm

private def RatBelowFiber (ℓ : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // ratBelow v = ℓ}

private theorem liesOver_of_ratBelow_eq {v : HeightOneSpectrum (𝓞 K)} {ℓ : ℕ}
    (h : ratBelow v = ℓ) : v.asIdeal.LiesOver (ratPrimeIdeal ℓ) :=
  h ▸ liesOver_ratBelow v

private noncomputable def ratBelowFiberEquiv :
    (Σ ℓ : ℕ, RatBelowFiber K ℓ) ≃ HeightOneSpectrum (𝓞 K) where
  toFun p := p.2.1
  invFun v := ⟨ratBelow v, v, rfl⟩
  left_inv p := by rcases p with ⟨ℓ, v, rfl⟩; rfl
  right_inv v := rfl

private theorem isEmpty_ratBelowFiber {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) :
    IsEmpty (RatBelowFiber K ℓ) :=
  ⟨fun v => hℓ (v.2 ▸ ratBelow_prime v.1)⟩

private instance (ℓ : ℕ) : Finite (RatBelowFiber K ℓ) := by
  by_cases hℓ : ℓ.Prime
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    have hinj : Function.Injective (fun (v : RatBelowFiber K ℓ) =>
        (⟨v.1.asIdeal, v.1.isPrime, liesOver_of_ratBelow_eq K v.2⟩ :
          ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))))) :=
      fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    have hfin : Finite ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))) := by
      rw [← IsDedekindDomain.coe_primesOverFinset (ratPrimeIdeal_ne_bot hℓ) (𝓞 K)]
      exact (IsDedekindDomain.primesOverFinset (ratPrimeIdeal ℓ) (𝓞 K)).finite_toSet.to_subtype
    exact Finite.of_injective _ hinj
  · have := isEmpty_ratBelowFiber K hℓ
    infer_instance

private theorem natCard_ratBelowFiber_le {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Nat.card (RatBelowFiber K ℓ) ≤ Module.finrank ℚ K := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hinj : Function.Injective (fun (v : RatBelowFiber K ℓ) =>
      (⟨v.1.asIdeal, v.1.isPrime, liesOver_of_ratBelow_eq K v.2⟩ :
        ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))))) :=
    fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine le_trans (Nat.card_le_card_of_injective _ hinj) ?_
  rw [Nat.card_coe_set_eq, ← IsDedekindDomain.coe_primesOverFinset
    (ratPrimeIdeal_ne_bot hℓ) (𝓞 K), Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (S := 𝓞 K) (K := ℚ) (L := K)
    (p := ratPrimeIdeal ℓ) (ratPrimeIdeal_ne_bot hℓ)

private lemma tsum_reindex' {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑' a, f (e a) = ∑' b, f b := by
  refine le_antisymm (ENNReal.tsum_comp_le_tsum_of_injective e.injective f) ?_
  simpa using ENNReal.tsum_comp_le_tsum_of_injective e.symm.injective fun a => f (e a)

private theorem tailSum_le {s : ℝ} (hs : 1 ≤ s) :
    tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * tailConst := by
  have hpt : ∀ v : HeightOneSpectrum (𝓞 K),
      (if (Ideal.absNorm v.asIdeal).Prime then 0 else normRpow K s v.asIdeal)
        ≤ ((ratBelow v : ℝ≥0∞) ^ 2)⁻¹ := by
    intro v
    by_cases hv : (Ideal.absNorm v.asIdeal).Prime
    · rw [ite_eq_left hv]; exact zero_le
    · rw [ite_eq_right hv]
      calc normRpow K s v.asIdeal
          ≤ normRpow K 1 v.asIdeal :=
            ENNReal.rpow_le_rpow_of_exponent_le (one_le_cast_absNorm v.ne_bot)
              (neg_le_neg hs)
        _ = ((Ideal.absNorm v.asIdeal : ℝ≥0∞))⁻¹ := ENNReal.rpow_neg_one _
        _ ≤ ((ratBelow v : ℝ≥0∞) ^ 2)⁻¹ := by
            refine ENNReal.inv_le_inv' ?_
            calc ((ratBelow v : ℝ≥0∞) ^ 2)
                = ((ratBelow v ^ 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
              _ ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) :=
                  Nat.cast_le.mpr (sq_ratBelow_le_absNorm K v hv)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [← tsum_reindex' (ratBelowFiberEquiv K) (fun v => ((ratBelow v : ℝ≥0∞) ^ 2)⁻¹),
    ENNReal.tsum_sigma']
  have hfib : ∀ ℓ : ℕ, ∀ v : RatBelowFiber K ℓ,
      ((ratBelow (ratBelowFiberEquiv K ⟨ℓ, v⟩) : ℝ≥0∞) ^ 2)⁻¹ = ((ℓ : ℝ≥0∞) ^ 2)⁻¹ := by
    intro ℓ v
    have : ratBelow (ratBelowFiberEquiv K ⟨ℓ, v⟩) = ℓ := v.2
    rw [this]
  calc ∑' (ℓ : ℕ) (v : RatBelowFiber K ℓ),
        ((ratBelow (ratBelowFiberEquiv K ⟨ℓ, v⟩) : ℝ≥0∞) ^ 2)⁻¹
      = ∑' ℓ : ℕ, (Nat.card (RatBelowFiber K ℓ) : ℝ≥0∞) * ((ℓ : ℝ≥0∞) ^ 2)⁻¹ := by
        refine tsum_congr fun ℓ => ?_
        rw [tsum_congr (hfib ℓ), ENNReal.tsum_const, ENat.card_eq_coe_natCard]
        norm_cast
    _ ≤ ∑' ℓ : ℕ, (Module.finrank ℚ K : ℝ≥0∞) *
          (if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0) := by
        refine ENNReal.tsum_le_tsum fun ℓ => ?_
        by_cases hℓ : ℓ.Prime
        · rw [ite_eq_left hℓ]
          gcongr
          exact Nat.cast_le.mpr (natCard_ratBelowFiber_le K hℓ)
        · have : Nat.card (RatBelowFiber K ℓ) = 0 :=
            @Nat.card_of_isEmpty _ (isEmpty_ratBelowFiber K hℓ)
          rw [ite_eq_right hℓ, mul_zero, this, Nat.cast_zero, zero_mul]
    _ = (Module.finrank ℚ K : ℝ≥0∞) * tailConst := by
        rw [tailConst, ENNReal.tsum_mul_left]

private theorem cutSum_le (S₀ : Finset ℕ) {s : ℝ} (hs : 0 < s) :
    cutSum K S₀ s ≤ ∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞) := by
  have hterm : ∀ ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)
      ≤ (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) := by
    intro ℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · rw [degOneCount_of_not_prime K Nat.not_prime_zero]
      simp
    · calc (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)
          ≤ (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * 1 := by
            gcongr
            exact ENNReal.rpow_le_one_of_one_le_of_neg (by exact_mod_cast hℓ)
              (neg_neg_iff_pos.mpr hs)
        _ = _ := mul_one _
  calc cutSum K S₀ s
      ≤ ∑' ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑ ℓ ∈ S₀, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) :=
        tsum_eq_sum fun _ hℓ => ite_eq_right hℓ
    _ = ∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞) :=
        Finset.sum_congr rfl fun _ hℓ => ite_eq_left hℓ

private theorem sum_degOneCount_ne_top (S₀ : Finset ℕ) :
    (∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞)) ≠ ⊤ :=
  (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.natCast_lt_top _).ne

private theorem term_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 0 < s) (ℓ : ℕ) :
    (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [degOneCount_of_not_prime K Nat.not_prime_zero]
    simp
  · refine ENNReal.mul_ne_top (by split <;> simp) ?_
    exact ((ENNReal.rpow_le_one_of_one_le_of_neg (by exact_mod_cast hℓ)
      (neg_neg_iff_pos.mpr hs)).trans_lt ENNReal.one_lt_top).ne

private theorem degOneSum_toReal_eq (S₀ : Finset ℕ) {s : ℝ} (hs : 0 < s) :
    (degOneSum K S₀ s).toReal
      = ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [degOneSum, ENNReal.tsum_toReal_eq (term_ne_top K S₀ hs)]
  exact tsum_congr (toReal_term K S₀ s)

private theorem tailSum_toReal_isBigO :
    (fun s : ℝ => (tailSum K s).toReal) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  rw [isBigO_one_iff]
  refine isBoundedUnder_of_eventually_le
    (a := ((Module.finrank ℚ K : ℝ≥0∞) * tailConst).toReal) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) tailConst_ne_top) (tailSum_le K hs.le)

private theorem cutSum_toReal_isBigO (S₀ : Finset ℕ) :
    (fun s : ℝ => (cutSum K S₀ s).toReal) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  rw [isBigO_one_iff]
  refine isBoundedUnder_of_eventually_le
    (a := (∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞)).toReal) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (sum_degOneCount_ne_top K S₀)
    (cutSum_le K S₀ (lt_trans zero_lt_one hs))

theorem degOneSum_add_log_isBigO (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) :
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)) =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) := by
  have h1 := primeSum_toReal_add_log_isBigO K
  have h2 := cutSum_toReal_isBigO K S₀
  have h3 := tailSum_toReal_isBigO K
  refine ((h1.sub h2).sub h3).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  have hdecomp := congrArg ENNReal.toReal (primeSum_eq_degOneSum_add K S₀ s)
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨degOneSum_ne_top K S₀ hs, cutSum_ne_top K S₀ hs⟩)
      (tailSum_ne_top K hs),
    ENNReal.toReal_add (degOneSum_ne_top K S₀ hs) (cutSum_ne_top K S₀ hs)] at hdecomp
  show (primeSum K s).toReal + Real.log (s - 1) - (cutSum K S₀ s).toReal
      - (tailSum K s).toReal
    = (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)
  rw [← degOneSum_toReal_eq K S₀ (lt_trans zero_lt_one hs), hdecomp]
  ring

theorem summable_degOne_term (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) :=
  (ENNReal.summable_toReal (degOneSum_ne_top K S₀ hs)).congr (toReal_term K S₀ s)

end FrobeniusDensity
