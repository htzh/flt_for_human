/-
  The Frobenius-density statement from the degree-one asymptotic
  (`FrobeniusDensity.statement_of_degOneAsymptotic`): if the degree-one prime
  count has the Chebotarev-with-log-pole asymptotic `DegOneAsymptotic L`, then
  every conjugacy condition is realised by a prime outside any finite set `S`.

  The proof runs the Möbius/`zpowers` weight identity (`weight_eq`,
  `sum_moebius_mul_pos`) against the degree-one count
  (`ncard_degreeOne_primesOver_eq_ncard_frobFixed`) and turns a non-realisation
  into the contradiction `log (s - 1) = O(1)`.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_statement_of_degOneAsymptotic.lean`, 165 lines).
  The two private helpers `tendsto_log_sub_one` and
  `not_isBigO_one_of_tendsto_atBot` are transcribed `private`; `tendsto_log_sub_one`
  is the same fact the S7-I tail restates privately in its own module. The
  mathematics is math/019 §4.
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.NcardConjGen
import FLTForHuman.NumberTheory.FrobeniusDensity.MobiusZeta
import FLTForHuman.NumberTheory.FrobeniusDensity.DegreeOneCount
import FLTForHuman.NumberTheory.FrobeniusDensity.BadPrimes
import FLTForHuman.NumberTheory.FrobeniusDensity.DegOneAsymptotic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open Filter Topology Asymptotics NumberField Ideal
open scoped Topology

namespace FrobeniusDensity

private theorem tendsto_log_sub_one :
    Tendsto (fun s : ℝ => Real.log (s - 1)) (𝓝[>] 1) atBot := by
  refine Real.tendsto_log_nhdsGT_zero.comp ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_sub_right (1:ℝ)).tendsto' 1 0 (by norm_num)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simpa [Set.mem_Ioi, sub_pos] using hs

private theorem not_isBigO_one_of_tendsto_atBot {f : ℝ → ℝ}
    (hf : Tendsto f (𝓝[>] (1:ℝ)) atBot) :
    ¬ (f =O[𝓝[>] (1:ℝ)] (fun _ => (1 : ℝ))) := by
  intro hO
  rw [isBigO_one_iff] at hO
  obtain ⟨C, hC⟩ := hO
  simp only [eventually_map] at hC
  have h1 : ∀ᶠ s in 𝓝[>] (1:ℝ), f s < -C - 1 := hf.eventually (eventually_lt_atBot (-C - 1))
  obtain ⟨s, hs1, hs2⟩ := (hC.and h1).exists
  rw [Real.norm_eq_abs] at hs1
  have := abs_le.mp hs1
  linarith [this.1]

theorem statement_of_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] (hL : FrobeniusDensity.DegOneAsymptotic L) :
    FrobeniusDensity.Statement L := by
  intro σ S
  classical
  set S₀ : Finset ℕ := S ∪ badPrimes L with hS₀
  set E : ℕ → IntermediateField ℚ L := fun f =>
    FixedPoints.intermediateField (Subgroup.zpowers (σ ^ (orderOf σ / f))) with hE
  set c : ℤ := ∑ f ∈ (orderOf σ).divisors,
    (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) with hc
  have hcpos : 0 < c := sum_moebius_mul_pos σ
  set T : ℕ → ℝ → ℝ := fun f s => ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
    (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) with hT
  by_contra hcon

  have hweight : ∀ ℓ : ℕ, ℓ ∉ S₀ →
      ∑ f ∈ (orderOf σ).divisors, (ArithmeticFunction.moebius (orderOf σ / f)) * ((f : ℤ) *
        (degOneCount (E f : IntermediateField ℚ L) ℓ : ℤ)) = 0 := by
    intro ℓ hℓS₀
    by_cases hℓ : ℓ.Prime
    · haveI : Fact ℓ.Prime := ⟨hℓ⟩
      obtain ⟨⟨Q₀, hQ₀p, hQ₀l⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) (ratPrimeIdeal ℓ)
      haveI := hQ₀p
      haveI := hQ₀l
      have hQ₀i : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥ :=
        inertia_eq_bot_of_notMem_badPrimes L hℓ (fun h => hℓS₀ (Finset.mem_union_right _ h)) Q₀
      haveI : Finite ((𝓞 L) ⧸ Q₀) :=
        finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
      have hcnt : ∀ f ∈ (orderOf σ).divisors,
          (degOneCount (E f : IntermediateField ℚ L) ℓ : ℤ)
            = ({x : (L ≃ₐ[ℚ] L) ⧸ Subgroup.zpowers (σ ^ (orderOf σ / f)) |
                arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ • x = x}.ncard : ℤ) := by
        intro f _
        rw [degOneCount_of_prime _ hℓ]
        exact_mod_cast
          ncard_degreeOne_primesOver_eq_ncard_frobFixed
            (H := Subgroup.zpowers (σ ^ (orderOf σ / f))) (E := E f) hℓ Q₀ hQ₀i
      rw [Finset.sum_congr rfl fun f hf => by rw [hcnt f hf]]
      rw [weight_eq σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)]
      norm_cast
      by_contra hne
      obtain ⟨k, hk, hconj⟩ :=
        (ncard_conj_gen_ne_zero_iff σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)).mp hne
      exact hcon ⟨ℓ, fun h => hℓS₀ (Finset.mem_union_left _ h),
        realizesCyclicAt_of_exists L σ hℓ Q₀ (fun _ => ⟨k, hk, hconj⟩)⟩
    · rw [Finset.sum_congr rfl fun f _ => by rw [degOneCount_of_not_prime _ hℓ]]
      simp

  have hsummable : ∀ f ∈ (orderOf σ).divisors, ∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ =>
      (if ℓ ∈ S₀ then 0 else (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ))
        * (ℓ : ℝ) ^ (-s)) :=
    fun f _ s hs => (hL (Subgroup.zpowers (σ ^ (orderOf σ / f))) S₀).1 s hs
  have hFzero : ∀ s : ℝ, 1 < s →
      ∑ f ∈ (orderOf σ).divisors,
        ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s = 0 := by
    intro s hs
    have hinter : ∑ f ∈ (orderOf σ).divisors,
        ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s
        = ∑' ℓ : ℕ, ∑ f ∈ (orderOf σ).divisors,
            ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
              ((if ℓ ∈ S₀ then 0 else
                (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) := by
      rw [show (∑ f ∈ (orderOf σ).divisors,
          ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s)
          = ∑ f ∈ (orderOf σ).divisors, ∑' ℓ : ℕ,
              ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
                ((if ℓ ∈ S₀ then 0 else
                  (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) from
        Finset.sum_congr rfl fun f _ => tsum_mul_left.symm]
      exact (Summable.tsum_finsetSum
        (fun f hf => ((hsummable f hf s hs).mul_left _))).symm
    rw [hinter]
    refine Eq.trans (tsum_congr fun ℓ => ?_) tsum_zero
    by_cases hℓS₀ : ℓ ∈ S₀
    · simp [hℓS₀]
    · have h := hweight ℓ hℓS₀
      have h2 : ∑ f ∈ (orderOf σ).divisors,
          ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
            ((if ℓ ∈ S₀ then 0 else
              (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
          = (((∑ f ∈ (orderOf σ).divisors,
              (ArithmeticFunction.moebius (orderOf σ / f)) * ((f : ℤ) *
                (degOneCount (E f : IntermediateField ℚ L) ℓ : ℤ)) : ℤ)) : ℝ)
              * (ℓ : ℝ) ^ (-s) := by
        rw [Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [ite_eq_right hℓS₀]
        push_cast
        ring
      rw [h2, h, Int.cast_zero, zero_mul]

  have hO : (fun s : ℝ => (∑ f ∈ (orderOf σ).divisors,
      ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s) + (c : ℝ) *
        Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hsum : ∀ s : ℝ, (∑ f ∈ (orderOf σ).divisors,
        ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s) + (c : ℝ) *
          Real.log (s - 1)
        = ∑ f ∈ (orderOf σ).divisors,
            ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
              (T f s + Real.log (s - 1)) := by
      intro s
      rw [hc]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    refine (Asymptotics.IsBigO.sum fun f _ => ?_).congr'
      (Eventually.of_forall fun s => by rw [Finset.sum_apply]; exact (hsum s).symm) EventuallyEq.rfl
    exact ((hL (Subgroup.zpowers (σ ^ (orderOf σ / f))) S₀).2).const_mul_left _
  have hO2 : (fun s : ℝ => (c : ℝ) * Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hO.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    rw [hFzero s hs, zero_add]
  have hO3 : (fun s : ℝ => Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hcne : (c : ℝ) ≠ 0 := by exact_mod_cast hcpos.ne'
    refine (hO2.const_mul_left (c : ℝ)⁻¹).congr'
      (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    show ((c : ℝ))⁻¹ * ((c : ℝ) * Real.log (s - 1)) = Real.log (s - 1)
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  exact not_isBigO_one_of_tendsto_atBot tendsto_log_sub_one hO3

end FrobeniusDensity
