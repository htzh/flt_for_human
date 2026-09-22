/-
  T18 — one new generator per prime power.

  The mandatory scope of T18 is the single `Inputs` field
  `full_eq_adjoin_full_div_prime`: for `p ∤ M`,
  `F^full_{M p ^ (a + 1)} = ℚ(F^full_{M p ^ a}, j(q ^ (p ^ (a + 1))))`. It is the
  generation half of the strong induction; with it the conditional capstone's debt
  is **3 → 2**.

  The engine is the **two-prime descent** `jqN_mem_of_div_primes`: if
  `j(q ^ (d / p))` and `j(q ^ (d / q))` both lie in a field `F`, then `j(q ^ d)`
  does. It is the unique-common-root principle (`Polynomial.mem_range_of_unique_common_root`,
  T4's generic engine) run with the level-`p` and level-`q` data read at the
  level-`N` nome: `j(q ^ d)` is the unique common root of `φ_p(j(q ^ (d/p)), ·)`
  and `φ_q(j(q ^ (d/q)), ·)`. The strong induction
  `w1_jqN_mem_adjoin_top_insert` walks `d ∣ M * p ^ (a + 1)` and either lands in
  `F^full_{M p ^ a}` or peels a prime `q` from the `M`-part.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_full_eq_adjoin_full_div_prime.lean` (node 601–620,
  helpers 397–600). The public statement is the `Theorems/` wrapper's verbatim.

  ## Dedup

  The pin carries `jqN_mem_of_div_primes` verbatim in three files
  (`S_ModularCurve_full_eq_adjoin_full_div_prime.lean:397`,
  `S_ModularCurve_full_eq_adjoin_primes.lean:397` and
  `S_ModularCurve_modularFunctionField_eq_full_of.lean:397`); this module ports it
  **once**. The redundant `jqN_congr'` (pin 530–532) is dropped in favour of the
  public `Defs/Jq.lean` `jqN_congr`.

  ## Scope

  The five remaining nodes of the original six-node topic
  (`full_eq_adjoin_primes`, `dedekindPsi_of_squarefree`,
  `relfinrank_full_of_squarefree`, `finrank_adjoin_jqN_eq_of_squarefree`,
  `functionFieldGeneration_of_squarefree`) are **deferred optional API**: their one
  external consumer was T19's `Gen p` step, now supplied by `gen_prime` in
  `Defs/Fields.lean` (`TOPIC-t17-t19-route-audit.md` §1). See
  `TOPIC-generation.md` §1 for the decision and its evidence.

  ## Assumptions

  T4's `Polynomial.mem_range_of_unique_common_root` (`FieldTheory/CommonRoot`);
  T12's `exists_phiIrreducible_evalSymm`; T13's `PhiGen.splits_prime_at_slot`; T14's
  `phiAtSeed*`, `isRoot_prime_at_slot_iff`, `roots_prime_at_slot_roots_nodup`,
  `iota_jqN`, `TS_congr`/`TS_injective`; `Defs/Cyclotomic`'s `cycUnit`/`cycUnit_spec`;
  `Defs/Fields`'s `modularFunctionFieldFull`/`jqd_mem_full`/`full_degeneracy_le`;
  `Defs/Laurent`'s `coeffMap_injective`/`qExpand_injective`.
-/
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties

set_option autoImplicit false
-- The pin installs the `Algebra F (LaurentSeries K)` instance (via `letI`); it is
-- consumed by typeclass search, so the style linter's `have` preference does not
-- apply. Same local disable as `Descent.lean`/`Nonmembership.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

open PhiGen

/-! ## The two-prime descent -/

/-- **The two-prime descent**: if `j(q ^ (d / p))` and `j(q ^ (d / q))` lie in `F`
then `j(q ^ d)` does. The unique-common-root principle applied to the level-`p`
and level-`q` data read at the level-`N` nome; `j(q ^ d)` is the unique common
root. Ported once for both pin generation files (verbatim from
`S_ModularCurve_full_eq_adjoin_full_div_prime.lean:397`). -/
private theorem jqN_mem_of_div_primes {K : Type*} [Field K] [Algebra ℚ K]
    {N : ℕ} [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    {F : IntermediateField ℚ (LaurentSeries ℚ)}
    {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {p q : ℕ} (pp : Nat.Prime p) (qq : Nat.Prime q) (hpq : p ≠ q)
    (hpd : p ∣ d) (hqd : q ∣ d) [NeZero (d / p)] [NeZero (d / q)]
    (hmp : jqN (d / p) ∈ F) (hmq : jqN (d / q) ∈ F) :
    jqN d ∈ F := by
  haveI : Fact (Nat.Prime p) := ⟨pp⟩
  haveI : Fact (Nat.Prime q) := ⟨qq⟩
  haveI : NeZero p := ⟨pp.ne_zero⟩
  haveI : NeZero q := ⟨qq.ne_zero⟩
  have hpN : p ∣ N := hpd.trans hdN
  have hqN : q ∣ N := hqd.trans hdN
  have hNp0 : N / p ≠ 0 := fun h0 => NeZero.ne N (by rw [← Nat.div_mul_cancel hpN, h0, zero_mul])
  have hNq0 : N / q ≠ 0 := fun h0 => NeZero.ne N (by rw [← Nat.div_mul_cancel hqN, h0, zero_mul])
  haveI : NeZero (N / p) := ⟨hNp0⟩
  haveI : NeZero (N / q) := ⟨hNq0⟩

  have hpe : p * (N / p * (d / p)) = N * (d / p) := by
    rw [← mul_assoc, Nat.mul_div_cancel' hpN]
  have hqe : q * (N / q * (d / q)) = N * (d / q) := by
    rw [← mul_assoc, Nat.mul_div_cancel' hqN]
  have hpe2 : p * (p * (N / p * (d / p))) = N * d := by
    rw [hpe, mul_left_comm, Nat.mul_div_cancel' hpd]
  have hqe2 : q * (q * (N / q * (d / q))) = N * d := by
    rw [hqe, mul_left_comm, Nat.mul_div_cancel' hqd]

  have data_p : ModularPolynomialData p := (exists_phiIrreducible_evalSymm p).choose
  have data_q : ModularPolynomialData q := (exists_phiIrreducible_evalSymm q).choose

  letI : Algebra F (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra

  have hmapA : (phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed data_p (coeffEmb K (qExpand ℚ N (jqN (d / p)))) :=
    phiAtSeed_map data_p _ _
  have hmapB : (phiAtSeed data_q (⟨jqN (d / q), hmq⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed data_q (coeffEmb K (qExpand ℚ N (jqN (d / q)))) :=
    phiAtSeed_map data_q _ _

  have hseed_p : coeffEmb K (qExpand ℚ N (jqN (d / p)))
      = qExpand K (p * (N / p * (d / p))) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq)) := by
    have h2 : TS K (N * (d / p)) 1 = TS K (p * (N / p * (d / p))) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
      exact TS_congr hpe.symm 1
    exact (iota_jqN N (d / p)).trans h2
  have hseed_q : coeffEmb K (qExpand ℚ N (jqN (d / q)))
      = qExpand K (q * (N / q * (d / q))) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq)) := by
    have h2 : TS K (N * (d / q)) 1 = TS K (q * (N / q * (d / q))) ((1 : Kˣ) ^ q) := by
      rw [one_pow]
      exact TS_congr hqe.symm 1
    exact (iota_jqN N (d / q)).trans h2

  have hdist_p : coeffEmb K (qExpand ℚ N (jqN d))
      = qExpand K (p * (p * (N / p * (d / p)))) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) := by
    have h2 : TS K (N * d) 1 = TS K (p * (p * (N / p * (d / p)))) ((1 : Kˣ) ^ (p * p)) := by
      rw [one_pow]
      exact TS_congr hpe2.symm 1
    exact (iota_jqN N d).trans h2
  have hdist_q : coeffEmb K (qExpand ℚ N (jqN d))
      = qExpand K (q * (q * (N / q * (d / q)))) (qTwist ((1 : Kˣ) ^ (q * q)) (coeffEmb K jq)) := by
    have h2 : TS K (N * d) 1 = TS K (q * (q * (N / q * (d / q)))) ((1 : Kˣ) ^ (q * q)) := by
      rw [one_pow]
      exact TS_congr hqe2.symm 1
    exact (iota_jqN N d).trans h2

  have hrootA : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)) = 0 ↔
        (y = qExpand K (p * (p * (N / p * (d / p)))) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) ∨
          ∃ b < p, y = qExpand K (N / p * (d / p)) (qTwist (1 * ζ ^ (b * (N / p))) (coeffEmb K jq))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hseed_p]
    exact isRoot_prime_at_slot_iff N ζ hζ p hpN data_p (N / p * (d / p)) 1 y
  have hrootB : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_q (⟨jqN (d / q), hmq⟩ : F)) = 0 ↔
        (y = qExpand K (q * (q * (N / q * (d / q)))) (qTwist ((1 : Kˣ) ^ (q * q)) (coeffEmb K jq)) ∨
          ∃ c < q, y = qExpand K (N / q * (d / q)) (qTwist (1 * ζ ^ (c * (N / q))) (coeffEmb K jq))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapB, hseed_q]
    exact isRoot_prime_at_slot_iff N ζ hζ q hqN data_q (N / q * (d / q)) 1 y

  have hA0 : phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F) ≠ 0 := (phiAtSeed_monic data_p _).ne_zero
  have hAs : ((phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)).map
      (algebraMap F (LaurentSeries K))).Splits := by
    rw [hmapA, hseed_p, phiAtSeed,
      PhiGen.splits_prime_at_slot N ζ hζ p hpN data_p (N / p * (d / p)) 1]
    exact (Polynomial.Splits.X_sub_C _).mul
      (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hAnd : ((phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)).map
      (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hseed_p, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup N ζ hζ p hpN data_p (N / p * (d / p)) 1
  have hxA : Polynomial.aeval (coeffEmb K (qExpand ℚ N (jqN d)))
      (phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)) = 0 :=
    (hrootA _).mpr (Or.inl hdist_p)
  have hxB : Polynomial.aeval (coeffEmb K (qExpand ℚ N (jqN d)))
      (phiAtSeed data_q (⟨jqN (d / q), hmq⟩ : F)) = 0 :=
    (hrootB _).mpr (Or.inl hdist_q)

  have huniq : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)) = 0 →
      Polynomial.aeval y (phiAtSeed data_q (⟨jqN (d / q), hmq⟩ : F)) = 0 →
      y = coeffEmb K (qExpand ℚ N (jqN d)) := by
    intro y hyA hyB
    rcases (hrootA y).mp hyA with hy1 | ⟨b, hb, hy1⟩
    · exact hy1.trans hdist_p.symm
    · rcases (hrootB y).mp hyB with hy2 | ⟨c, hc, hy2⟩
      · exact hy2.trans hdist_q.symm
      · exfalso
        have hTS : TS K (N / p * (d / p)) (1 * ζ ^ (b * (N / p)))
            = TS K (N / q * (d / q)) (1 * ζ ^ (c * (N / q))) := hy1.symm.trans hy2
        have he : N / p * (d / p) = N / q * (d / q) := (TS_injective hTS).1
        have h1 : p * p * (N / p * (d / p)) = q * q * (N / p * (d / p)) := by
          rw [mul_assoc, hpe2, mul_assoc, he, hqe2]
        have h2 : p * p = q * q :=
          Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne (N / p * (d / p)))) h1
        have h3 : q ∣ p * p := by rw [h2]; exact dvd_mul_right q q
        have h4 : q ∣ p := ((Nat.Prime.dvd_mul qq).mp h3).elim id id
        exact hpq (((Nat.prime_dvd_prime_iff_eq qq pp).mp h4).symm)

  have hrange := Polynomial.mem_range_of_unique_common_root
    (phiAtSeed data_p (⟨jqN (d / p), hmp⟩ : F)) (phiAtSeed data_q (⟨jqN (d / q), hmq⟩ : F))
    hA0 hAs hAnd (coeffEmb K (qExpand ℚ N (jqN d))) hxA hxB huniq
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hrange
  have hf' : coeffEmb K (qExpand ℚ N ((f : LaurentSeries ℚ)))
      = coeffEmb K (qExpand ℚ N (jqN d)) := hf
  have hemb : Function.Injective (coeffEmb K) :=
    coeffMap_injective ((algebraMap ℚ K).injective)
  have hval : (f : LaurentSeries ℚ) = jqN d := qExpand_injective N (hemb hf')
  rw [← hval]
  exact f.2

/-! ## The generation step -/

/-- **The generation walk**: every `j(q ^ d)` with `d ∣ M * p ^ (a + 1)` lies in
`ℚ(F^full_{M p ^ a}, j(q ^ (p ^ (a + 1))))`. Strong induction on `d`: either `d`
already divides `M * p ^ a`, or a prime `q ≠ p` divides its `M`-part and the
two-prime descent applies to `d / p` (in the target) and `d / q` (smaller, so the
induction hypothesis). -/
private theorem w1_jqN_mem_adjoin_top_insert (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) :
    ∀ (d : ℕ) [NeZero d], d ∣ M * p ^ (a + 1) →
      jqN d ∈ IntermediateField.adjoin ℚ
        (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :
          Set (LaurentSeries ℚ))) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd0 hdN
    by_cases hbase : d ∣ M * p ^ a
    · exact IntermediateField.subset_adjoin ℚ _
        (Set.mem_insert_of_mem _ (jqd_mem_full (M * p ^ a) hbase))
    · have hcop : Nat.Coprime M (p ^ (a + 1)) :=
        (Nat.Coprime.pow_right _ (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpM).symm))
      have hsplit : Nat.gcd d M * Nat.gcd d (p ^ (a + 1)) = d :=
        (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hdN
      set m := Nat.gcd d M with hmdef
      have hmM : m ∣ M := Nat.gcd_dvd_right d M
      have hm0 : m ≠ 0 := fun h0 => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ hmM))
      obtain ⟨j, hj, hpj⟩ := (Nat.dvd_prime_pow hp.out).mp (Nat.gcd_dvd_right d (p ^ (a + 1)))
      have hd : d = m * p ^ j := by rw [← hsplit, hpj]
      have hja : j = a + 1 := by
        by_contra hja
        exact hbase (hd ▸ mul_dvd_mul hmM (pow_dvd_pow p (by omega)))
      rw [hja] at hd
      rcases eq_or_ne m 1 with hm1 | hm1
      · rw [jqN_congr (show d = p ^ (a + 1) by rw [hd, hm1, one_mul])]
        exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
      ·
        set q := m.minFac with hqdef
        have hq : q.Prime := Nat.minFac_prime hm1
        have hqm : q ∣ m := Nat.minFac_dvd m
        have hqp : p ≠ q := fun h => hpM ((h ▸ hqm).trans hmM)
        have hpd : p ∣ d := hd ▸ Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero a)) m
        have hqd : q ∣ d := hd ▸ (hqm.trans (dvd_mul_right m (p ^ (a + 1))))
        obtain ⟨m', hm'⟩ := hqm
        have hm'0 : m' ≠ 0 := fun h0 => hm0 (by rw [hm', h0, Nat.mul_zero])
        have hdp : d / p = m * p ^ a := by
          rw [hd, pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ hp.out.pos]
        have hdq : d / q = m' * p ^ (a + 1) := by
          rw [hd, hm', Nat.mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
        haveI : NeZero (d / p) :=
          ⟨by rw [hdp]; exact Nat.mul_ne_zero hm0 (pow_ne_zero _ hp.out.ne_zero)⟩
        haveI : NeZero (d / q) :=
          ⟨by rw [hdq]; exact Nat.mul_ne_zero hm'0 (pow_ne_zero _ hp.out.ne_zero)⟩
        have hmem_p : jqN (d / p) ∈ IntermediateField.adjoin ℚ
            (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :
              Set (LaurentSeries ℚ))) := by
          refine IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _
            (jqd_mem_full (M * p ^ a) ?_))
          rw [hdp]
          exact mul_dvd_mul hmM dvd_rfl
        have hmem_q : jqN (d / q) ∈ IntermediateField.adjoin ℚ
            (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :
              Set (LaurentSeries ℚ))) := by
          refine ih (d / q) (Nat.div_lt_self (Nat.pos_of_ne_zero hd0.out) hq.one_lt) ?_
          exact (Nat.div_dvd_of_dvd hqd).trans hdN
        exact jqN_mem_of_div_primes (cycUnit (M * p ^ (a + 1)))
          (cycUnit_spec (M * p ^ (a + 1))) hdN hp.out hq hqp hpd hqd hmem_p hmem_q

/-! ## The node -/

/-- **One new generator per prime power**: for `p ∤ M`,
`F^full_{M p ^ (a + 1)} = ℚ(F^full_{M p ^ a}, j(q ^ (p ^ (a + 1))))`. This is the
`Inputs.full_eq_adjoin_full_div_prime` field. Verbatim from
`Theorems/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean`. -/
theorem full_eq_adjoin_full_div_prime (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) :
    modularFunctionFieldFull (M * p ^ (a + 1)) =
      IntermediateField.adjoin ℚ
        (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :
          Set (LaurentSeries ℚ))) := by
  refine le_antisymm ?_ ?_
  · rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hd0, hdN, rfl⟩
    exact w1_jqN_mem_adjoin_top_insert M p a hpM d hdN
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact jqd_mem_full (M * p ^ (a + 1)) (dvd_mul_left _ _)
    · exact full_degeneracy_le (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ a))) hx

end ModularCurve

end
