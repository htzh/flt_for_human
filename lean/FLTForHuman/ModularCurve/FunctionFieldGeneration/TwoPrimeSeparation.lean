/-
  T17-b — the two-prime separation.

  `jqN r ∉ ℚ(j, j(q ^ p) : p ∈ S)` for a finite set `S` of primes with `r ∉ S`. The
  engine is `step_contradiction`: if `j(q ^ r) = g(j(q ^ p))`, then `g` has degree
  `< p + 1` and is constant on the `p + 1` roots of `Φ_p(j(q), ·)` (a T4 `CommonRoot`
  engine), so `j(q ^ r) ∈ ℚ(j)`, contradicting `[ℚ(j)(j(q ^ p)) : ℚ(j)] = p + 1` —
  T16's first statement. The Finset induction over `S` is
  `jqN_prime_not_mem_adjoin_key`.

  It is public `Theorems/` API and is not on the capstone's path (the prime
  non-membership is `Nonmembership.jqN_prime_not_mem_full`, which does not need the
  separation); it is consumed by `relfinrank_adjoin_primes`, `relfinrank_full_mul_prime`
  and `jqN_sq_not_mem_adjoin`.

  ## Why it is downstream of T16, and separate

  This is the one non-membership statement that consumes T16
  (`finrank_adjoin_jqN_prime_of_not_mem`, over an arbitrary `F`), so it cannot sit beside
  `Nonmembership.lean`'s two facts, which T16's degree step consumes. Until 2026-11-04 the
  whole node was one module, with the tower and this statement in `Nonmembership.lean`;
  the split follows the dependency: T16 consumes the tower, this consumes T16.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_adjoin.lean` (node 426–651; lines 406–425 are
  T14's helpers). The public statement is the `Theorems/` wrapper's verbatim.

  ## Dedup

  The pin file opens with T14's ~370-line prelude, already written once in
  `Defs/PhiAtSlot.lean`, `Defs/TS.lean`, `Defs/Cyclotomic.lean` and `Defs/Jq.lean`; none of
  it is re-copied here. The pin's `set_option maxHeartbeats 3200000 in` (at 961) is
  omitted — below the port's global 4000000.

  ## Assumptions

  T4's `mem_range_of_eval_eq_const` (`FieldTheory/CommonRoot`); T12's
  `exists_phiIrreducible_evalSymm`; T13's `PhiGen.splits_prime_at_slot`; T14's
  `phiAtSeed*`, `isRoot_prime_at_slot_iff`, `roots_prime_at_slot*`, `iota_jq`,
  `TS_congr`/`TS_injective`; T16's `finrank_adjoin_jqN_prime_of_not_mem`;
  `Defs/Laurent`'s `coeffMap_injective`; `Defs/Cyclotomic`'s
  `cycUnit`/`cycUnit_spec`; `Defs/Fields`'s `modularFunctionFieldFull`; `Defs/Jq`'s
  `coeff_jq_neg_one`/`jqN_one`.
  spec-pin: Theorems/Thm_ModularCurve_jqN_prime_not_mem_adjoin.lean
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.FunctionFieldGeneration.DegreeStep

set_option autoImplicit false
-- The pin installs the `Algebra F (LaurentSeries K) := σ.toAlgebra` instance (via
-- `letI`) and the `IsCyclotomicExtension` instance; both are consumed by typeclass
-- search, so the style linter's `have` preference does not apply.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

open PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## The two-prime separation -/

private theorem step_contradiction (p r : ℕ) [hpp : Fact (Nat.Prime p)] [hrr : Fact (Nat.Prime r)]
    (hrp : r ≠ p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * r))
    (data_p : ModularPolynomialData p) (data_r : ModularPolynomialData r)
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F)
    (hpF : jqN p ∉ F) (hrF : jqN r ∉ F)
    (hmem : jqN r ∈ IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) : False := by
  haveI : NeZero (p * r) := ⟨Nat.mul_ne_zero hpp.out.ne_zero hrr.out.ne_zero⟩
  classical

  have hdeg := finrank_adjoin_jqN_prime_of_not_mem F hj p hpF
  have hjq_coe : algebraMap F (LaurentSeries ℚ) ⟨jq, hj⟩ = jq := rfl

  have haeval_p : Polynomial.aeval (jqN p) (phiAtSeed data_p (⟨jq, hj⟩ : F)) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map, hjq_coe]
    exact phiAtSeed_jq_eval p data_p
  have hα : IsIntegral F (jqN p) :=
    ⟨phiAtSeed data_p (⟨jq, hj⟩ : F), phiAtSeed_monic data_p _, by
      rw [← Polynomial.aeval_def]; exact haeval_p⟩

  have hmin_natdeg : (minpoly F (jqN p)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hα]
    exact hdeg
  have hPdeg : (phiAtSeed data_p (⟨jq, hj⟩ : F)).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree, dedekindPsi_prime hpp.out]
  have hmin_eq : phiAtSeed data_p (⟨jq, hj⟩ : F) = minpoly F (jqN p) := by
    apply minpoly.unique_of_degree_le_degree_minpoly _ _ (phiAtSeed_monic data_p _) haeval_p
    rw [Polynomial.degree_eq_natDegree (phiAtSeed_monic data_p (⟨jq, hj⟩ : F)).ne_zero,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero hα), hPdeg, hmin_natdeg]

  letI : Algebra F (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (p * r))).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : algebraMap F (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (p * r))).comp (algebraMap F (LaurentSeries ℚ)) :=
    RingHom.algebraMap_toAlgebra _

  have hmap_min : (minpoly F (jqN p)).map (algebraMap F (LaurentSeries K))
      = data_p.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (qExpand K (p * r) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq)))) := by
    rw [← hmin_eq, halg, ← Polynomial.map_map, phiAtSeed_map, hjq_coe, phiAtSeed_map,
      RingHom.comp_apply, iota_jq, one_pow, phiAtSeed, TS, coeffEmb_jq]
  have hpdvd : p ∣ p * r := dvd_mul_right p r
  have hroots : (minpoly F (jqN p)).aroots (LaurentSeries K)
      = qExpand K (p * (p * r)) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) ::ₘ
        (Multiset.range p).map
          (fun b => qExpand K r (qTwist ((1 : Kˣ) * ζ ^ (b * (p * r / p))) (coeffEmb K jq))) := by
    rw [Polynomial.aroots_def, hmap_min, roots_prime_at_slot (p * r) ζ hζ p hpdvd data_p r 1]
  have hM_nodup : ((minpoly F (jqN p)).aroots (LaurentSeries K)).Nodup := by
    rw [hroots]
    exact roots_prime_at_slot_nodup (p * r) ζ hζ p hpdvd r 1
  have hM_card : Multiset.card ((minpoly F (jqN p)).aroots (LaurentSeries K)) = p + 1 := by
    rw [hroots, Multiset.card_cons, Multiset.card_map, Multiset.card_range]

  obtain ⟨g, hg_deg, hg⟩ := (IntermediateField.adjoin.powerBasis hα).exists_eq_aeval
    (⟨jqN r, hmem⟩ : IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ)))
  rw [IntermediateField.adjoin.powerBasis_gen] at hg
  rw [IntermediateField.adjoin.powerBasis_dim, hmin_natdeg] at hg_deg

  have hconst_range : ∀ cf : F, algebraMap F (LaurentSeries K) cf ∈ (qExpand K r).range := by
    intro cf
    rw [halg, RingHom.comp_apply, RingHom.comp_apply]
    refine RingHom.mem_range.mpr ⟨qExpand K p (coeffEmb K (algebraMap F (LaurentSeries ℚ) cf)), ?_⟩
    rw [qExpand_qExpand, ← coeffEmb_qExpand]
    exact congrArg (coeffEmb K) (qExpand_congr (Nat.mul_comm r p) _)
  have hroot_range : ∀ y₀ ∈ (minpoly F (jqN p)).aroots (LaurentSeries K),
      y₀ ∈ (qExpand K r).range := by
    intro y₀ hy₀
    rw [hroots] at hy₀
    rcases Multiset.mem_cons.mp hy₀ with h | h
    · subst h
      refine RingHom.mem_range.mpr
        ⟨qExpand K (p * p) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)), ?_⟩
      rw [qExpand_qExpand]
      exact qExpand_congr (by ring) _
    · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp h
      exact RingHom.mem_range.mpr ⟨qTwist ((1 : Kˣ) * ζ ^ (b * (p * r / p))) (coeffEmb K jq), rfl⟩

  have hrpZ : ¬ ((r : ℤ) ∣ (p : ℤ)) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    exact hrp ((Nat.prime_dvd_prime_iff_eq hrr.out hpp.out).mp hdvd)
  have hrdvd : r ∣ p * r := dvd_mul_left r p

  have hkill : ∀ y : LaurentSeries K,
      (phiAtSeed data_r (coeffEmb K (qExpand ℚ (p * r) jq))).eval y = 0 →
      y ∈ (qExpand K r).range → y = coeffEmb K (qExpand ℚ (p * r) (jqN r)) := by
    intro y hy hyr
    have hseed : coeffEmb K (qExpand ℚ (p * r) jq)
        = qExpand K (r * p) (qTwist ((1 : Kˣ) ^ r) (coeffEmb K jq)) := by
      rw [one_pow, iota_jq, show TS K (p * r) (1 : Kˣ) = TS K (r * p) 1 from
        TS_congr (Nat.mul_comm p r) 1, TS, coeffEmb_jq]
    rw [phiAtSeed, hseed] at hy
    rcases (isRoot_prime_at_slot_iff (p * r) ζ hζ r hrdvd data_r p 1 y).mp hy with h | ⟨c, hc, h⟩
    · rw [h, one_pow, iota_jqN, coeffEmb_jq]
      show TS K (r * (r * p)) 1 = TS K (p * r * r) 1
      exact TS_congr (by ring) 1
    · exfalso
      rw [h] at hyr
      exact qExpand_qTwist_notMem_range_qExpand hrpZ _ hyr

  have hx_root : Polynomial.aeval
      (⟨jqN r, hmem⟩ : IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ)))
      (phiAtSeed data_r (⟨jq, hj⟩ : F)) = 0 := by
    apply aeval_intermediateField_eq_zero
    show Polynomial.aeval (jqN r) (phiAtSeed data_r (⟨jq, hj⟩ : F)) = 0
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map, hjq_coe]
    exact phiAtSeed_jq_eval r data_r

  have hval_key : ∀ y₀ ∈ (minpoly F (jqN p)).aroots (LaurentSeries K),
      Polynomial.aeval y₀ g = coeffEmb K (qExpand ℚ (p * r) (jqN r)) := by
    intro y₀ hy₀
    obtain ⟨σ, hσ_gen⟩ :
        ∃ σ : (IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) →ₐ[F] LaurentSeries K,
          σ (IntermediateField.AdjoinSimple.gen F (jqN p)) = y₀ :=
      ⟨(IntermediateField.algHomAdjoinIntegralEquiv F hα).symm ⟨y₀, hy₀⟩,
        IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hα ⟨y₀, hy₀⟩⟩
    have hσx_eq : σ ⟨jqN r, hmem⟩ = Polynomial.aeval y₀ g := by
      rw [hg, ← Polynomial.aeval_algHom_apply, hσ_gen]
    have hy_root : (phiAtSeed data_r (coeffEmb K (qExpand ℚ (p * r) jq))).eval
        (σ ⟨jqN r, hmem⟩) = 0 := by
      have h1 := Polynomial.aeval_algHom_apply σ
        (⟨jqN r, hmem⟩ : IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ)))
        (phiAtSeed data_r (⟨jq, hj⟩ : F))
      rw [hx_root, map_zero] at h1
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, ← Polynomial.map_map,
        phiAtSeed_map, hjq_coe, phiAtSeed_map, RingHom.comp_apply] at h1
      exact h1
    have hrange : σ ⟨jqN r, hmem⟩ ∈ (qExpand K r).range := by
      rw [hσx_eq, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      exact sum_mem fun i _ => mul_mem (hconst_range _) (pow_mem (hroot_range y₀ hy₀) i)
    rw [← hσx_eq]
    exact hkill _ hy_root hrange

  have hs_card : ((minpoly F (jqN p)).aroots (LaurentSeries K)).toFinset.card = p + 1 := by
    rw [Multiset.toFinset_card_of_nodup hM_nodup, hM_card]
  have hfin : coeffEmb K (qExpand ℚ (p * r) (jqN r)) ∈ (algebraMap F (LaurentSeries K)).range := by
    refine Polynomial.mem_range_of_eval_eq_const g _
      ((minpoly F (jqN p)).aroots (LaurentSeries K)).toFinset ?_ ?_
    · rw [hs_card]
      exact hg_deg
    · intro y₀ hy₀
      exact hval_key y₀ (Multiset.mem_toFinset.mp hy₀)
  obtain ⟨cf, hcf⟩ := RingHom.mem_range.mp hfin
  rw [halg, RingHom.comp_apply, RingHom.comp_apply] at hcf
  have h3 : algebraMap F (LaurentSeries ℚ) cf = jqN r := by
    have hinj : Function.Injective (coeffEmb K) := by
      rw [coeffEmb]
      exact coeffMap_injective (algebraMap ℚ K).injective
    exact qExpand_injective (p * r) (hinj hcf)
  rw [IntermediateField.algebraMap_apply] at h3
  exact hrF (h3 ▸ cf.2)

private theorem jqN_prime_not_mem_adjoin_key (S : Finset ℕ) : (∀ p ∈ S, p.Prime) →
    ∀ (r : ℕ) [NeZero r], Nat.Prime r → r ∉ S →
    jqN r ∉ IntermediateField.adjoin ℚ
      (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p}) := by
  induction S using Finset.induction_on with
  | empty =>
      intro _ r _ hr hrS hmem
      haveI : Fact (Nat.Prime r) := ⟨hr⟩
      have hset : (insert jq {x : LaurentSeries ℚ | ∃ p ∈ (∅ : Finset ℕ), ∃ _ : NeZero p, x = jqN p})
          = ({jq} : Set (LaurentSeries ℚ)) := by
        ext x
        simp
      rw [hset] at hmem

      have hM3 := finrank_adjoin_jqN_eq_of_prime r
      have hbot : IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          ({jqN r} : Set (LaurentSeries ℚ)) = ⊥ := by
        rw [IntermediateField.adjoin_simple_eq_bot_iff]
        exact IntermediateField.mem_bot.mpr ⟨⟨jqN r, hmem⟩, rfl⟩
      rw [hbot, IntermediateField.finrank_bot] at hM3
      have h2 := hr.two_le
      omega
  | insert q T hqT IH =>
      intro hS' r _ hr hrS' hmem
      have hq : Nat.Prime q := hS' q (Finset.mem_insert_self q T)
      have hT : ∀ p ∈ T, p.Prime := fun p hp => hS' p (Finset.mem_insert_of_mem hp)
      have hrq : r ≠ q := fun h => hrS' (h ▸ Finset.mem_insert_self q T)
      have hrT : r ∉ T := fun h => hrS' (Finset.mem_insert_of_mem h)
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      haveI : Fact (Nat.Prime r) := ⟨hr⟩
      have hqF : jqN q ∉ IntermediateField.adjoin ℚ
          (insert jq {x : LaurentSeries ℚ | ∃ p ∈ T, ∃ _ : NeZero p, x = jqN p}) := IH hT q hq hqT
      have hrF : jqN r ∉ IntermediateField.adjoin ℚ
          (insert jq {x : LaurentSeries ℚ | ∃ p ∈ T, ∃ _ : NeZero p, x = jqN p}) := IH hT r hr hrT
      have hj : jq ∈ IntermediateField.adjoin ℚ
          (insert jq {x : LaurentSeries ℚ | ∃ p ∈ T, ∃ _ : NeZero p, x = jqN p}) :=
        IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
      have hsets : (insert jq {x : LaurentSeries ℚ | ∃ p ∈ insert q T, ∃ _ : NeZero p, x = jqN p})
          = (insert jq {x : LaurentSeries ℚ | ∃ p ∈ T, ∃ _ : NeZero p, x = jqN p}) ∪ {jqN q} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union,
          Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨p', rfl | hp'T, hne, rfl⟩)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr rfl
          · exact Or.inl (Or.inr ⟨p', hp'T, hne, rfl⟩)
        · rintro ((rfl | ⟨p', hp'T, hne, rfl⟩) | rfl)
          · exact Or.inl rfl
          · exact Or.inr ⟨p', Or.inr hp'T, hne, rfl⟩
          · exact Or.inr ⟨q, Or.inl rfl, ⟨hq.ne_zero⟩, rfl⟩
      rw [hsets, ← IntermediateField.adjoin_adjoin_left,
        IntermediateField.mem_restrictScalars] at hmem
      obtain ⟨data_q, -, -⟩ := exists_phiIrreducible_evalSymm q
      obtain ⟨data_r, -, -⟩ := exists_phiIrreducible_evalSymm r
      haveI : NeZero (q * r) := ⟨Nat.mul_ne_zero hq.ne_zero hr.ne_zero⟩
      exact step_contradiction q r hrq (cycUnit (q * r)) (cycUnit_spec (q * r)) data_q data_r
        _ hj hqF hrF hmem

/-- **The two-prime separation**: `jqN r` is not in `ℚ(j, j(q ^ p) : p ∈ S)` for a
finite set `S` of primes not containing `r`. Verbatim from
`Theorems/Thm_ModularCurve_jqN_prime_not_mem_adjoin.lean`. -/
theorem jqN_prime_not_mem_adjoin (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ)
    [hr : Fact (Nat.Prime r)] (hrS : r ∉ S) : jqN r ∉ IntermediateField.adjoin ℚ
      (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p}) :=
  jqN_prime_not_mem_adjoin_key S hS r hr.out hrS

end ModularCurve

end
