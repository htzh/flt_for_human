/-
  T15 — descent by one prime, and the one-prime reduction of `Gen`.

  This is math/010 §4–§5. Two theorems:

  * `jqN_div_mem_modularFunctionField` — descent by one prime:
    `j(q ^ M) ∈ ℚ(j(q), j(q ^ (M * p)))`. It is the unique-common-root principle
    (`Polynomial.mem_range_of_unique_common_root`, T4's generic engine) applied to
    the level-`p` datum read at the level-`M * p` nome: `A` is `phiAtSeed data`
    at `jqN (M * p)` (T14), `B` is the minimal polynomial of `jqN M` mapped into
    `F = ℚ(j(q), j(q ^ (M * p)))`, and the caller's slot hypotheses `htw`/`hsp`
    rule out every common root other than `x₀ = j(q ^ (M * p))`. The tail strips
    the coefficient extension with `coeffEmb`-injectivity and `qExpand`-injectivity.
  * `modularFunctionField_eq_full_of` — the one-prime reduction of `Gen N`:
    the one-prime step `jqN M ∈ F_N` and `Gen M` for every factorization
    `N = M * p` give `modularFunctionField N = modularFunctionFieldFull N`.

  Both are `Inputs` fields of `FunctionFieldGeneration/Spine.lean`, so proving
  them shrinks the conditional capstone's debt **7 → 5** without changing the
  structure.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_modularFunctionField_eq_full_of.lean` lines 553–727.
  `P2M/Sol/S_ModularCurve_jqN_div_mem_modularFunctionField.lean` is byte-identical
  (the two `S_` files are one development, shipped twice), and both nodes have
  `Theorems/` wrappers, so the statements below are the wrappers' verbatim.

  ## Dedup

  The pin file's lines 28–542 are the shared prelude, already written once by T14
  (`Defs/PhiAtSlot.lean`, `PhiSlotRoots.lean`, `Defs/TS.lean`); nothing of it is
  re-copied here. Every mathematical ingredient is a ported theorem or a mathlib
  call — this module adds no new engine.

  ## Assumptions

  T4's `Polynomial.mem_range_of_unique_common_root` (`FieldTheory/CommonRoot`);
  T12's `exists_phiIrreducible_evalSymm`; T13's `splits_prime_at_slot`; T14's
  `phiAtSeed`/`phiAtSeed_map`/`phiAtSeed_monic`, `isRoot_prime_at_slot_iff`,
  `roots_prime_at_slot_roots_nodup`, `iota_jqN`, `TS_congr`; `Defs/Laurent`'s
  `coeffMap_injective`/`qExpand_injective`; `Defs/Fields`'s
  `modularFunctionField*`/`adjoin_jq_le`/`jqd_mem_full`.
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.Defs.Fields

set_option autoImplicit false
-- The pin installs the `Algebra F (LaurentSeries K)` instance (via `letI`) and a
-- `NeZero (d * m')` instance (via `haveI`); both are consumed by typeclass
-- search — `algebraMap F (LaurentSeries K)` and the `modularFunctionField`
-- family — so the style linter's `have` preference does not apply. Same local
-- disable as `PhiGenSplits.lean` and `ModularPolynomialProperties.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

/-- **Descent by one prime**: `j(q ^ M) ∈ ℚ(j(q), j(q ^ (M * p)))`.

The unique-common-root principle applied to the level-`p` modular polynomial read
at the level-`M * p` nome; the two slot hypotheses `htw`/`hsp` (later discharged
by T19's slot product) rule out every other common root. Verbatim from
`Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean`. -/
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (htw : ∀ y : LaurentSeries K,
      Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
            (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
              (LaurentSeries ℚ)))) = 0 →
        ∀ w : Kˣ, y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq)) → w = 1)
    (hsp : ∀ y : LaurentSeries K,
      Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
            (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
              (LaurentSeries ℚ)))) = 0 →
        y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))) :
    jqN M ∈ modularFunctionField (M * p) := by
  classical
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  have hpN : p ∣ M * p := dvd_mul_left p M

  set F := modularFunctionField (M * p) with hF
  have hjNmem : jqN (M * p) ∈ F :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
  have hle : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ F :=
    adjoin_jq_le (M * p)
  letI : Algebra F (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra

  set A : Polynomial F := phiAtSeed data (⟨jqN (M * p), hjNmem⟩ : F) with hA

  let ι₀ : (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* F :=
    { toFun := fun x => ⟨(x : LaurentSeries ℚ), hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  set B : Polynomial F :=
    (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map ι₀
    with hB

  have hmapA : A.map (algebraMap F (LaurentSeries K))
      = phiAtSeed data (coeffEmb K (qExpand ℚ (M * p) (jqN (M * p)))) :=
    phiAtSeed_map data _ _
  have hseed : coeffEmb K (qExpand ℚ (M * p) (jqN (M * p)))
      = qExpand K (p * (M * p * M)) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq)) := by
    have h2 : TS K ((M * p) * (M * p)) 1 = TS K (p * (M * p * M)) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
      exact TS_congr (by ring) 1
    exact (iota_jqN (M * p) (M * p)).trans h2
  have hdist : coeffEmb K (qExpand ℚ (M * p) (jqN M))
      = qExpand K (M * p * M) (qTwist (1 * ζ ^ (0 * (M * p / p))) (coeffEmb K jq)) := by
    have h2 : TS K ((M * p) * M) 1 = TS K (M * p * M) (1 * ζ ^ (0 * (M * p / p))) := by
      rw [Nat.zero_mul, pow_zero, mul_one]
    exact (iota_jqN (M * p) M).trans h2
  have hspread : coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))
      = qExpand K (p * (p * (M * p * M))) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) := by
    have h2 : TS K ((M * p) * (M * p * p)) 1
        = TS K (p * (p * (M * p * M))) ((1 : Kˣ) ^ (p * p)) := by
      rw [one_pow]
      exact TS_congr (by ring) 1
    exact (iota_jqN (M * p) (M * p * p)).trans h2

  have hrootA : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 ↔
        (y = qExpand K (p * (p * (M * p * M))) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) ∨
          ∃ b < p, y = qExpand K (M * p * M)
            (qTwist (1 * ζ ^ (b * (M * p / p))) (coeffEmb K jq))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hseed]
    exact isRoot_prime_at_slot_iff (M * p) ζ hζ p hpN data (M * p * M) 1 y

  have hcomp : (algebraMap F (LaurentSeries K)).comp ι₀
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp
          (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (LaurentSeries ℚ)) := RingHom.ext fun x => rfl

  have hBev : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 →
      Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
          (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (LaurentSeries ℚ)))) = 0 := by
    intro y hy
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map] at hy
    rwa [hcomp] at hy

  have hA0 : A ≠ 0 := (phiAtSeed_monic data _).ne_zero
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [hmapA, hseed, phiAtSeed,
      PhiGen.splits_prime_at_slot (M * p) ζ hζ p hpN data (M * p * M) 1]
    exact (Polynomial.Splits.X_sub_C _).mul
      (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hAnd : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hseed, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup (M * p) ζ hζ p hpN data (M * p * M) 1

  set x₀ : LaurentSeries K := coeffEmb K (qExpand ℚ (M * p) (jqN M)) with hx₀
  have hxA : Polynomial.aeval x₀ A = 0 :=
    (hrootA x₀).mpr (Or.inr ⟨0, hp.out.pos, hdist⟩)
  have hxB : Polynomial.aeval x₀ B = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, Polynomial.eval_map]
    have hx₀ψ : x₀ = ((coeffEmb K).comp (qExpand ℚ (M * p))) (jqN M) := rfl
    rw [hx₀ψ, Polynomial.eval₂_hom]
    have hmp := minpoly.aeval
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hmp
    rw [hmp, map_zero]

  have huniq : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x₀ := by
    intro y hyA hyB
    rcases (hrootA y).mp hyA with hy1 | ⟨b, hb, hy1⟩
    · exact absurd (hy1.trans hspread.symm) (hsp y (hBev y hyB))
    · have hw := htw y (hBev y hyB) (1 * ζ ^ (b * (M * p / p))) hy1
      rw [one_mul] at hw
      have hb0 : b = 0 := by
        have hord : (M * p) ∣ b * M := by
          have hval : (ζ : K) ^ (b * (M * p / p)) = 1 := by
            have := congrArg Units.val hw
            simpa using this
          rw [Nat.mul_div_cancel M hp.out.pos] at hval
          exact (hζ.pow_eq_one_iff_dvd _).mp hval
        have hpb : p ∣ b := by
          have h2 : M * p ∣ M * b := by rwa [Nat.mul_comm b M] at hord
          exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne M))).mp h2
        exact Nat.eq_zero_of_dvd_of_lt hpb hb
      rw [hb0] at hy1
      exact hy1.trans hdist.symm

  have hrange := Polynomial.mem_range_of_unique_common_root A B hA0 hAs hAnd x₀ hxA hxB huniq
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hrange
  have hf' : coeffEmb K (qExpand ℚ (M * p) ((f : LaurentSeries ℚ)))
      = coeffEmb K (qExpand ℚ (M * p) (jqN M)) := hf
  have hemb : Function.Injective (coeffEmb K) :=
    coeffMap_injective ((algebraMap ℚ K).injective)
  have hval : (f : LaurentSeries ℚ) = jqN M := qExpand_injective (M * p) (hemb hf')
  rw [← hval]
  exact f.2

/-- **The one-prime reduction of `Gen`**: if every factorization `N = M * p` has
the one-prime step `jqN M ∈ F_N` and `Gen M`, then `modularFunctionField N` is
the full divisor field. Verbatim from
`Theorems/Thm_ModularCurve_modularFunctionField_eq_full_of.lean`. -/
theorem modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      jqN M ∈ modularFunctionField N)
    (hgen' : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      modularFunctionField M = modularFunctionFieldFull M) :
    modularFunctionField N = modularFunctionFieldFull N := by
  refine le_antisymm (modularFunctionField_le_full N) ?_
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd0, hdN, rfl⟩
  rcases eq_or_ne d N with rfl | hdlt
  · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
  ·
    obtain ⟨m, hm⟩ := hdN
    have hm1 : m ≠ 1 := fun h1 => hdlt (by rw [hm, h1, Nat.mul_one])
    have hm0 : m ≠ 0 := fun h0 => NeZero.ne N (by rw [hm, h0, Nat.mul_zero])
    have hq : m.minFac.Prime := Nat.minFac_prime hm1
    obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
    have hm'0 : m' ≠ 0 := fun h0 => hm0 (by rw [hm', h0, Nat.mul_zero])
    haveI : NeZero (d * m') := ⟨Nat.mul_ne_zero hd0.out hm'0⟩
    have hdm' : (d * m') * m.minFac = N := by
      rw [Nat.mul_assoc, Nat.mul_comm m' m.minFac, ← hm', ← hm]
    have hmem : jqN (d * m') ∈ modularFunctionField N := hstep (d * m') m.minFac hq hdm'
    have hfull : modularFunctionField (d * m') = modularFunctionFieldFull (d * m') :=
      hgen' (d * m') m.minFac hq hdm'
    have hsub : modularFunctionFieldFull (d * m') ≤ modularFunctionField N := by
      rw [← hfull, modularFunctionField, IntermediateField.adjoin_le_iff]
      rintro y (rfl | hy)
      · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hmem
    exact hsub (jqd_mem_full (d * m') ⟨m', rfl⟩)

end ModularCurve

end
