/-
  T17 — the non-membership tower and the two-prime separation.

  This is the non-membership half of the strong induction (math/010 §6a), two
  statements in one module:

  * `jqN_pow_not_mem_adjoin_full` — the **prime-power tower**, an `Inputs` field:
    `j(q ^ (p ^ (a + 2))) ∉ ℚ(F_M^full, j(q ^ p), …, j(q ^ (p ^ (a + 1))))`. The
    proof builds the tower of intermediate fields
    `C_i = ℚ(F_M^full, j(q ^ (p ^ j)) : j ≤ i)` and, by strong induction on `a`,
    a compatible family of `ℚ`-algebra homs `σ_i : C_i → K((q))` whose images lie
    in a shrinking `qExpand` range. The modular equation `Φ_p` has both
    `j(q ^ (p ^ (a + 2)))` and `j(q ^ (p ^ a))` as roots of
    `Φ_p(j(q ^ (p ^ (a + 1))), ·)`; pushing it through `σ` forces both to the
    *same* root, and `σ` injective gives `j(q ^ (p ^ (a + 2))) = j(q ^ (p ^ a))`,
    contradicted by the `q ^ (-(p ^ a))` coefficient (1 vs 0).
  * `jqN_prime_not_mem_adjoin` — the **two-prime separation**, public `Theorems/`
    API: `jqN r` is not in `ℚ(j, j(q ^ p) : p ∈ S)` for a finite set `S` of
    primes with `r ∉ S`. The engine is `step_contradiction`: if
    `j(q ^ r) = g(j(q ^ p))`, then `g` has degree `< p + 1` and is constant on
    the `p + 1` roots of `Φ_p(j(q), ·)` (a T4 `CommonRoot` engine), so
    `j(q ^ r) ∈ ℚ(j)`, contradicting
    `[ℚ(j)(j(q ^ p)) : ℚ(j)] = p + 1` — T16's first statement. The Finset
    induction over `S` is `jqN_prime_not_mem_adjoin_key`.

  The tower is an `Inputs` field, so proving it takes the conditional capstone's
  debt down by one. The base is **not** on the capstone's path (T19's private
  M-arbitrary lemma is what discharges `Inputs.jqN_prime_not_mem_full`); it is
  public `Theorems/` API, consumed by `relfinrank_adjoin_primes`,
  `relfinrank_full_mul_prime` and `jqN_sq_not_mem_adjoin`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` (node 443–985; lines
  400–442 are T14's helpers) and
  `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_adjoin.lean` (node 426–651; lines
  406–425 are T14's helpers). Both public statements are the `Theorems/` wrappers'
  verbatim.

  ## Dedup

  Both files open with T14's ~370-line prelude, already written once in
  `Defs/PhiAtSlot.lean`, `Defs/TS.lean`, `Defs/Cyclotomic.lean` and
  `Defs/Jq.lean`; none of it is re-copied here. The six tower helpers and the two
  base helpers that the pin repeats are those T14 declarations, imported. The
  pin's two `set_option maxHeartbeats 3200000 in` (at 715 and 961) are omitted —
  they are below the port's global `4000000`.

  ## Assumptions

  T4's `mem_range_of_eval_eq_const` (`FieldTheory/CommonRoot`); T12's
  `exists_phiIrreducible_evalSymm`; T13's `PhiGen.splits_prime_at_slot`; T14's
  `phiAtSeed*`, `isRoot_prime_at_slot_iff`, `roots_prime_at_slot*`, `iota_jq`,
  `iota_jqN`, `TS_congr`/`TS_injective`,
  `qExpand_qTwist_notMem_range_qExpand`; T16's
  `finrank_adjoin_jqN_prime_of_not_mem`; `Defs/Laurent`'s `coeffMap_injective`/
  `qExpand_injective`; `Defs/Cyclotomic`'s `cycUnit`/`cycUnit_spec`;
  `Defs/Fields`'s `modularFunctionFieldFull`/`jqd_mem_full`; `Defs/Jq`'s
  `coeff_jq_neg_one`/`jqN_one`/`jqN_congr`.
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
-- `letI`) and the `IsCyclotomicExtension` instance; both are consumed by
-- typeclass search, so the style linter's `have` preference does not apply. Same
-- local disable as `Descent.lean`/`DegreeStep.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

open PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## The prime-power tower -/

private theorem nat_ne_of_mul {a b : ℕ} (ha : 0 < a) (hb : 2 ≤ b) : a * b ≠ a := by
  intro h
  have h2 : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb
  rw [h] at h2
  omega

omit [Algebra ℚ K] in
private theorem mem_range_qExpand_of_mul {a b : ℕ} [NeZero a] [NeZero b] {z : LaurentSeries K}
    (h : z ∈ (qExpand K (a * b)).range) : z ∈ (qExpand K b).range := by
  obtain ⟨w, rfl⟩ := RingHom.mem_range.mp h
  refine RingHom.mem_range.mpr ⟨qExpand K a w, ?_⟩
  rw [qExpand_qExpand]
  exact qExpand_congr (Nat.mul_comm b a) _

omit [Algebra ℚ K] in
private theorem range_qExpand_congr {A A' : ℕ} [NeZero A] [NeZero A'] (h : A = A') :
    (qExpand K A).range = (qExpand K A').range := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨w, (qExpand_congr h w).symm⟩
  · rintro ⟨w, rfl⟩; exact ⟨w, qExpand_congr h w⟩

private def chainField (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ ((modularFunctionFieldFull M : Set (LaurentSeries ℚ))
    ∪ {x : LaurentSeries ℚ | ∃ j : ℕ, j ≤ i ∧ x = jqN (p ^ j)})

private theorem mem_chainField (M p : ℕ) [NeZero M] [NeZero p] {j i : ℕ} (hj : j ≤ i) :
    jqN (p ^ j) ∈ chainField M p i :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, hj, rfl⟩)

private theorem full_le_chainField (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    modularFunctionFieldFull M ≤ chainField M p i :=
  fun _ hx => IntermediateField.subset_adjoin ℚ _ (Or.inl hx)

private theorem chainField_zero (M p : ℕ) [NeZero M] [NeZero p] :
    chainField M p 0 = modularFunctionFieldFull M := by
  apply le_antisymm
  · rw [chainField, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact hx
    · rw [Nat.le_zero] at hj
      subst hj
      rw [show jqN (p ^ 0) = jq from (jqN_congr (pow_zero p)).trans jqN_one]
      have h2 := jqd_mem_full M (one_dvd M)
      rwa [qExpand_one_apply] at h2
  · exact full_le_chainField M p 0

private theorem chainField_mono (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    chainField M p i ≤ chainField M p (i + 1) := by
  rw [chainField, chainField]
  refine IntermediateField.adjoin.mono ℚ _ _ (Set.union_subset_union_right _ ?_)
  rintro z ⟨j, hj, rfl⟩
  exact ⟨j, le_trans hj (Nat.le_succ i), rfl⟩

private theorem chainField_succ (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    chainField M p (i + 1) = IntermediateField.adjoin ℚ
      ((chainField M p i : Set (LaurentSeries ℚ)) ∪ {jqN (p ^ i * p)}) := by
  apply le_antisymm
  · rw [chainField, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact IntermediateField.subset_adjoin ℚ _
        (Or.inl (full_le_chainField M p i hx))
    · rcases Nat.lt_or_ge j (i + 1) with h | h
      · exact IntermediateField.subset_adjoin ℚ _
          (Or.inl (mem_chainField M p (Nat.lt_succ_iff.mp h)))
      · have hje : j = i + 1 := le_antisymm hj h
        subst hje
        refine IntermediateField.subset_adjoin ℚ _ (Or.inr ?_)
        rw [Set.mem_singleton_iff]
        exact jqN_congr (pow_succ p i)
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact chainField_mono M p i hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [show jqN (p ^ i * p) = jqN (p ^ (i + 1)) from jqN_congr (pow_succ p i).symm]
      exact mem_chainField M p (le_refl (i + 1))

private theorem chain_extend (p e s : ℕ) [hpp : Fact (Nat.Prime p)] [NeZero e] [NeZero s]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * e * s)) (dp : ModularPolynomialData p)
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd_mem : jqN d ∈ F) (hx_not : jqN (d * p) ∉ F)
    (t : ℕ)
    (hσd : σ ⟨jqN d, hd_mem⟩
      = qExpand K (p * e) (qTwist (ζ ^ (t * (p * e))) (coeffEmb K jq)))
    (hrange : ∀ y : F, σ y ∈ (qExpand K (p * e)).range)
    (G : IntermediateField ℚ (LaurentSeries ℚ))
    (hG : G = IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {jqN (d * p)})) :
    ∃ (σ' : G →+* LaurentSeries K) (t' : ℕ),
      (∀ (z : F) (hz : (z : LaurentSeries ℚ) ∈ G), σ' ⟨z, hz⟩ = σ z) ∧
      (∀ hx : jqN (d * p) ∈ G, σ' ⟨jqN (d * p), hx⟩
        = qExpand K e (qTwist (ζ ^ (t' * e)) (coeffEmb K jq))) ∧
      (∀ y : G, σ' y ∈ (qExpand K e).range) := by
  subst hG
  classical
  have hp0 : 0 < p := hpp.out.pos

  have hP_aeval : Polynomial.aeval (jqN (d * p)) (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map]
    exact phiAtSeed_jqN_eval p dp d
  have hint : IsIntegral F (jqN (d * p)) :=
    ⟨phiAtSeed dp (⟨jqN d, hd_mem⟩ : F), phiAtSeed_monic dp _, by
      rwa [Polynomial.aeval_def] at hP_aeval⟩
  have hdvd : minpoly F (jqN (d * p)) ∣ phiAtSeed dp (⟨jqN d, hd_mem⟩ : F) :=
    minpoly.dvd F _ hP_aeval

  letI : Algebra F (LaurentSeries K) := σ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = σ := RingHom.algebraMap_toAlgebra σ
  have hpB : p ∣ p * e * s := ⟨e * s, by ring⟩
  have hBdiv : p * e * s / p = e * s := by
    rw [show p * e * s = p * (e * s) from by ring, Nat.mul_div_cancel_left _ hp0]
  have hunit_seed : ζ ^ (t * (p * e)) = (ζ ^ (t * e)) ^ p := by
    rw [← pow_mul]
    congr 1
    ring
  have hmapP : (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed dp (qExpand K (p * e) (qTwist ((ζ ^ (t * e)) ^ p) (coeffEmb K jq))) := by
    rw [phiAtSeed_map, halg, hσd, hunit_seed]
  have hroots_iff : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)) = 0 ↔
      (y = qExpand K (p * (p * e)) (qTwist ((ζ ^ (t * e)) ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ c < p, y = qExpand K e
          (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapP, phiAtSeed]
    have h := isRoot_prime_at_slot_iff (p * e * s) ζ hζ p hpB dp e (ζ ^ (t * e)) y
    rw [hBdiv] at h
    exact h

  have hPmap_ne : (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K)) ≠ 0 :=
    ((phiAtSeed_monic dp _).map _).ne_zero
  have hPmap_splits : ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map
      (algebraMap F (LaurentSeries K))).Splits := by
    rw [hmapP, phiAtSeed, PhiGen.splits_prime_at_slot (p * e * s) ζ hζ p hpB dp e
      (ζ ^ (t * e))]
    exact (Polynomial.Splits.X_sub_C _).mul
      (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hPmap_nodup : ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map
      (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapP, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup (p * e * s) ζ hζ p hpB dp e (ζ ^ (t * e))
  have hm_dvd_map : (minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))
      ∣ (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K)) :=
    Polynomial.map_dvd _ hdvd
  have hm_roots_le : ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots
      ≤ ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K))).roots :=
    Polynomial.roots.le_of_dvd hPmap_ne hm_dvd_map
  have hm_splits : ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).Splits :=
    hPmap_splits.of_dvd hPmap_ne hm_dvd_map
  have hm_deg : 2 ≤ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).natDegree := by
    rw [(minpoly.monic hint).natDegree_map, minpoly.two_le_natDegree_iff hint]
    intro hmem
    obtain ⟨w, hw⟩ := hmem
    rw [← hw] at hx_not
    exact hx_not w.2
  have hm_nodup : (((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots).Nodup :=
    Multiset.nodup_of_le hm_roots_le hPmap_nodup
  have hroot_trans : ∀ y ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots,
      Polynomial.aeval y (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)) = 0 := by
    intro y hy
    have h1 : y ∈ ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map
        (algebraMap F (LaurentSeries K))).roots := Multiset.mem_of_le hm_roots_le hy
    rw [Polynomial.mem_roots hPmap_ne] at h1
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact h1

  have h2d : ∃ y₁ ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots,
      ∃ y₂ ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots, y₁ ≠ y₂ := by
    have hcard : 1 < (((minpoly F (jqN (d * p))).map
        (algebraMap F (LaurentSeries K))).roots).toFinset.card := by
      rw [Multiset.toFinset_card_of_nodup hm_nodup, ← hm_splits.natDegree_eq_card_roots]
      omega
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp hcard
    exact ⟨y₁, Multiset.mem_toFinset.mp hy₁, y₂, Multiset.mem_toFinset.mp hy₂, hne⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := h2d
  have hex_twist : ∃ c < p, qExpand K e (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq))
      ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots := by
    rcases (hroots_iff y₁).mp (hroot_trans y₁ hy₁) with h1 | ⟨c, hc, h1⟩
    · rcases (hroots_iff y₂).mp (hroot_trans y₂ hy₂) with h2 | ⟨c, hc, h2⟩
      · exact absurd (h1.trans h2.symm) hne
      · exact ⟨c, hc, h2 ▸ hy₂⟩
    · exact ⟨c, hc, h1 ▸ hy₁⟩
  obtain ⟨c, hc, htwist_mem⟩ := hex_twist
  have htwist_aroots : qExpand K e (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq))
      ∈ (minpoly F (jqN (d * p))).aroots (LaurentSeries K) := htwist_mem

  obtain ⟨ψ, hψ_gen⟩ : ∃ ψ : IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ))
        →ₐ[F] LaurentSeries K,
      ψ (IntermediateField.AdjoinSimple.gen F (jqN (d * p)))
        = qExpand K e (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq)) :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv F hint).symm ⟨_, htwist_aroots⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hint ⟨_, htwist_aroots⟩⟩

  have hle : ∀ {z : LaurentSeries ℚ},
      z ∈ IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {jqN (d * p)}) →
      z ∈ IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)) := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact (IntermediateField.adjoin F
          ({jqN (d * p)} : Set (LaurentSeries ℚ))).algebraMap_mem ⟨w, hw⟩
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact IntermediateField.subset_adjoin F _ rfl
    | algebraMap q =>
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    | add x y hx hy ihx ihy => exact add_mem ihx ihy
    | inv x hx ihx => exact inv_mem ihx
    | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
  refine ⟨{
    toFun := fun z => ψ ⟨z.1, hle z.2⟩
    map_one' := (congrArg ψ (Subtype.ext rfl)).trans (map_one ψ)
    map_mul' := fun z w => by
      have h1 : (⟨(z * w).1, hle (z * w).2⟩ :
          IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
          = ⟨z.1, hle z.2⟩ * ⟨w.1, hle w.2⟩ := Subtype.ext rfl
      rw [h1, map_mul]
    map_zero' := (congrArg ψ (Subtype.ext rfl)).trans (map_zero ψ)
    map_add' := fun z w => by
      have h1 : (⟨(z + w).1, hle (z + w).2⟩ :
          IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
          = ⟨z.1, hle z.2⟩ + ⟨w.1, hle w.2⟩ := Subtype.ext rfl
      rw [h1, map_add] }, t + c * s, ?_, ?_, ?_⟩
  ·
    intro z hz
    show ψ ⟨(z : LaurentSeries ℚ), _⟩ = σ z
    have h1 : (⟨(z : LaurentSeries ℚ), hle hz⟩ :
        IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
        = algebraMap F (IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ))) z :=
      Subtype.ext rfl
    rw [h1, AlgHom.commutes, halg]
  ·
    intro hx
    show ψ ⟨jqN (d * p), _⟩ = _
    have h1 : (⟨jqN (d * p), hle hx⟩ :
        IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
        = IntermediateField.AdjoinSimple.gen F (jqN (d * p)) := Subtype.ext rfl
    have hu : ζ ^ (t * e) * ζ ^ (c * (e * s)) = ζ ^ ((t + c * s) * e) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h1, hψ_gen, hu]
  ·
    intro z
    show ψ ⟨z.1, hle z.2⟩ ∈ (qExpand K e).range
    obtain ⟨g, hg⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval'
      (⟨z.1, hle z.2⟩ : IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
    rw [IntermediateField.adjoin.powerBasis_gen] at hg
    rw [hg, ← Polynomial.aeval_algHom_apply, hψ_gen, Polynomial.aeval_def,
      Polynomial.eval₂_eq_sum_range]
    refine sum_mem fun i _ => mul_mem ?_ (pow_mem ?_ i)
    · rw [halg]
      exact mem_range_qExpand_of_mul (hrange _)
    · exact RingHom.mem_range.mpr
        ⟨qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq), rfl⟩

/-! ## The tower endgame -/

private theorem chain_endgame (M p : ℕ) [NeZero M] [hp : Fact (Nat.Prime p)] (a : ℕ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 2)))
    (dp : ModularPolynomialData p) (hsp : EvalSymm dp.Φ)
    (hF : jqN p ∉ modularFunctionFieldFull M)
    (hIH : ∀ a' : ℕ, a' < a → jqN (p ^ (a' + 2)) ∉ chainField M p (a' + 1))
    (hmem : jqN (p ^ (a + 2)) ∈ chainField M p (a + 1)) : False := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hp2 : 2 ≤ p := hp.out.two_le
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)

  have hnot : ∀ i : ℕ, i ≤ a → jqN (p ^ i * p) ∉ chainField M p i := by
    intro i hi
    rw [show jqN (p ^ i * p) = jqN (p ^ (i + 1)) from jqN_congr (pow_succ p i).symm]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [chainField_zero]
      rw [show jqN (p ^ (0 + 1)) = jqN p from jqN_congr (by rw [zero_add, pow_one])]
      exact hF
    · have heq1 : jqN (p ^ (i + 1)) = jqN (p ^ (i - 1 + 2)) :=
        jqN_congr (congrArg (fun n => p ^ n) (by omega))
      have heq2 : chainField M p i = chainField M p (i - 1 + 1) :=
        congrArg (chainField M p) (by omega)
      rw [heq1, heq2]
      exact hIH (i - 1) (by omega)

  have chain : ∀ i : ℕ, i ≤ a →
      ∃ (σ : chainField M p i →+* LaurentSeries K) (t : ℕ),
        (σ ⟨jqN (p ^ i), mem_chainField M p (le_refl i)⟩
          = qExpand K (M * p ^ (a + 2 - i))
            (qTwist (ζ ^ (t * (M * p ^ (a + 2 - i)))) (coeffEmb K jq))) ∧
        (∀ y : chainField M p i, σ y ∈ (qExpand K (M * p ^ (a + 2 - i))).range) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨((coeffEmb K).comp (qExpand ℚ (M * p ^ (a + 2)))).comp
        (algebraMap (chainField M p 0) (LaurentSeries ℚ)), 0, ?_, ?_⟩
      · show coeffEmb K (qExpand ℚ (M * p ^ (a + 2)) (jqN (p ^ 0))) = _
        rw [show jqN (p ^ 0) = jq from (jqN_congr (pow_zero p)).trans jqN_one, iota_jq,
          zero_mul, pow_zero]
        show TS K (M * p ^ (a + 2)) 1 = TS K (M * p ^ (a + 2 - 0)) 1
        exact TS_congr (by rw [Nat.sub_zero]) 1
      · intro y
        show coeffEmb K (qExpand ℚ (M * p ^ (a + 2)) (y : LaurentSeries ℚ)) ∈ _
        rw [coeffEmb_qExpand]
        rw [← range_qExpand_congr (show (M * p ^ (a + 2) : ℕ) = M * p ^ (a + 2 - 0) from by
          rw [Nat.sub_zero])]
        exact RingHom.mem_range.mpr ⟨coeffEmb K (y : LaurentSeries ℚ), rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨σ, t, hσtop, hσrange⟩ := ih (Nat.le_of_succ_le hi)
      have hpow_step : M * p ^ (a + 2 - i) = p * (M * p ^ (a + 2 - (i + 1))) := by
        rw [show a + 2 - i = (a + 2 - (i + 1)) + 1 from by omega, pow_succ]
        ring
      have hσtop' : σ ⟨jqN (p ^ i), mem_chainField M p (le_refl i)⟩
          = qExpand K (p * (M * p ^ (a + 2 - (i + 1))))
            (qTwist (ζ ^ (t * (p * (M * p ^ (a + 2 - (i + 1)))))) (coeffEmb K jq)) := by
        rw [hσtop]
        have h1 : ζ ^ (t * (M * p ^ (a + 2 - i)))
            = ζ ^ (t * (p * (M * p ^ (a + 2 - (i + 1))))) := by
          rw [hpow_step]
        rw [h1]
        show TS K (M * p ^ (a + 2 - i)) _ = TS K (p * (M * p ^ (a + 2 - (i + 1)))) _
        exact TS_congr hpow_step _
      have hζ' : IsPrimitiveRoot (ζ : K) (p * (M * p ^ (a + 2 - (i + 1))) * p ^ i) := by
        have hBs : M * p ^ (a + 2) = p * (M * p ^ (a + 2 - (i + 1))) * p ^ i := by
          have h1 : (1 : ℕ) + (a + 2 - (i + 1)) + i = a + 2 := by omega
          calc M * p ^ (a + 2) = M * p ^ (1 + (a + 2 - (i + 1)) + i) := by rw [h1]
            _ = p * (M * p ^ (a + 2 - (i + 1))) * p ^ i := by
                rw [pow_add, pow_add, pow_one]; ring
        exact hBs ▸ hζ
      have hσrange' : ∀ y : chainField M p i,
          σ y ∈ (qExpand K (p * (M * p ^ (a + 2 - (i + 1))))).range := by
        intro y
        have h := hσrange y
        rwa [range_qExpand_congr hpow_step] at h
      obtain ⟨σ', t', hcompat, hσ'new, hσ'range⟩ :=
        chain_extend p (M * p ^ (a + 2 - (i + 1))) (p ^ i) ζ hζ' dp (chainField M p i) σ
          (p ^ i) (mem_chainField M p (le_refl i)) (hnot i (Nat.le_of_succ_le hi)) t
          hσtop' hσrange' (chainField M p (i + 1)) (chainField_succ M p i)
      refine ⟨σ', t', ?_, hσ'range⟩
      have hxmem : jqN (p ^ i * p) ∈ chainField M p (i + 1) := by
        rw [show jqN (p ^ i * p) = jqN (p ^ (i + 1)) from jqN_congr (pow_succ p i).symm]
        exact mem_chainField M p (le_refl (i + 1))
      have hmk : (⟨jqN (p ^ (i + 1)), mem_chainField M p (le_refl (i + 1))⟩ :
          chainField M p (i + 1)) = ⟨jqN (p ^ i * p), hxmem⟩ :=
        Subtype.ext (jqN_congr (pow_succ p i))
      rw [hmk]
      exact hσ'new hxmem

  obtain ⟨σa, ta, hatop, harange⟩ := chain a (le_refl a)
  have hpow_top : M * p ^ (a + 2 - a) = p * (M * p) := by
    rw [show a + 2 - a = 2 from by omega]
    ring
  have hatop' : σa ⟨jqN (p ^ a), mem_chainField M p (le_refl a)⟩
      = qExpand K (p * (M * p)) (qTwist (ζ ^ (ta * (p * (M * p)))) (coeffEmb K jq)) := by
    rw [hatop]
    have h1 : ζ ^ (ta * (M * p ^ (a + 2 - a))) = ζ ^ (ta * (p * (M * p))) := by
      rw [hpow_top]
    rw [h1]
    show TS K (M * p ^ (a + 2 - a)) _ = TS K (p * (M * p)) _
    exact TS_congr hpow_top _
  have harange' : ∀ y : chainField M p a, σa y ∈ (qExpand K (p * (M * p))).range := by
    intro y
    have h := harange y
    rwa [range_qExpand_congr hpow_top] at h
  have hζtop : IsPrimitiveRoot (ζ : K) (p * (M * p) * p ^ a) := by
    have hBs : M * p ^ (a + 2) = p * (M * p) * p ^ a := by
      have h1 : (1 : ℕ) + 1 + a = a + 2 := by omega
      calc M * p ^ (a + 2) = M * p ^ (1 + 1 + a) := by rw [h1]
        _ = p * (M * p) * p ^ a := by rw [pow_add, pow_add, pow_one]; ring
    exact hBs ▸ hζ
  obtain ⟨σ, tt, hcompat, hnew, hrange⟩ :=
    chain_extend p (M * p) (p ^ a) ζ hζtop dp (chainField M p a) σa (p ^ a)
      (mem_chainField M p (le_refl a)) (hnot a (le_refl a)) ta hatop' harange'
      (chainField M p (a + 1)) (chainField_succ M p a)

  have hmem_a1 : jqN (p ^ (a + 1)) ∈ chainField M p (a + 1) :=
    mem_chainField M p (le_refl (a + 1))
  have hmem_a : jqN (p ^ a) ∈ chainField M p (a + 1) :=
    mem_chainField M p (Nat.le_succ a)

  have hrel_up_Ω : (phiAtSeed dp (jqN (p ^ (a + 1)))).eval (jqN (p ^ (a + 2))) = 0 := by
    have h := phiAtSeed_jqN_eval p dp (p ^ (a + 1))
    rwa [show jqN (p ^ (a + 1) * p) = jqN (p ^ (a + 2)) from
      jqN_congr (pow_succ p (a + 1)).symm] at h
  have hrel_dn_Ω : (phiAtSeed dp (jqN (p ^ (a + 1)))).eval (jqN (p ^ a)) = 0 := by
    have h := phiAtSeed_jqN_eval_down p dp hsp (p ^ a)
    rwa [show jqN (p ^ a * p) = jqN (p ^ (a + 1)) from jqN_congr (pow_succ p a).symm] at h
  have hrel_up_E : (phiAtSeed dp (⟨jqN (p ^ (a + 1)), hmem_a1⟩ : chainField M p (a + 1))).eval
      (⟨jqN (p ^ (a + 2)), hmem⟩ : chainField M p (a + 1)) = 0 :=
    phiAtSeed_eval_of_injective dp _ _
      (algebraMap (chainField M p (a + 1)) (LaurentSeries ℚ)) Subtype.val_injective hrel_up_Ω
  have hrel_dn_E : (phiAtSeed dp (⟨jqN (p ^ (a + 1)), hmem_a1⟩ : chainField M p (a + 1))).eval
      (⟨jqN (p ^ a), hmem_a⟩ : chainField M p (a + 1)) = 0 :=
    phiAtSeed_eval_of_injective dp _ _
      (algebraMap (chainField M p (a + 1)) (LaurentSeries ℚ)) Subtype.val_injective hrel_dn_Ω

  have hσ_a1 : σ ⟨jqN (p ^ (a + 1)), hmem_a1⟩
      = qExpand K (M * p) (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)) := by
    have hx : jqN (p ^ a * p) ∈ chainField M p (a + 1) := by
      rw [show jqN (p ^ a * p) = jqN (p ^ (a + 1)) from jqN_congr (pow_succ p a).symm]
      exact hmem_a1
    have hmk : (⟨jqN (p ^ (a + 1)), hmem_a1⟩ : chainField M p (a + 1))
        = ⟨jqN (p ^ a * p), hx⟩ := Subtype.ext (jqN_congr (pow_succ p a))
    rw [hmk]
    exact hnew hx

  have hz_up : (phiAtSeed dp (qExpand K (M * p)
      (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval
      (σ ⟨jqN (p ^ (a + 2)), hmem⟩) = 0 := by
    have h := phiAtSeed_eval_map dp _ _
      (σ : chainField M p (a + 1) →+* LaurentSeries K) hrel_up_E
    rwa [hσ_a1] at h
  have hz_dn : (phiAtSeed dp (qExpand K (M * p)
      (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval
      (σ ⟨jqN (p ^ a), hmem_a⟩) = 0 := by
    have h := phiAtSeed_eval_map dp _ _
      (σ : chainField M p (a + 1) →+* LaurentSeries K) hrel_dn_E
    rwa [hσ_a1] at h

  have hpB : p ∣ M * p ^ (a + 2) := by
    refine ⟨M * p ^ (a + 1), ?_⟩
    rw [pow_succ]
    ring
  have hBdiv : M * p ^ (a + 2) / p = M * p ^ (a + 1) := by
    rw [show M * p ^ (a + 2) = M * p ^ (a + 1) * p from by rw [pow_succ]; ring]
    exact Nat.mul_div_cancel _ hp0
  have hseed_eq : qExpand K (M * p) (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq))
      = qExpand K (p * M) (qTwist ((ζ ^ (tt * M)) ^ p) (coeffEmb K jq)) := by
    have h1 : ζ ^ (tt * (M * p)) = (ζ ^ (tt * M)) ^ p := by
      rw [← pow_mul]
      congr 1
      ring
    rw [h1]
    show TS K (M * p) _ = TS K (p * M) _
    exact TS_congr (Nat.mul_comm M p) _
  have hroots_top : ∀ y : LaurentSeries K,
      (phiAtSeed dp (qExpand K (M * p)
        (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval y = 0 ↔
      (y = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ c < p, y = qExpand K M
          (qTwist (ζ ^ (tt * M) * ζ ^ (c * (M * p ^ (a + 1)))) (coeffEmb K jq))) := by
    intro y
    rw [hseed_eq, phiAtSeed]
    have h := isRoot_prime_at_slot_iff (M * p ^ (a + 2)) ζ hζ p hpB dp M (ζ ^ (tt * M)) y
    rw [hBdiv] at h
    exact h

  have hMp_ne : ¬ (((M * p : ℕ) : ℤ) ∣ ((M : ℕ) : ℤ)) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    have h1 := Nat.le_of_dvd hM0 h
    have h2 : M * 2 ≤ M * p := Nat.mul_le_mul_left M hp2
    omega
  have hz_up_spread : σ ⟨jqN (p ^ (a + 2)), hmem⟩
      = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) := by
    rcases (hroots_top _).mp hz_up with h | ⟨c, hc, h⟩
    · exact h
    · exfalso
      have hr := hrange ⟨jqN (p ^ (a + 2)), hmem⟩
      rw [h] at hr
      exact qExpand_qTwist_notMem_range_qExpand hMp_ne _ hr

  have hz_dn_form : σ ⟨jqN (p ^ a), hmem_a⟩
      = qExpand K (p * (M * p)) (qTwist (ζ ^ (ta * (p * (M * p)))) (coeffEmb K jq)) := by
    have h1 := hcompat ⟨jqN (p ^ a), mem_chainField M p (le_refl a)⟩ hmem_a
    exact h1.trans hatop'
  have hz_dn_spread : σ ⟨jqN (p ^ a), hmem_a⟩
      = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) := by
    rcases (hroots_top _).mp hz_dn with h | ⟨c, hc, h⟩
    · exact h
    · exfalso
      have h1 := hz_dn_form.symm.trans h
      have h2 := (TS_injective (K := K) (e := p * (M * p)) (e' := M)
        (u := ζ ^ (ta * (p * (M * p))))
        (u' := ζ ^ (tt * M) * ζ ^ (c * (M * p ^ (a + 1)))) h1).1
      have h3 : M * (p * p) = M := by
        rw [show M * (p * p) = p * (M * p) from by ring]
        exact h2
      exact nat_ne_of_mul hM0 (le_trans hp2 (Nat.le_mul_of_pos_right p hp0)) h3

  have hsub : (⟨jqN (p ^ (a + 2)), hmem⟩ : chainField M p (a + 1))
      = ⟨jqN (p ^ a), hmem_a⟩ :=
    RingHom.injective σ (hz_up_spread.trans hz_dn_spread.symm)
  have hval : jqN (p ^ (a + 2)) = jqN (p ^ a) := Subtype.ext_iff.mp hsub
  have hc1 : (jqN (p ^ a)).coeff (-((p ^ a : ℕ) : ℤ)) = 1 := by
    show (qExpand ℚ (p ^ a) jq).coeff _ = 1
    have h := qExpand_coeff_mul (R := ℚ) (N := p ^ a) jq (-1)
    rw [mul_neg_one] at h
    rw [h, coeff_jq_neg_one]
  have hc2 : (jqN (p ^ (a + 2))).coeff (-((p ^ a : ℕ) : ℤ)) = 0 := by
    show (qExpand ℚ (p ^ (a + 2)) jq).coeff _ = 0
    apply qExpand_coeff_of_not_dvd
    rw [dvd_neg, Int.natCast_dvd_natCast]
    intro hdvd
    have hle2 := Nat.le_of_dvd (pow_pos hp0 a) hdvd
    have h1 : p ^ a < p ^ a * (p * p) :=
      lt_mul_of_one_lt_right (pow_pos hp0 a) (by nlinarith)
    have h2 : p ^ a * (p * p) = p ^ (a + 2) := by rw [pow_add]; ring
    omega
  rw [hval, hc1] at hc2
  exact one_ne_zero hc2

private theorem jqN_pow_not_mem_adjoin_full_key (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ) (hF : jqN p ∉ modularFunctionFieldFull M) :
    jqN (p ^ (a + 2)) ∉ chainField M p (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro hmem
  obtain ⟨dp, -, hsp⟩ := exists_phiIrreducible_evalSymm p
  exact chain_endgame M p a (cycUnit (M * p ^ (a + 2))) (cycUnit_spec (M * p ^ (a + 2)))
    dp hsp hF IH hmem

/-- **The prime-power tower**: for `jqN p ∉ F_M^full`,
`j(q ^ (p ^ (a + 2))) ∉ ℚ(F_M^full, j(q ^ p), …, j(q ^ (p ^ (a + 1))))`. This is
the `Inputs.jqN_pow_not_mem_adjoin_full` field. Verbatim from
`Theorems/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`. -/
theorem jqN_pow_not_mem_adjoin_full (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hF : jqN p ∉ modularFunctionFieldFull M) :
    jqN (p ^ (a + 2)) ∉ IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull M : Set (LaurentSeries ℚ))
        ∪ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a + 1 ∧ x = jqN (p ^ i)}) :=
  jqN_pow_not_mem_adjoin_full_key M p a hF

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
      RingHom.comp_apply, iota_jq, one_pow, phiAtSeed, TS]
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
        TS_congr (Nat.mul_comm p r) 1, TS]
    rw [phiAtSeed, hseed] at hy
    rcases (isRoot_prime_at_slot_iff (p * r) ζ hζ r hrdvd data_r p 1 y).mp hy with h | ⟨c, hc, h⟩
    · rw [h, one_pow, iota_jqN]
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
