/-
  T19 — the slot product and the prime non-membership.

  The last two of the seven significant statements the capstone consumes:

  * `minpoly_jqN_map_eq_prod_slots` (the pin's `rval_aux`) — the explicit
    conjugate list: for a primitive `M`-th root `ζ`,
    `(minpoly ℚ⟮jq⟯ (jqN M)).map (coeffEmb K ∘ qExpand ℚ M ∘ ℚ⟮jq⟯ ↪ ℒ)`
    is the product of `(X - C (sv K ζ a b))` over `a ∈ M.divisors` and
    `b < M / a` with `gcd (gcd a b) (M / a) = 1`. Proved by strong induction on
    `M` from T13's `splits_prime_at_slot`, with `Hall M` as the induction input;
    its values are named `sv K ζ a b`.
  * `jqN_prime_not_mem_full` — `j(q ^ p) ∉ F_M^full` for `p ∤ M`, from `Hall M`.
    The proof reads the `ψ(M)` slot roots off node 1, writes
    `j(q ^ p) = g(j(q ^ M))` with `deg g < ψ(M)`, shows `g` constant on the slots
    (T4's `mem_range_of_eval_eq_const`), so `j(q ^ p) ∈ ℚ(j)`, contradicting
    T16's `[ℚ(j)(j(q ^ p)) : ℚ(j)] = p + 1`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` (the pin's
  `S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` is a byte-identical twin).
  The two public statements are the `Theorems/` wrappers' verbatim — explicit
  `hall` conjunction, not the port's `Hall M` abbreviation.

  ## Route

  * **The induction is the theory's, not this module's.** It lives at a general coefficient
    field in `FunctionFieldGeneration/Generic/SlotProduct.lean`
    (`slotProductInduction`, `pushedMinpoly_eq_slotPolynomial`, on the level-degree package
    `PkgAt` of `Generic/LevelPackage.lean`), with its `ℚ` instance in
    `FunctionFieldGeneration/Rat/SlotProduct.lean` (`minpoly_eq_prod_slotValues`,
    `pushedMinpoly_rat`, `pushedMinpolyAt_rat`): base field `ℚ⟮jq⟯`, level series `jqN M`,
    carrier `coeffEmb K`. What stays here is the pin's *spelling* of that content, delegated:
    `sv` is `slotValue (coeffEmb K jq)`, so the pin's `if`-form is `sv`'s own body (pinned
    by `slotValue_def`); `sv_eq_TS`, `sv_inj` and `sv_inj_slot` are the theory's
    `slotValue_eq_TS`, `slotValue_inj` and `slotValue_inj_slot` at that carrier;
    `map_qExpand_minpoly_eq` is the theory's slot-free level step
    `pushedMinpolyAt_map_qExpand` pasted onto the pin's iterated product by
    `map_slotPolynomial`; and the headline is the theory's `slotProductInduction` read back
    into that iterated product (`slotPolynomial_eq_prod`). No step of the induction is
    re-proved here.
  * **Slot count.** The pin's 108-line CRT `slotAt_mul` is replaced by the closed
    form `slotAt n d = h (n / d, d)` with
    `h (a, d) = (d / gcd a d) * φ (gcd a d)`, proved from mathlib's
    `Nat.periodic_coprime`/`Nat.count_eq_card_filter_range`, and `slots_mul` uses
    mathlib `Nat.Coprime.divisors_mul`. `gcd_eq_of_modEq`, `slotCond_mod_iff`,
    `slotAt_mul`, `gcd_mul_left/right_of_dvd` are dropped. The four `dedekindPsi_*`
    re-proofs are dropped for the public `Defs/Jq.lean` lemmas (the `ψ` promotion
    was completed by the independent bridge effort). See
    [audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md).
    The chain (`slotAt`, `slots`, `card_slotFilter_eq_dedekindPsi`) lives in
    `FunctionFieldGeneration/SlotValues.lean`, next to the `card_slotValues` that cites it.
  * **M-arbitrary non-membership** uses T18's `gen_prime`/`tight_one`/`gen_one` in
    its `hallp`, replacing the pin's `functionFieldGeneration_of_squarefree p`
    call; `mem_range_of_eval_eq_const` is imported from `FieldTheory/CommonRoot`.

  ## Structure

  * `sv` and `sv_eq_TS` are the `ℚ` spelling of the theory's slot value: `sv K ζ a b` is
    `slotValue (coeffEmb K) jq ζ a b`, and `sv_eq_TS` is its defining equation in the `TS`
    vocabulary every slot computation runs on. `TS_congr'` is the pinned generic congruence
    for `TS` (its own `ℚ`-free statement, kept as the pin has it).
  * `sv_inj` (the pin's raw-bound form) and `sv_inj_slot` (the slot-bound form a certificate's
    distinctness step holds) are the theory's slot separation at the carrier `coeffEmb K`;
    `sv_inj` delegates to the theory's raw-bound `slotValue_inj`, and this module no longer
    touches `TS_injective`.
  * `map_qExpand_minpoly_eq` is the pin's iterated-product bridge — the level-`M'` slot product
    read at the higher nome `k * M'`. The theory proves the level step slot-free
    (`pushedMinpolyAt_map_qExpand`, with the two-level object `pushedMinpolyAt`, transcribed at
    `ℚ` by `pushedMinpolyAt_rat`); the product-map step onto the iterated spelling is the
    theory's `map_slotPolynomial`, so no `Polynomial.map_prod` is re-derived here.
  * `mem_adjoin_jqN_of_mem_mff` is the adjoin collapse the non-membership needs; it never
    depended on the induction.
  spec-pin: P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean
  spec-pin: Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean
  spec-pin: Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean
-/

import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.NatDivisors
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotValues
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.ModularEquation.Split
import FLTForHuman.ModularCurve.ModularEquation.Existence
import FLTForHuman.NumberTheory.DedekindPsi
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Rat.SlotProduct

set_option autoImplicit false
-- The pin installs the `Algebra ℚ⟮jq⟯ (LaurentSeries K)` instance (via `letI`) and
-- uses `haveI` for various `NeZero`/`Fact` instances; they are consumed by
-- typeclass search, so the style linter's `have` preference does not apply. Same
-- local disable as `Nonmembership.lean`/`Generation.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

-- The `algebraAdjoinAdjoin` scoped instances (friction entry 19) are what make the
-- `Module.Free`/`IsFractionRing` search on the adjoin towers cheap; the pin's
-- `p2m_open` activated them, a textual translation must say so.
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve

/-! ## The slot values `sv` -/

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The slot value `sv K ζ a b = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))`,
with `sv K ζ 0 b = 0` so the `if`-form matches the pin's wrapper. -/
def sv (K : Type*) [Field K] [Algebra ℚ K] (ζ : Kˣ) (a b : ℕ) : LaurentSeries K :=
  slotValue (coeffEmb K jq) ζ a b

theorem sv_eq_TS (ζ : Kˣ) (a b : ℕ) [NeZero a] :
    sv K ζ a b = TS K (a * a) (ζ ^ (b * a)) := by
  exact slotValue_eq_TS (coeffEmb K jq) ζ a b (coeffEmb_jq K)

omit [Algebra ℚ K] in
theorem TS_congr' {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (he : e = e')
    (hu : u = u') : TS K e u = TS K e' u' := by
  subst he
  rw [hu]

/-- **The slots `sv K ζ a b` are distinct** for `a ≠ 0`, `b * a < M`. Delegated: the theory's
`slotValue_inj` is stated on exactly these raw bounds, so the pin's raw-bound form is one
application. -/
theorem sv_inj {M : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) M)
    {a b a' b' : ℕ} (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb : b * a < M) (hb' : b' * a' < M)
    (h : sv K ζ a b = sv K ζ a' b') : a = a' ∧ b = b' :=
  slotValue_inj (coeffEmb K jq) (coeffEmb_jq K) hζ ha0 ha0' hb hb' h

/-- A member of the two-generator field `ℚ(jq, jqN M)` lies in `ℚ⟮jq⟯⟮jqN M⟯`: the
scalars-extended adjoin collapses to the simple extension by `jqN M`. -/
theorem mem_adjoin_jqN_of_mem_mff {M : ℕ} [NeZero M] {x : LaurentSeries ℚ}
    (hx : x ∈ modularFunctionField M) :
    x ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
  have hle : ℚ⟮jq⟯ ≤
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ)) :=
    IntermediateField.adjoin.mono ℚ _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hE := IntermediateField.extendScalars_adjoin hle
  have hcollapse : IntermediateField.adjoin ℚ⟮jq⟯
      ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ))
      = IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro z (rfl | rfl)
      · exact (IntermediateField.adjoin ℚ⟮jq⟯ _).algebraMap_mem jGen
      · exact IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl
    · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  rw [modularFunctionField] at hx
  have h2 : x ∈ IntermediateField.extendScalars hle :=
    (IntermediateField.mem_extendScalars _).mpr hx
  rw [hE, hcollapse] at h2
  exact h2

/-- Push the `k`-fold `qExpand` through the mapped minimal polynomial: it acts
coefficientwise on the conjugate product. -/
theorem map_qExpand_minpoly_eq {M' : ℕ} [NeZero M'] (k : ℕ) [NeZero k] {N : ℕ}
    [NeZero N] (hN : N = k * M') (ζ' : Kˣ)
    (hid : (minpoly ℚ⟮jq⟯ (jqN M')).map
        (((coeffEmb K).comp (qExpand ℚ M')).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ∏ a ∈ M'.divisors, ∏ b ∈ (Finset.range (M' / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M' / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ' a b))) :
    (minpoly ℚ⟮jq⟯ (jqN M')).map
        (((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ∏ a ∈ M'.divisors, ∏ b ∈ (Finset.range (M' / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M' / a) = 1),
          (Polynomial.X - Polynomial.C (qExpand K k (sv K ζ' a b))) := by
  subst hN
  have h1 : (minpoly ℚ⟮jq⟯ (jqN M')).map
      (((coeffEmb K).comp (qExpand ℚ (k * M'))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = (pushedMinpoly (κ' := K) jq M').map (qExpand K k) := by
    rw [← pushedMinpolyAt_rat M' (k * M')]
    rw [pushedMinpolyAt_map_qExpand (κ' := K) jq (m := M') (k := k), pushedMinpolyAt_self]
  rw [h1, pushedMinpoly_rat M', hid]
  show (∏ a ∈ M'.divisors, ∏ b ∈ (Finset.range (M' / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M' / a) = 1),
      (Polynomial.X - Polynomial.C (slotValue (coeffEmb K jq) ζ' a b))).map (qExpand K k)
    = ∏ a ∈ M'.divisors, ∏ b ∈ (Finset.range (M' / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M' / a) = 1),
      (Polynomial.X - Polynomial.C (qExpand K k (sv K ζ' a b)))
  rw [← slotPolynomial_eq_prod (coeffEmb K jq) M' ζ']
  exact map_slotPolynomial (coeffEmb K jq) M' ζ' (qExpand K k)

/-! ## The slot multiset

The slot product of the headline is a product over the multiset of slot values
`∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd … = 1), (X - C (F a b))`. Making
that multiset explicit lets the counting (`card_slotValues`), the distinctness
(`nodup_slotValues`) and "the product is the factored multiset" (`prod_slotValues`)
be stated once; the headlines then run on those three lemmas. The multiset API is
`FunctionFieldGeneration/SlotValues.lean`. -/

/-- **Slot values separate their parameters**: for `a, a' ∣ M`, `b < M / a`,
`b' < M / a'` and `ζ` a primitive `M`-th root, equal slot values force `(a, b) = (a', b')`.
This is `sv_inj` with the hypotheses `b * a < M`, `b' * a' < M` supplied by the slot
bounds. -/
theorem sv_inj_slot {M : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hM0 : M ≠ 0) {a b a' b' : ℕ} (haM : a ∣ M) (haM' : a' ∣ M)
    (hb : b < M / a) (hb' : b' < M / a') (h : sv K ζ a b = sv K ζ a' b') :
    a = a' ∧ b = b' := by
  exact slotValue_inj_slot (coeffEmb K jq) (coeffEmb_jq K) hζ hM0 haM haM' hb hb' h

/-- **The slot product**: the mapped minimal polynomial of `jqN M` is the product
of `(X - C (sv K ζ a b))` over the slots. Verbatim from
`Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` (explicit `hall`
conjunction, explicit `if` form). -/
theorem minpoly_jqN_map_eq_prod_slots {K : Type*} [Field K] [Algebra ℚ K]
    (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) :
    (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ M)).comp
          (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (LaurentSeries ℚ)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))) :=
  (pushedMinpoly_rat M).symm.trans <|
    (minpoly_eq_prod_slotValues M ζ hζ hall).trans <|
      prod_slotValues M (fun a b => sv K ζ a b)

end ModularCurve

end
