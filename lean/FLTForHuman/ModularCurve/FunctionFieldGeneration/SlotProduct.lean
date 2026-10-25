/-
  T19 — the slot product and the prime non-membership.

  The last two `Inputs` fields, so with them the conditional capstone's debt is
  **2 → 0**:

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

  * **Slot count.** The pin's 108-line CRT `slotAt_mul` is replaced by the closed
    form `slotAt n d = h (n / d, d)` with
    `h (a, d) = (d / gcd a d) * φ (gcd a d)`, proved from mathlib's
    `Nat.periodic_coprime`/`Nat.count_eq_card_filter_range`, and `slots_mul` uses
    mathlib `Nat.Coprime.divisors_mul`. `gcd_eq_of_modEq`, `slotCond_mod_iff`,
    `slotAt_mul`, `gcd_mul_left/right_of_dvd` are dropped. The four `dedekindPsi_*`
    re-proofs are dropped for the public `Defs/Jq.lean` lemmas (the `ψ` promotion
    was completed by the independent bridge effort). See
    [audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md).
  * **`rval_aux`** transcribes the pin's 680 lines (the 493-line `hslot_root` is
    ~64% irreducible mathematics; the audit found no shorter route).
  * **M-arbitrary non-membership** uses T18's `gen_prime`/`tight_one`/`gen_one` in
    its `hallp`, replacing the pin's `functionFieldGeneration_of_squarefree p`
    call; `mem_range_of_eval_eq_const` is imported from `FieldTheory/CommonRoot`.

  ## Structure

  Both long proofs are chains of `private` lemmas named after the sub-goal each
  closes; the headlines are then short assemblies. This mirrors the `C` twin
  `SlotProductAnyField.lean`, whose split has the same seams.

  * **The slot multiset** (`slotValues`) makes the product's index set explicit. Its generic
    half — `slotValues`, `mem_slotValues`, `card_slotValues`, `prod_slotValues`,
    `nodup_slotValues` — is **homed once**, in `FunctionFieldGeneration/SlotValues.lean`, which
    the `C` twin imports as well; this module supplies the count at the call site
    (`card_slotFilter_eq_dedekindPsi`, its own public export) and the `sv`-specific
    instantiation (`sv_inj_slot`, `nodup_slotValues_sv`, `nodup_slotValues_qExpand`).
  * **`rval_aux`** (strong induction on `M`) keeps only the induction. Its statement is
    the `def` `SlotProductAt`; `minpoly_map_eq_prod_slots_one` is the base case;
    `isRoot_map_minpoly_sv` collects the slot roots — `isRoot_map_minpoly_sv_top` at
    `a = M`, and `isRoot_map_minpoly_sv_of_descent` otherwise. The descent rests on
    `exists_slot_descent_data`, `isRoot_qExpand_sv_of_slot_product`,
    `finrank_adjoin_mul_dedekindPsi` (the `finrank_mul_finrank` tower, one type check),
    `phiAtSeed_slot_factor`, `qExpand_qTwist_slot_eq_sv`, and the two prime cases
    `isRoot_map_minpoly_sv_of_dvd` / `…_of_not_dvd` (which use `sv_ne_image_of_dvd`,
    `not_isRoot_minpoly_of_prime_deg` and `isRoot_map_minpoly_of_isRoot_subfield`).
    The shared counting (`card_slotValues`, instantiated at `sv`), distinctness
    (`nodup_slotValues_sv`) and degree (`natDegree_minpoly_jqN`) then squeeze the slot list onto
    the roots.
  * **`jqN_prime_not_mem_adjoin`** keeps only the final contradiction: the constancy of
    `g'` on the slots is `eval_map_eq_of_mem_slotValues`, and the `hall` input at the
    prime is `hall_prime`.

  The `ℚ`-layer differences from the `C` twin stay visible rather than being forced
  into its shape: the coefficient map is `(coeffEmb K).comp (qExpand ℚ M)`, the
  function field is the port's opaque `modularFunctionField`/`modularFunctionFieldFull`
  pair, and `isRoot_map_minpoly_sv_of_descent` / `eval_map_eq_of_mem_slotValues`
  install the pin's `letI : Algebra ℚ⟮jq⟯ (LaurentSeries K)` (its `p2m_open` instance)
  together with the equation `halg : algebraMap … = (coeffEmb K).comp (qExpand ℚ M) ∘ …`.
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
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.NumberTheory.DedekindPsi

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

/-! ## The slot count

`slotAt n d` counts the `b < d` with `gcd (gcd (n/d) b) d = 1`; `slots n` sums it
over the divisors of `n`. The endpoint is `slots n = ψ(n)`, by
`Nat.recOnPosPrimePosCoprime`. -/

private def slotAt (n d : ℕ) : ℕ :=
  ((Finset.range d).filter fun b => Nat.gcd (Nat.gcd (n / d) b) d = 1).card

private def slots (n : ℕ) : ℕ := ∑ d ∈ n.divisors, slotAt n d

/-- The slot predicate is symmetric in `b` and `d`. -/
private theorem slotCond_eq (x d b : ℕ) :
    Nat.gcd (Nat.gcd x b) d = Nat.gcd (Nat.gcd x d) b := by
  rw [Nat.gcd_assoc, Nat.gcd_comm b d, ← Nat.gcd_assoc]

private theorem slotCond_iff (x d b : ℕ) :
    Nat.gcd (Nat.gcd x b) d = 1 ↔ Nat.Coprime (Nat.gcd x d) b := by
  rw [slotCond_eq]

/-- **The closed form**: `slotAt n d = (d / gcd (n/d) d) * φ (gcd (n/d) d)`. -/
private theorem slotAt_eq (n d : ℕ) : slotAt n d = dedekindPsiFibre (n / d, d) := by
  unfold slotAt
  rw [Finset.filter_congr (fun b _ => slotCond_iff (n / d) d b)]
  exact card_fibre (n / d) d

/-- Multiplicativity of `dedekindPsiFibre` under coprime `(a d)`-products. -/
private theorem dedekindPsiFibre_mul (a₁ d₁ a₂ d₂ : ℕ) (hcop : Nat.Coprime (a₁ * d₁) (a₂ * d₂)) :
    dedekindPsiFibre (a₁ * a₂, d₁ * d₂) = dedekindPsiFibre (a₁, d₁) * dedekindPsiFibre (a₂, d₂) := by
  have ha₁a₂ : Nat.Coprime a₁ a₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop).coprime_dvd_right (Dvd.intro _ rfl)
  have ha₁d₂ : Nat.Coprime a₁ d₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop).coprime_dvd_right (Dvd.intro_left _ rfl)
  have hd₁a₂ : Nat.Coprime d₁ a₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hcop).coprime_dvd_right (Dvd.intro _ rfl)
  have hd₁d₂ : Nat.Coprime d₁ d₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hcop).coprime_dvd_right
      (Dvd.intro_left _ rfl)

  have hg : Nat.gcd (a₁ * a₂) (d₁ * d₂) = Nat.gcd a₁ d₁ * Nat.gcd a₂ d₂ := by
    rw [Nat.Coprime.gcd_mul _ hd₁d₂]
    rw [Nat.gcd_comm (a₁ * a₂) d₁, Nat.gcd_comm (a₁ * a₂) d₂,
      Nat.Coprime.gcd_mul _ ha₁a₂, Nat.Coprime.gcd_mul _ ha₁a₂,
      Nat.Coprime.gcd_eq_one hd₁a₂, (Nat.Coprime.gcd_eq_one ha₁d₂.symm), mul_one, one_mul,
      Nat.gcd_comm d₁ a₁, Nat.gcd_comm d₂ a₂]
  have hg₁ : Nat.gcd a₁ d₁ ∣ d₁ := Nat.gcd_dvd_right _ _
  have hg₂ : Nat.gcd a₂ d₂ ∣ d₂ := Nat.gcd_dvd_right _ _
  have hcopg : Nat.Coprime (Nat.gcd a₁ d₁) (Nat.gcd a₂ d₂) :=
    (hd₁d₂.coprime_dvd_left hg₁).coprime_dvd_right hg₂
  simp only [dedekindPsiFibre]
  rw [hg, Nat.totient_mul hcopg, ← Nat.div_mul_div_comm hg₁ hg₂]
  ring

private theorem slotAt_one (n : ℕ) : slotAt n 1 = 1 := by
  unfold slotAt
  simp [Nat.gcd_one_right]

private theorem slotAt_self (n : ℕ) (hn : 0 < n) : slotAt n n = n := by
  unfold slotAt
  simp [Nat.div_self hn, Nat.gcd_one_left]

private theorem slotAt_prime_pow_mid {p : ℕ} (hp : p.Prime) {i k : ℕ} (hi0 : 0 < i)
    (hik : i < k) : slotAt (p ^ k) (p ^ i) = Nat.totient (p ^ i) := by
  unfold slotAt
  rw [Nat.totient_eq_card_coprime]
  congr 1
  refine Finset.filter_congr fun b _ => ?_
  rw [slotCond_iff]
  constructor
  · intro h
    have hpg : p ∣ Nat.gcd (p ^ k / p ^ i) (p ^ i) := by
      refine Nat.dvd_gcd ?_ (dvd_pow_self p hi0.ne')
      rw [Nat.pow_div hik.le hp.pos]
      exact dvd_pow_self p (by omega)
    exact Nat.Coprime.pow_left i (Nat.Coprime.coprime_dvd_left hpg h)
  · intro h
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) h

private theorem slots_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    slots (p ^ (k + 1)) = p ^ (k + 1) + p ^ k := by
  unfold slots
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
  have hrest : ∀ x ∈ Finset.range (k + 1),
      slotAt (p ^ (k + 1)) (p ^ x) = Nat.totient (p ^ x) := by
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · rw [pow_zero, slotAt_one, Nat.totient_one]
    · exact slotAt_prime_pow_mid hp hx0 (Finset.mem_range.mp hx)
  rw [Finset.sum_congr rfl hrest, slotAt_self _ (pow_pos hp.pos _),
    ← Nat.sum_divisors_prime_pow (f := Nat.totient) hp, Nat.sum_totient, Nat.add_comm]

private theorem slots_mul (M M' : ℕ) (hco : Nat.Coprime M M') :
    slots (M * M') = slots M * slots M' := by
  unfold slots
  rw [Finset.sum_mul_sum]
  rw [Nat.Coprime.divisors_mul hco, Finset.sum_map]
  change (∑ x ∈ (M.divisors ×ˢ M'.divisors).attach,
      slotAt (M * M') ((x : ℕ × ℕ).1 * (x : ℕ × ℕ).2))
    = ∑ i ∈ M.divisors, ∑ j ∈ M'.divisors, slotAt M i * slotAt M' j
  rw [Finset.sum_attach (f := fun y : ℕ × ℕ => slotAt (M * M') (y.1 * y.2))]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
  rw [slotAt_eq, slotAt_eq, slotAt_eq, ← Nat.div_mul_div_comm (Nat.mem_divisors.mp hd₁).1
    (Nat.mem_divisors.mp hd₂).1]
  exact dedekindPsiFibre_mul (M / d₁) d₁ (M' / d₂) d₂
    (by rw [Nat.div_mul_cancel (Nat.mem_divisors.mp hd₁).1,
            Nat.div_mul_cancel (Nat.mem_divisors.mp hd₂).1]; exact hco)

private theorem slots_eq_dedekindPsi : ∀ n : ℕ, n ≠ 0 → slots n = dedekindPsi n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [slots_prime_pow hp j, dedekindPsi_prime_pow p (j + 1) hp (Nat.succ_ne_zero j)]
    simp
  | zero => exact fun h0 => absurd rfl h0
  | one =>
    intro _
    rw [dedekindPsi_one]
    unfold slots
    rw [Nat.divisors_one, Finset.sum_singleton]
    exact slotAt_one 1
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [slots_mul a b hab, iha (by omega), ihb (by omega),
      dedekindPsi_mul_of_coprime a b hab]

/-- The one public counting export (the audit's `card_slotFilter_eq_dedekindPsi`,
`audit-slot-counting-mathlib.md` §5): the divisor sum of the slot-filter counts is
`ψ(M)`. `slotAt`/`slots` stay `private`; this is the statement a consumer of the
slot list can cite directly. -/
theorem card_slotFilter_eq_dedekindPsi (M : ℕ) (hM : M ≠ 0) :
    (∑ a ∈ M.divisors,
      ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card) = dedekindPsi M := by
  have h1 : ∀ a ∈ M.divisors,
      ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card = slotAt M (M / a) := by
    intro a ha
    rw [slotAt_eq, Nat.div_div_self (Nat.mem_divisors.mp ha).1 hM,
      Finset.filter_congr (fun b _ => slotCond_iff a (M / a) b)]
    exact card_fibre a (M / a)
  rw [Finset.sum_congr rfl h1, Nat.sum_div_divisors]
  exact slots_eq_dedekindPsi M hM

/-! ## The slot values `sv` -/

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The slot value `sv K ζ a b = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))`,
with `sv K ζ 0 b = 0` so the `if`-form matches the pin's wrapper. -/
private def sv (K : Type*) [Field K] [Algebra ℚ K] (ζ : Kˣ) (a b : ℕ) : LaurentSeries K :=
  if h : a = 0 then 0 else
    letI : NeZero a := ⟨h⟩
    qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))

private theorem sv_eq (ζ : Kˣ) (a b : ℕ) [NeZero a] :
    sv K ζ a b = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) := by
  unfold sv
  rw [dite_eq_right (NeZero.ne a)]

private theorem sv_eq_TS (ζ : Kˣ) (a b : ℕ) [NeZero a] :
    sv K ζ a b = TS K (a * a) (ζ ^ (b * a)) := by
  rw [sv_eq, coeffEmb_jq]
  rfl

omit [Algebra ℚ K] in
private theorem TS_congr' {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (he : e = e')
    (hu : u = u') : TS K e u = TS K e' u' := by
  subst he
  rw [hu]

/-- The slots `sv K ζ a b` are distinct for `a ≠ 0`, `b * a < M`: the exponent and
the twist separate them by `TS_injective` and `IsPrimitiveRoot.pow_inj`. -/
private theorem sv_inj {M : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) M)
    {a b a' b' : ℕ} (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb : b * a < M) (hb' : b' * a' < M)
    (h : sv K ζ a b = sv K ζ a' b') : a = a' ∧ b = b' := by
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero a' := ⟨ha0'⟩
  rw [sv_eq_TS, sv_eq_TS] at h
  obtain ⟨he, hu⟩ := TS_injective h
  have haa : a = a' := (mul_self_inj (Nat.zero_le a) (Nat.zero_le a')).mp he
  subst haa
  refine ⟨rfl, ?_⟩
  have hv : ((ζ : K)) ^ (b * a) = ((ζ : K)) ^ (b' * a) := by
    have h1 := congrArg Units.val hu
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  have h2 : b * a = b' * a := hζ.pow_inj hb hb' hv
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha0) h2

private theorem sv_top (M : ℕ) [NeZero M] (ζ : Kˣ) :
    sv K ζ M 0 = coeffEmb K (qExpand ℚ M (jqN M)) := by
  rw [sv_eq_TS, iota_jqN M M]
  exact TS_congr' rfl (by rw [zero_mul, pow_zero])

/-- A member of the two-generator field `ℚ(jq, jqN M)` lies in `ℚ⟮jq⟯⟮jqN M⟯`: the
scalars-extended adjoin collapses to the simple extension by `jqN M`. -/
private theorem mem_adjoin_jqN_of_mem_mff {M : ℕ} [NeZero M] {x : LaurentSeries ℚ}
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
private theorem map_qExpand_minpoly_eq {M' : ℕ} [NeZero M'] (k : ℕ) [NeZero k] {N : ℕ}
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
  have hcomp : (qExpand K k).comp (((coeffEmb K).comp (qExpand ℚ M')).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ((coeffEmb K).comp (qExpand ℚ (k * M'))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    refine RingHom.ext fun z => ?_
    simp only [RingHom.comp_apply]
    rw [coeffEmb_qExpand, qExpand_qExpand, ← coeffEmb_qExpand]
  have h1 : (minpoly ℚ⟮jq⟯ (jqN M')).map
      (((coeffEmb K).comp (qExpand ℚ (k * M'))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ((minpoly ℚ⟮jq⟯ (jqN M')).map
          (((coeffEmb K).comp (qExpand ℚ M')).comp
            (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).map (qExpand K k) := by
    rw [Polynomial.map_map, hcomp]
  rw [h1, hid, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-! ## The base field and the slot multiset

The slot product of the headline is a product over the multiset of slot values
`∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd … = 1), (X - C (F a b))`. Making
that multiset explicit lets the counting (`card_slotValues`), the distinctness
(`nodup_slotValues`) and "the product is the factored multiset" (`prod_slotValues`)
be stated once; both headlines then run on the same three lemmas. This is the
`ℚ`-layer twin of the same block in `SlotProductAnyField.lean`. -/

/-- **Slot values separate their parameters**: for `a, a' ∣ M`, `b < M / a`,
`b' < M / a'` and `ζ` a primitive `M`-th root, equal slot values force `(a, b) = (a', b')`.
This is `sv_inj` with the hypotheses `b * a < M`, `b' * a' < M` supplied by the slot
bounds. -/
private theorem sv_inj_slot {M : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hM0 : M ≠ 0) {a b a' b' : ℕ} (haM : a ∣ M) (haM' : a' ∣ M)
    (hb : b < M / a) (hb' : b' < M / a') (h : sv K ζ a b = sv K ζ a' b') :
    a = a' ∧ b = b' := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hM0 (Nat.eq_zero_of_zero_dvd haM)
  have ha0' : a' ≠ 0 := by
    rintro rfl
    exact hM0 (Nat.eq_zero_of_zero_dvd haM')
  have hba : b * a < M := by
    calc b * a < M / a * a :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hb
      _ = M := Nat.div_mul_cancel haM
  have hba' : b' * a' < M := by
    calc b' * a' < M / a' * a' :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0')).mpr hb'
      _ = M := Nat.div_mul_cancel haM'
  exact sv_inj hζ ha0 ha0' hba hba' h

/-- **The slots of `ζ` are distinct**: the slot values `sv K ζ a b` form a multiset
without repetitions. -/
private theorem nodup_slotValues_sv {M : ℕ} {ζ : Kˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) :
    (slotValues M (fun a b => sv K ζ a b)).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact sv_inj_slot hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1) h

/-- **The expanded slots are distinct**: applying `qExpand K p` to the `ζ ^ p`-slots
keeps them distinct, `qExpand K p` being injective. -/
private theorem nodup_slotValues_qExpand {M p : ℕ} [NeZero p] {ζ : Kˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M) :
    (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact sv_inj_slot hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1)
    (RingHom.injective (qExpand K p) h)

/-! ## The slot product `rval_aux` and its named steps

`rval_aux` is a strong induction on `M`. Its content is split as follows.

* `SlotProductAt M K ζ` is the induction statement itself, packaged so that it can be
  passed around as the induction hypothesis.
* `isRoot_map_minpoly_sv`: every slot value `sv K ζ a b` is a root of the mapped minimal
  polynomial. For `a = M` this is `isRoot_map_minpoly_sv_top`; otherwise the slot descends
  along the least prime `p` of `M / a` to the level `a * d''`, which is
  `isRoot_map_minpoly_sv_of_descent`. That step uses the induction hypothesis at
  `a * d''` (`isRoot_qExpand_sv_of_slot_product`), the degree of the step
  (`finrank_adjoin_mul_dedekindPsi`), the factorisation of `Φ_p` at the descended slot
  (`phiAtSeed_slot_factor`), and then splits on whether `p ∣ a * d''`:
  `isRoot_map_minpoly_sv_of_dvd` (the seed polynomial is divided by the linear factor at the
  descended conjugate) and `isRoot_map_minpoly_sv_of_not_dvd` (degrees agree, so the minimal
  polynomial is the seed polynomial).
* `minpoly_map_eq_prod_slots_one` is the base case `M = 1`.
* The counting `card_slotValues`, the distinctness `nodup_slotValues_sv` and the degree
  `natDegree_minpoly_jqN` then show that the `ψ(M)` slot values exhaust the roots.

The `ℚ`-layer differences from the `C` twin (`SlotProductAnyField.lean`) are the
coefficient map `(coeffEmb K).comp (qExpand ℚ M)` and the `letI : Algebra ℚ⟮jq⟯
(LaurentSeries K)` installed in `isRoot_map_minpoly_sv_of_descent` (the pin's
`p2m_open` instance, needed to read the conjugates `ψ` as `ℚ⟮jq⟯`-algebra maps). -/

section RValCore

/-- **The slot-product statement at `M`**: the conclusion of `rval_aux`, as a named
predicate, so the strong-induction hypothesis can be passed to the lemmas below. It is a
`def`, not an `abbrev`: as an `abbrev` it would re-unfold at every use. -/
private def SlotProductAt (M : ℕ) [NeZero M] (K : Type*) [Field K] [Algebra ℚ K] (ζ : Kˣ) : Prop :=
  IsPrimitiveRoot ((ζ : Kˣ) : K) M →
    (∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) →
    (minpoly ℚ⟮jq⟯ (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b))

/-- **The base case `M = 1`**: `jqN 1 = jq` already lies in the base field `ℚ⟮jq⟯`, so its
minimal polynomial is `X - C jq`; the slot product has the single slot
`sv K ζ 1 0 = coeffEmb K jq`. -/
private theorem minpoly_map_eq_prod_slots_one (ζ : Kˣ) :
    (minpoly ℚ⟮jq⟯ (jqN 1)).map
        (((coeffEmb K).comp (qExpand ℚ 1)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ∏ a ∈ (1 : ℕ).divisors, ∏ b ∈ (Finset.range (1 / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (1 / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b)) := by
  have hjq1 : jqN 1 = algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ) jGen := by
    rw [show jqN 1 = jq from by rw [jqN, qExpand_one_apply]]
    rfl
  have hmin : minpoly ℚ⟮jq⟯ (jqN 1) = Polynomial.X - Polynomial.C jGen := by
    rw [hjq1]
    exact minpoly.eq_X_sub_C (B := LaurentSeries ℚ) jGen
  have hfil : (Finset.range (1 / 1)).filter
      (fun b => Nat.gcd (Nat.gcd 1 b) (1 / 1) = 1) = {0} := by decide
  rw [hmin, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Nat.divisors_one,
    Finset.prod_singleton, hfil, Finset.prod_singleton]
  congr 1
  have h1 : (((coeffEmb K).comp (qExpand ℚ 1)).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) jGen = coeffEmb K jq := by
    simp only [RingHom.comp_apply]
    rw [show (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) jGen = jq from rfl, qExpand_one_apply]
  rw [h1]
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have h2 : sv K ζ 1 0 = coeffEmb K jq := by
    rw [sv_eq_TS]
    have h3 : TS K (1 * 1) (ζ ^ (0 * 1)) = TS K 1 1 :=
      TS_congr' (Nat.mul_one 1) (by rw [Nat.zero_mul, pow_zero])
    rw [h3, TS, qTwist_one_apply, qExpand_one_apply, coeffEmb_jq]
  rw [h2]

/-- **The slot at the top divisor**: for `a = M` (i.e. `M / a = 1`) the only slot is
`b = 0`, and `sv K ζ M 0 = coeffEmb K (qExpand ℚ M (jqN M))` is a root of the mapped
minimal polynomial by definition of `minpoly`. -/
private theorem isRoot_map_minpoly_sv_top {M a b : ℕ} [NeZero M] (ζ : Kˣ) (haM : a ∣ M)
    (hd1 : M / a = 1)
    (hb : b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)) :
    ((minpoly ℚ⟮jq⟯ (jqN M)).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (sv K ζ a b) := by
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  have hbr : b < M / a := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have haM' : a = M := by rw [hd1, mul_one] at had; exact had
  have hb0 : b = 0 := by omega
  subst hb0
  rw [show sv K ζ a 0 = sv K ζ M 0 from by rw [haM'], sv_top,
    show coeffEmb K (qExpand ℚ M (jqN M))
      = ((coeffEmb K).comp (qExpand ℚ M)) (jqN M) from rfl]
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂]
  have h0 : Polynomial.eval₂ (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) (jqN M)
      (minpoly ℚ⟮jq⟯ (jqN M)) = 0 := by
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  rw [h0, map_zero]

/-- **Integrality of `jqN M` over the base field**: `hall` gives the adjoin of `jqN M` the
positive finite dimension `ψ(M)`, so `jqN M` is integral over `ℚ⟮jq⟯`. -/
private theorem isIntegral_adjoin_jqN {M : ℕ} [NeZero M]
    (htM : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) = dedekindPsi M) :
    IsIntegral ℚ⟮jq⟯ (jqN M) := by
  haveI : FiniteDimensional ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ (NeZero.ne M))
  exact IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite ℚ⟮jq⟯
    (⟨jqN M, IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl⟩ :
      IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))))

/-- **The degree of the minimal polynomial**: `minpoly ℚ⟮jq⟯ (jqN M)` has degree `ψ(M)`,
the dimension of the adjoin. -/
private theorem natDegree_minpoly_jqN {M : ℕ} [NeZero M]
    (htM : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) = dedekindPsi M) :
    (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M := by
  haveI : FiniteDimensional ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ (NeZero.ne M))
  rw [← IntermediateField.adjoin.finrank (isIntegral_adjoin_jqN htM)]
  exact htM

/-- **The degree step at a divisor**: adjoining `jqN M` to `ℚ⟮jq⟯⟮jqN d⟯` multiplies the
degree by `ψ(d)`, i.e. `[top : ℚ⟮jq⟯⟮jqN d⟯] * ψ(d) = ψ(M)`. The adjoin
`ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯` collapses to `ℚ⟮jq⟯⟮jqN M⟯` because `jqN d` already lies in the
modular function field of `M` (`modularFunctionField M`, which `hgM` identifies with
`modularFunctionFieldFull M`). -/
private theorem finrank_adjoin_mul_dedekindPsi {M d : ℕ} [NeZero M] [NeZero d] (hd : d ∣ M)
    (htM : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) = dedekindPsi M)
    (hgM : modularFunctionField M = modularFunctionFieldFull M)
    (htd : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d) :
    Module.finrank ℚ⟮jq⟯⟮jqN d⟯ (ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯) * dedekindPsi d = dedekindPsi M := by
  haveI : Module.Free ℚ⟮jq⟯⟮jqN d⟯ ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯ :=
    Module.Free.of_divisionRing _ _
  have htow := Module.finrank_mul_finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯ ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯
  have habs : IntermediateField.adjoin ℚ⟮jq⟯
      (({jqN d} : Set (LaurentSeries ℚ)) ∪ {jqN M})
      = IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 : jqN d ∈ modularFunctionFieldFull M := jqd_mem_full M hd
      rw [← hgM] at h1
      exact mem_adjoin_jqN_of_mem_mff h1
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact IntermediateField.subset_adjoin _ _ rfl
  have htop : Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯ = dedekindPsi M := by
    have h1 := IntermediateField.adjoin_adjoin_left ℚ⟮jq⟯
      ({jqN d} : Set (LaurentSeries ℚ)) {jqN M}
    have h2 : Module.finrank ℚ⟮jq⟯
        (IntermediateField.restrictScalars ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯)
        = Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯⟮jqN M⟯ := rfl
    rw [← h2, h1, habs]
    exact htM
  rw [← htd, ← htop, Nat.mul_comm]
  exact htow

/-- **The descended slot root, pushed up**: if the slot product holds at the level
`d = a * d''` for the primitive root `ζ ^ p` (the strong-induction hypothesis) and
`M = p * (a * d'')`, then the expanded slot value `qExpand K p (sv K (ζ ^ p) a (b % d''))`
is a root of the `qExpand ℚ M`-push of `minpoly ℚ⟮jq⟯ (jqN (a * d''))`: it is one of the
slots of the slot product at `a * d''`, read after `qExpand K p`. -/
private theorem isRoot_qExpand_sv_of_slot_product {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] {ζ : Kˣ} (hM : M = p * (a * d''))
    (hprod : (minpoly ℚ⟮jq⟯ (jqN (a * d''))).map
        (((coeffEmb K).comp (qExpand ℚ (a * d''))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ∏ a' ∈ (a * d'').divisors, ∏ b' ∈ (Finset.range (a * d'' / a')).filter
          (fun b' => Nat.gcd (Nat.gcd a' b') (a * d'' / a') = 1),
          (Polynomial.X - Polynomial.C (sv K (ζ ^ p) a' b')))
    (hb''lt : b % d'' < d'') (hprim' : Nat.gcd (Nat.gcd a (b % d'')) d'' = 1) :
    ((minpoly ℚ⟮jq⟯ (jqN (a * d''))).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (qExpand K p (sv K (ζ ^ p) a (b % d''))) := by
  have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne d'')
  rw [map_qExpand_minpoly_eq p hM (ζ ^ p) hprod, Polynomial.IsRoot, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := a) (Nat.mem_divisors.mpr ⟨⟨d'', rfl⟩, hM'0⟩) ?_
  rw [Polynomial.eval_prod]
  have hM'a : a * d'' / a = d'' := Nat.mul_div_cancel_left d'' (Nat.pos_of_ne_zero (NeZero.ne a))
  refine Finset.prod_eq_zero (i := b % d'') ?_ ?_
  · rw [hM'a]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb''lt, hprim'⟩
  · rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- **The `Φ_p`-factorisation at a slot**: the seed polynomial `Φ_p` evaluated at the slot
`qExpand K p (sv K (ζ ^ p) a b)` splits as the extra conjugate at level `p * p` times the
`p` finite conjugates `qExpand K (a * a) (qTwist (ζ ^ (b * a) * ζ ^ (c * (M / p))) …)`.
This is `PhiGen.splits_prime_at_slot` after rewriting the slot value through `TS`. -/
private theorem phiAtSeed_slot_factor {M a b p : ℕ} [NeZero M] [NeZero a] [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) (hpp : p.Prime) (hpM : p ∣ M)
    (dp : ModularPolynomialData p) :
    phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a b))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * (a * a)))
          (qTwist ((ζ ^ (b * a)) ^ (p * p)) (coeffEmb K jq))))
        * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K (a * a)
          (qTwist (ζ ^ (b * a) * ζ ^ (c * (M / p))) (coeffEmb K jq)))) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hseed : qExpand K p (sv K (ζ ^ p) a b)
      = qExpand K (p * (a * a)) (qTwist ((ζ ^ (b * a)) ^ p) (coeffEmb K jq)) := by
    rw [sv_eq_TS, qExpand_TS, coeffEmb_jq]
    show TS K (p * (a * a)) ((ζ ^ p) ^ (b * a))
      = TS K (p * (a * a)) ((ζ ^ (b * a)) ^ p)
    exact TS_congr' rfl (by rw [← pow_mul, ← pow_mul, Nat.mul_comm])
  have hC5 := PhiGen.splits_prime_at_slot M ζ hζ p hpM dp (a * a) (ζ ^ (b * a))
  rw [hseed]
  exact hC5

/-- **The target slot**: for `M = a * d'' * p` and `b < M / a`, the `(b / d'')`-th finite
conjugate at the descended slot is the slot value `sv K ζ a b` — the two exponents agree
because `b = b % d'' + (b / d'') * d''`. -/
private theorem qExpand_qTwist_slot_eq_sv {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero p] {ζ : Kˣ} (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b) :
    qExpand K (a * a) (qTwist (ζ ^ (b % d'' * a) * ζ ^ (b / d'' * (M / p)))
      (coeffEmb K jq)) = sv K ζ a b := by
  rw [sv_eq, coeffEmb_jq]
  show TS K (a * a) (ζ ^ (b % d'' * a) * ζ ^ (b / d'' * (M / p))) = TS K (a * a) (ζ ^ (b * a))
  refine TS_congr' rfl ?_
  rw [hMp, ← pow_add]
  congr 1
  rw [show b % d'' * a + b / d'' * (a * d'')
    = (b % d'' + b / d'' * d'') * a from by ring, hbsplit]

/-- **Transfer to the base field**: a root of the `ψ`-push of the minimal polynomial over
`A = ℚ⟮jq⟯⟮jqN d⟯` is a root of the `(coeffEmb K ∘ qExpand ℚ M)`-push of the minimal
polynomial over `ℚ⟮jq⟯`: the base minimal polynomial maps into `A` as a multiple of the
`A`-minimal polynomial. -/
private theorem isRoot_map_minpoly_of_isRoot_subfield {M d : ℕ} [NeZero M] [NeZero d]
    {ψ : ℚ⟮jq⟯⟮jqN d⟯ →+* LaurentSeries K}
    (hψcomp : ψ.comp (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯)
      = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
    {x : LaurentSeries K}
    (hroot : ((minpoly ℚ⟮jq⟯⟮jqN d⟯ (jqN M)).map ψ).IsRoot x) :
    ((minpoly ℚ⟮jq⟯ (jqN M)).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot x := by
  have htowdvd : minpoly ℚ⟮jq⟯⟮jqN d⟯ (jqN M)
      ∣ (minpoly ℚ⟮jq⟯ (jqN M)).map (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯) :=
    minpoly.dvd_map_of_isScalarTower ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN d⟯ (jqN M)
  have h1 := Polynomial.map_dvd ψ htowdvd
  rw [Polynomial.map_map] at h1
  rw [hψcomp] at h1
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h1 hroot

/-- **The conjugate at the descended slot**: if the expanded slot value
`qExpand K p (sv K (ζ ^ p) a (b % d''))` is a root of the `qExpand ℚ M`-push of
`minpoly ℚ⟮jq⟯ (jqN (a * d''))`, then it is the image of the slot generator under a
`ℚ⟮jq⟯`-algebra map `ψ₁` out of `A = ℚ⟮jq⟯⟮jqN (a * d'')⟯`, and the push of scalars along
`ψ₁` is the `(coeffEmb K).comp (qExpand ℚ M)` map. This is the pin's
`p2m_open`-instance step: the `AlgHom` needs the `letI : Algebra ℚ⟮jq⟯ (LaurentSeries K)`
of the caller, which is why it is taken as an instance argument here. -/
private theorem exists_algHom_adjoin_of_isRoot {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] [NeZero (a * d'')] {ζ : Kˣ}
    (hα' : IsIntegral ℚ⟮jq⟯ (jqN (a * d'')))
    (hroot' : ((minpoly ℚ⟮jq⟯ (jqN (a * d''))).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (qExpand K p (sv K (ζ ^ p) a (b % d''))))
    [Algebra ℚ⟮jq⟯ (LaurentSeries K)]
    (halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) :
    ∃ ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K,
      ψ₁ (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
          = qExpand K p (sv K (ζ ^ p) a (b % d''))
        ∧ (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K).comp
            (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯)
          = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
  have hy_mem : qExpand K p (sv K (ζ ^ p) a (b % d''))
      ∈ (minpoly ℚ⟮jq⟯ (jqN (a * d''))).aroots (LaurentSeries K) := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hα', ?_⟩
    rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map]
    exact hroot'
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K,
      ψ₁ (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
        = qExpand K p (sv K (ζ ^ p) a (b % d'')) :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv ℚ⟮jq⟯ hα').symm ⟨_, hy_mem⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ⟮jq⟯ hα' ⟨_, hy_mem⟩⟩
  refine ⟨ψ₁, hψ₁, ?_⟩
  rw [AlgHom.comp_algebraMap]
  exact halg

/-- **The seed polynomial at the descended conjugate**: for `a * d'' = p * m` the seed
polynomial `phiAtSeed dp`, evaluated at the expanded slot
`qExpand K p (sv K (ζ ^ p) a (b % d''))`, is rooted at `ψ ⟨jqN m, _⟩`. The proof reads the
vanishing of `phiAtSeed dp` at `jqN (a * d'')` through `EvalSymm` (`phiAtSeed_eval_symm`),
descends it to the element of `A`, and pushes it along `ψ`. -/
private theorem isRoot_phiAtSeed_slot_apply {a b d'' p m : ℕ} [NeZero a]
    [NeZero p] [NeZero (a * d'')] [NeZero m] {ζ : Kˣ} {dp : ModularPolynomialData p} (hdpsym : EvalSymm dp.Φ)
    (hm : a * d'' = p * m) {hmem : jqN m ∈ ℚ⟮jq⟯⟮jqN (a * d'')⟯}
    {ψ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
      = qExpand K p (sv K (ζ ^ p) a (b % d''))) :
    (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot (ψ ⟨jqN m, hmem⟩) := by
  have hdown : (phiAtSeed dp (jqN (a * d''))).eval (jqN m) = 0 := by
    rw [phiAtSeed_eval_symm dp hdpsym]
    have h1 := phiAtSeed_jqN_eval p dp m
    rwa [show jqN (m * p) = jqN (a * d'') from jqN_congr (by rw [hm]; ring)] at h1
  have hdownF₁ : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯
      (jqN (a * d'')))).eval (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) = 0 :=
    phiAtSeed_eval_of_injective dp _ _
      (algebraMap ℚ⟮jq⟯⟮jqN (a * d'')⟯ (LaurentSeries ℚ)) (RingHom.injective _) hdown
  have h1 := phiAtSeed_eval_map dp _ _ ψ hdownF₁
  rwa [hψ₁] at h1

/-- **Separation at the descended point** (the case `p ∣ a * d''`): if `a * d'' = m * p` and
`m < M`, then the slot value `sv K ζ a b` is not the image `ψ ⟨jqN m, _⟩` of the descended
conjugate. If it were, `TS`-injectivity applied to the slot product at `m` (the induction
hypothesis for `ζ ^ (p * p)`) would force `p ∣ gcd (gcd a b) (M / a)`, against the
coprimality of the slot. -/
private theorem sv_ne_image_of_dvd {M a b d'' p m : ℕ} [NeZero M] [NeZero a] [NeZero d'']
    [NeZero p] [NeZero m] {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) (hpp : p.Prime)
    (hMM' : M = a * d'' * p) (hm : a * d'' = p * m) (hm0 : m ≠ 0) (hmM : m ∣ M)
    (hmlt : m < M) (hbr : b < M / a) (haM : a ∣ M)
    (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) (hdd : M / a = p * d'')
    (hmem : jqN m ∈ ℚ⟮jq⟯⟮jqN (a * d'')⟯)
    {ψ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K}
    (hroot : ((minpoly ℚ⟮jq⟯ (jqN m)).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (ψ ⟨jqN m, hmem⟩))
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) :
    sv K ζ a b ≠ ψ ⟨jqN m, hmem⟩ := by
  intro hcon
  have hζ'' : IsPrimitiveRoot ((ζ ^ (p * p) : Kˣ) : K) m := by
    have h1 := isPrimitiveRoot_pow_div hζ hmM
    have h2 : M / m = p * p := by
      have hM : M = m * (p * p) := by rw [hMM', hm]; ring
      rw [hM]
      exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)
    rwa [h2] at h1
  have hIH'' := IH m hmlt (ζ ^ (p * p)) hζ''
    (fun e he'' _ => hall e (he''.trans hmM))
  have hIHM'' := map_qExpand_minpoly_eq (p * p)
    (show M = p * p * m from by rw [hMM', hm]; ring) (ζ ^ (p * p)) hIH''
  rw [hIHM'', Polynomial.IsRoot, Polynomial.eval_prod] at hroot
  obtain ⟨α, hαmem, hα0⟩ := Finset.prod_eq_zero_iff.mp hroot
  rw [Polynomial.eval_prod] at hα0
  obtain ⟨β, hβmem, hβ0⟩ := Finset.prod_eq_zero_iff.mp hα0
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hβ0
  obtain ⟨hαdvd, -⟩ := Nat.mem_divisors.mp hαmem
  obtain ⟨hβr, -⟩ := Finset.mem_filter.mp hβmem
  rw [Finset.mem_range] at hβr
  have hα0' : α ≠ 0 := by
    rintro rfl
    exact hm0 (Nat.eq_zero_of_zero_dvd hαdvd)
  haveI : NeZero α := ⟨hα0'⟩
  have hcoll : TS K (a * a) (ζ ^ (b * a))
      = TS K (p * p * (α * α)) (ζ ^ (p * p * (β * α))) := by
    calc TS K (a * a) (ζ ^ (b * a)) = sv K ζ a b := (sv_eq_TS ζ a b).symm
      _ = ψ ⟨jqN m, hmem⟩ := hcon
      _ = qExpand K (p * p) (sv K (ζ ^ (p * p)) α β) := hβ0
      _ = qExpand K (p * p) (TS K (α * α) ((ζ ^ (p * p)) ^ (β * α))) := by
          rw [sv_eq_TS]
      _ = TS K (p * p * (α * α)) ((ζ ^ (p * p)) ^ (β * α)) := qExpand_TS _ _ _
      _ = TS K (p * p * (α * α)) (ζ ^ (p * p * (β * α))) :=
          TS_congr' rfl (by rw [← pow_mul])
  obtain ⟨hexp, hunit⟩ := TS_injective hcoll
  have haα : a = p * α := by
    have h2 : a * a = (p * α) * (p * α) := by rw [hexp]; ring
    exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp h2
  have hpa : p ∣ a := ⟨α, haα⟩
  have hba : b * a < M := by
    calc b * a < M / a * a :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne a))).mpr hbr
      _ = M := Nat.div_mul_cancel haM
  have hppβα : p * p * (β * α) < M := by
    have h1 : β * α < m := by
      calc β * α < m / α * α :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hα0')).mpr hβr
        _ ≤ m := Nat.div_mul_le_self m α
    calc p * p * (β * α) < p * p * m :=
        (Nat.mul_lt_mul_left (Nat.mul_pos hpp.pos hpp.pos)).mpr h1
      _ = M := by rw [hMM', hm]; ring
  have hvv : ((ζ : K)) ^ (b * a) = ((ζ : K)) ^ (p * p * (β * α)) := by
    have h1 := congrArg Units.val hunit
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  have hexp2 : b * a = p * p * (β * α) := hζ.pow_inj hba hppβα hvv
  have hpb : p ∣ b := by
    refine ⟨β, ?_⟩
    rw [haα] at hexp2
    have h1 : b * (p * α) = p * β * (p * α) := by
      rw [hexp2]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpp.pos
      (Nat.pos_of_ne_zero hα0')) h1
  have hfinal : p ∣ Nat.gcd (Nat.gcd a b) (M / a) :=
    Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) ⟨d'', hdd⟩
  rw [hbc] at hfinal
  exact hpp.ne_one (Nat.dvd_one.mp hfinal)

/-- **The root at a slot when `p ∣ a * d''`** (one case of the descent): the minimal
polynomial of `jqN M` over `A = ℚ⟮jq⟯⟮jqN (a * d'')⟯` has degree `p`, one less than the
seed polynomial `phiAtSeed dp` of degree `p + 1`; it is therefore the seed polynomial
divided by the linear factor at the descended conjugate. Evaluating the remaining `p`
finite conjugates at `sv K ζ a b` gives a root. -/
private theorem isRoot_map_minpoly_sv_of_dvd {M a b d'' p m : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] [NeZero m] {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hpp : p.Prime) (hpM : p ∣ M) (dp : ModularPolynomialData p)
    (hα₁ : IsIntegral ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M))
    (hdeg : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).natDegree = p)
    (hmem : jqN m ∈ ℚ⟮jq⟯⟮jqN (a * d'')⟯)
    (hmindvd : minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d''))))
    (hc₀p : b / d'' < p)
    (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b)
    {ψ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
      = qExpand K p (sv K (ζ ^ p) a (b % d'')))
    (hψx : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
      (ψ ⟨jqN m, hmem⟩))
    (hψxnotmin : ¬ ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ).IsRoot
      (ψ ⟨jqN m, hmem⟩))
    (htarget_ne : sv K ζ a b ≠ ψ ⟨jqN m, hmem⟩) :
    ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ).IsRoot (sv K ζ a b) := by
  have hΦfact := phiAtSeed_slot_factor (M := M) (a := a) (b := b % d'') (p := p) (K := K)
    hζ hpp hpM dp
  have htarget := qExpand_qTwist_slot_eq_sv (M := M) (a := a) (b := b) (d'' := d'') (p := p)
    (K := K) (ζ := ζ) hMp hbsplit
  have hQ : (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩)) *
      (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩)))
      = phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hψx
  have hΦmonic : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).Monic :=
    phiAtSeed_monic dp _
  have hQmonic : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
      (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩))).Monic :=
    Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C _)
      (by rw [hQ]; exact hΦmonic)
  have hΦdeg : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree]
    exact dedekindPsi_prime hpp
  have hQdeg : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
      (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩))).natDegree = p := by
    have h1 : p + 1 = 1 + (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩))).natDegree := by
      rw [← hΦdeg]
      conv_lhs => rw [← hQ]
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hQmonic.ne_zero,
        Polynomial.natDegree_X_sub_C]
    omega
  have hP₁dvd : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ
      ∣ phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) := by
    have h1 := Polynomial.map_dvd ψ hmindvd
    rwa [phiAtSeed_map, hψ₁] at h1
  have hcop : IsCoprime (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩))
      ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ) := by
    rw [(Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd]
    intro hcon
    exact hψxnotmin (Polynomial.dvd_iff_isRoot.mp hcon)
  have hP₁dvdQ : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ
      ∣ phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩)) := by
    have h1 := hP₁dvd
    rw [← hQ] at h1
    exact (hcop.symm).dvd_of_dvd_mul_left h1
  have hdeg₁ : ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ).natDegree = p := by
    rw [Polynomial.Monic.natDegree_map (minpoly.monic hα₁)]
    exact hdeg
  have hmineqQ : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ
      = phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩)) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le ((minpoly.monic hα₁).map _)
      hQmonic hP₁dvdQ (le_of_eq (hQdeg.trans hdeg₁.symm)) |>.symm
  have htargetΦ : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
      (sv K ζ a b) := by
    rw [hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
    refine mul_eq_zero.mpr (Or.inr ?_)
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
    rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  rw [hmineqQ, Polynomial.IsRoot]
  have h1 : ((Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩)) *
      (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqN m, hmem⟩)))).eval (sv K ζ a b) = 0 := by
    rw [hQ]
    exact htargetΦ
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) htarget_ne
  · exact h2

/-- **The root at a slot when `p ∤ a * d''`** (the other case of the descent): the degree of
`jqN M` over `A = ℚ⟮jq⟯⟮jqN (a * d'')⟯` is `p + 1`, the degree of `phiAtSeed dp`; the two
monic polynomials coincide, and `sv K ζ a b` is one of the `p` finite conjugates of `Φ_p` at
that slot. -/
private theorem isRoot_map_minpoly_sv_of_not_dvd {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) (hpp : p.Prime)
    (hpM : p ∣ M) (dp : ModularPolynomialData p) (hpM' : ¬ p ∣ a * d'')
    (hstep : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯
        (ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯) * dedekindPsi (a * d'') = dedekindPsi M)
    (hMM' : M = a * d'' * p) (hM'0 : a * d'' ≠ 0)
    (hα₁ : IsIntegral ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M))
    (hmindvd : minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d''))))
    (hc₀p : b / d'' < p)
    (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b)
    {ψ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
      = qExpand K p (sv K (ζ ^ p) a (b % d''))) :
    ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map ψ).IsRoot (sv K ζ a b) := by
  have hΦfact := phiAtSeed_slot_factor (M := M) (a := a) (b := b % d'') (p := p) (K := K)
    hζ hpp hpM dp
  have htarget := qExpand_qTwist_slot_eq_sv (M := M) (a := a) (b := b) (d'' := d'') (p := p)
    (K := K) (ζ := ζ) hMp hbsplit
  have hψM : dedekindPsi M = dedekindPsi (a * d'') * (p + 1) := by
    rw [hMM']
    exact dedekindPsi_mul_prime_not_dvd hpp hpM'
  have he : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ (ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯) = p + 1 := by
    have h1 : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯
        (ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯) * dedekindPsi (a * d'')
        = (p + 1) * dedekindPsi (a * d'') := by
      rw [hstep, hψM]
      ring
    exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos _ hM'0) h1
  have hdeg₁ : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hα₁]
    exact he
  have hΦdeg : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯
      (jqN (a * d'')))).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree]
    exact dedekindPsi_prime hpp
  have hmineq : minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
      = phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d''))) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hα₁)
      (phiAtSeed_monic dp _) hmindvd (le_of_eq (hΦdeg.trans hdeg₁.symm)) |>.symm
  rw [hmineq, phiAtSeed_map, hψ₁, hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
  refine mul_eq_zero.mpr (Or.inr ?_)
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
  rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- **The root at a descending slot** (the main case `M / a ≠ 1` of
`isRoot_map_minpoly_sv`): let `p = (M / a).minFac` and `M / a = p * d''`. Replacing `M` by
`a * d''` and `ζ` by `ζ ^ p` (the induction hypothesis), the slot `(a, b % d'')` at level
`a * d''` pushes up to a conjugate `ψ₁` of `jqN M` over `ℚ⟮jq⟯⟮jqN (a * d'')⟯`; the value
`sv K ζ a b` is then read off the `Φ_p`-factorisation at that conjugate, in the two cases
`p ∣ a * d''` and `p ∤ a * d''`. -/
private theorem isRoot_map_minpoly_sv_of_descent {M : ℕ} [NeZero M] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d)
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ)
    {a b : ℕ} (haM : a ∣ M) (ha0 : a ≠ 0) (hd1 : M / a ≠ 1) (hbr : b < M / a)
    (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) :
    ((minpoly ℚ⟮jq⟯ (jqN M)).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (sv K ζ a b) := by
  classical
  obtain ⟨htM_self, hgM_self⟩ := hall M dvd_rfl
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  obtain ⟨p, d'', hpp, hd''0, hdd, hb''lt, hc₀p, hprim', hbsplit⟩ :=
    exists_slot_descent_data (NeZero.ne M) haM hd1 hbr hbc
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero d'' := ⟨hd''0⟩
  have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero ha0 hd''0
  haveI : NeZero (a * d'') := ⟨hM'0⟩
  have hMM' : M = a * d'' * p := by rw [← had, hdd]; ring
  have hM'M : a * d'' ∣ M := ⟨p, hMM'⟩
  have hM'lt : a * d'' < M := by
    calc a * d'' = a * d'' * 1 := by ring
      _ < a * d'' * p := (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hM'0)).mpr hpp.one_lt
      _ = M := hMM'.symm
  have hpM : p ∣ M := by
    have hpd : p ∣ M / a := ⟨d'', hdd⟩
    exact hpd.trans (Nat.div_dvd_of_dvd haM)
  have hMp : M / p = a * d'' := by
    rw [hMM']
    exact Nat.mul_div_cancel _ hpp.pos
  have hζ' : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) (a * d'') := by
    have h1 := isPrimitiveRoot_pow_div hζ hM'M
    have h2 : M / (a * d'') = p := by
      rw [hMM']
      exact Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM'0)
    rwa [h2] at h1
  -- the induction hypothesis at `a * d''`, pushed up by `qExpand K p`
  have hprod := IH (a * d'') hM'lt (ζ ^ p) hζ' (fun e he _ => hall e (he.trans hM'M))
  have hroot' := isRoot_qExpand_sv_of_slot_product (M := M) (a := a) (b := b) (d'' := d'')
    (p := p) (K := K) (ζ := ζ) (show M = p * (a * d'') from by rw [hMM']; ring) hprod
    hb''lt hprim'
  -- the conjugate `ψ₁` at the descended slot; the `Algebra` instance is the pin's `letI`
  obtain ⟨htM', hgM'⟩ := hall (a * d'') hM'M
  have hα' : IsIntegral ℚ⟮jq⟯ (jqN (a * d'')) := isIntegral_adjoin_jqN htM'
  letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
  have halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) :=
    RingHom.algebraMap_toAlgebra _
  obtain ⟨ψ₁, hψ₁, hψcomp⟩ := exists_algHom_adjoin_of_isRoot (K := K) hα' hroot' halg
  -- the seed polynomial at the descended slot
  obtain ⟨dp, _, hdpsym⟩ := exists_phiIrreducible_evalSymm p
  have hup : (phiAtSeed dp (jqN (a * d''))).eval (jqN M) = 0 := by
    have h1 := phiAtSeed_jqN_eval p dp (a * d'')
    rwa [show jqN (a * d'' * p) = jqN M from jqN_congr hMM'.symm] at h1
  have haev : Polynomial.aeval (jqN M)
      (phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, phiAtSeed_map]
    exact hup
  have hα₁ : IsIntegral ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M) :=
    ⟨phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d''))),
      phiAtSeed_monic dp _, by rw [← Polynomial.aeval_def]; exact haev⟩
  have hmindvd : minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d''))) :=
    minpoly.dvd _ _ haev
  -- the degree of the step and its two prime cases
  have hstep := finrank_adjoin_mul_dedekindPsi hM'M htM_self hgM_self htM'
  by_cases hpM' : p ∣ a * d''
  · -- `p ∣ a * d''`: the degree over `A` is `p`, and the seed polynomial is divided
    have hψM : dedekindPsi M = dedekindPsi (a * d'') * p := by
      rw [hMM']
      exact dedekindPsi_mul_prime_dvd hpp hpM'
    have he : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ (ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯) = p := by
      have h1 : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯
          (ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯) * dedekindPsi (a * d'')
          = p * dedekindPsi (a * d'') := by
        rw [hstep, hψM]
        ring
      exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos _ hM'0) h1
    have hdeg : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).natDegree = p := by
      rw [← IntermediateField.adjoin.finrank hα₁]
      exact he
    obtain ⟨m, hm⟩ := hpM'
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact hM'0 hm
    haveI : NeZero m := ⟨hm0⟩
    have hmM : m ∣ M := ⟨p * p, by rw [hMM', hm]; ring⟩
    have hmlt : m < M := by
      calc m ≤ a * d'' := by rw [hm]; exact Nat.le_mul_of_pos_left m hpp.pos
        _ < M := hM'lt
    have hmem : jqN m ∈ ℚ⟮jq⟯⟮jqN (a * d'')⟯ := by
      have h1 : jqN m ∈ modularFunctionFieldFull (a * d'') :=
        jqd_mem_full (a * d'') ⟨p, by rw [hm]; ring⟩
      rw [← hgM'] at h1
      exact mem_adjoin_jqN_of_mem_mff h1
    have hxnotmin : ¬ (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).IsRoot
        (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) :=
      not_isRoot_minpoly_of_prime_deg p hpp hα₁ hdeg ⟨jqN m, hmem⟩
    have hψxnotmin : ¬ ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
        (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)).IsRoot
        (ψ₁ (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)) := by
      intro hcon
      refine hxnotmin ?_
      rw [Polynomial.IsRoot, Polynomial.eval_map,
        show ψ₁ (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)
          = (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) from rfl,
        Polynomial.eval₂_hom] at hcon
      exact (injective_iff_map_eq_zero _).mp
        (RingHom.injective (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)) _ hcon
    have htarget_ne : sv K ζ a b ≠ ψ₁ (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) := by
      intro hcon
      have hroot'' : ((minpoly ℚ⟮jq⟯ (jqN m)).map (((coeffEmb K).comp
          (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
          (ψ₁ (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)) := by
        have h1 : Polynomial.aeval (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)
            (minpoly ℚ⟮jq⟯ (jqN m)) = 0 := by
          refine aeval_intermediateField_eq_zero ?_
          show Polynomial.aeval (jqN m) (minpoly ℚ⟮jq⟯ (jqN m)) = 0
          exact minpoly.aeval _ _
        have h2 := Polynomial.aeval_algHom_apply ψ₁
          (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) (minpoly ℚ⟮jq⟯ (jqN m))
        rw [h1, map_zero] at h2
        rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map] at h2
        exact h2
      exact sv_ne_image_of_dvd (ψ := (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K))
        hζ hpp hMM' hm hm0 hmM hmlt hbr haM hbc hdd hmem hroot'' IH hall hcon
    have hψx : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
        (ψ₁ (⟨jqN m, hmem⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)) :=
      isRoot_phiAtSeed_slot_apply (K := K) (dp := dp) (m := m) hdpsym hm
        (ψ := (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)) hψ₁
    have hroot_step := isRoot_map_minpoly_sv_of_dvd (K := K)
      (ψ := (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K))
      hζ hpp hpM dp hα₁ hdeg hmem hmindvd hc₀p hMp hbsplit hψ₁ hψx hψxnotmin htarget_ne
    exact isRoot_map_minpoly_of_isRoot_subfield (K := K) hψcomp hroot_step
  · -- `p ∤ a * d''`: degrees agree, so the minimal polynomial *is* the seed polynomial
    exact isRoot_map_minpoly_of_isRoot_subfield (K := K) hψcomp
      (isRoot_map_minpoly_sv_of_not_dvd (K := K)
        (ψ := (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K))
        hζ hpp hpM dp hpM' hstep hMM' hM'0 hα₁ hmindvd hc₀p hMp hbsplit hψ₁)

/-- **Every slot value is a root**: for a slot `(a, b)` of `M` (`a ∈ M.divisors`,
`b < M / a` coprime to `M / a`), the value `sv K ζ a b` is a root of the
`(coeffEmb K ∘ qExpand ℚ M)`-push of `minpoly ℚ⟮jq⟯ (jqN M)`. Either `a = M` (the top slot,
`b = 0`), or the slot descends along the least prime of `M / a` to the level `a * d''`. -/
private theorem isRoot_map_minpoly_sv {M : ℕ} [NeZero M] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d)
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ)
    {a b : ℕ} (ha : a ∈ M.divisors)
    (hb : b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)) :
    ((minpoly ℚ⟮jq⟯ (jqN M)).map
      (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (sv K ζ a b) := by
  obtain ⟨haM, -⟩ := Nat.mem_divisors.mp ha
  have hbr : b < M / a := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1 := (Finset.mem_filter.mp hb).2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact NeZero.ne M (Nat.eq_zero_of_zero_dvd haM)
  by_cases hd1 : M / a = 1
  · exact isRoot_map_minpoly_sv_top (K := K) ζ haM hd1 hb
  · exact isRoot_map_minpoly_sv_of_descent (K := K) ζ hζ hall IH haM ha0 hd1 hbr hbc

/-- **The slot product** (strong induction on `M`): the mapped minimal polynomial of `jqN M`
over `ℚ⟮jq⟯` is the product of `X - C (sv K ζ a b)` over the slots. The `ψ(M)` slot values
are distinct roots (`isRoot_map_minpoly_sv`, `nodup_slotValues_sv`), and `ψ(M) = deg` of that
polynomial, so they are exactly its roots. -/
private theorem rval_aux : ∀ (M : ℕ) [NeZero M] {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : Kˣ), IsPrimitiveRoot ((ζ : Kˣ) : K) M →
    (∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) →
    (minpoly ℚ⟮jq⟯ (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b)) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
  intro _ K _ _ ζ hζ hall
  classical
  by_cases hM1 : M = 1
  · subst hM1
    exact minpoly_map_eq_prod_slots_one (K := K) ζ
  · have hM0 : M ≠ 0 := NeZero.ne M
    obtain ⟨htM_self, -⟩ := hall M dvd_rfl
    have hα : IsIntegral ℚ⟮jq⟯ (jqN M) := isIntegral_adjoin_jqN htM_self
    have hdeg : (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M :=
      natDegree_minpoly_jqN htM_self
    have hPne : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) ≠ 0 :=
      ((minpoly.monic hα).map _).ne_zero
    have hPdeg : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).natDegree = dedekindPsi M := by
      rw [Polynomial.Monic.natDegree_map (minpoly.monic hα)]
      exact hdeg
    have IH' : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ := by
      intro n hn _ ζ'
      exact IH n hn ζ'
    have hroot : ∀ a b : ℕ, a ∈ M.divisors →
        b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) →
        ((minpoly ℚ⟮jq⟯ (jqN M)).map
          (((coeffEmb K).comp (qExpand ℚ M)).comp
            (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot (sv K ζ a b) :=
      fun a b ha hb => isRoot_map_minpoly_sv ζ hζ hall IH' ha hb
    have hTnodup : (slotValues M (fun a b => sv K ζ a b)).Nodup :=
      nodup_slotValues_sv hM0 hζ
    have hTle : slotValues M (fun a b => sv K ζ a b) ≤
        ((minpoly ℚ⟮jq⟯ (jqN M)).map
          (((coeffEmb K).comp (qExpand ℚ M)).comp
            (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ slotValues M (fun a b => sv K ζ a b)
      · have h1 : Multiset.count x (slotValues M (fun a b => sv K ζ a b)) ≤ 1 :=
          Multiset.nodup_iff_count_le_one.mp hTnodup x
        have h2 : 1 ≤ Multiset.count x ((minpoly ℚ⟮jq⟯ (jqN M)).map
            (((coeffEmb K).comp (qExpand ℚ M)).comp
              (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots := by
          rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots']
          obtain ⟨a, b, ha, hb, rfl⟩ := mem_slotValues.mp hx
          exact ⟨hPne, hroot a b ha hb⟩
        omega
      · rw [Multiset.count_eq_zero.mpr hx]
        exact Nat.zero_le _
    have hroots_eq : ((minpoly ℚ⟮jq⟯ (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ M)).comp
          (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots
        = slotValues M (fun a b => sv K ζ a b) := by
      refine (Multiset.eq_of_le_of_card_le hTle ?_).symm
      rw [card_slotValues hM0 _ (card_slotFilter_eq_dedekindPsi M hM0)]
      calc Multiset.card ((minpoly ℚ⟮jq⟯ (jqN M)).map
            (((coeffEmb K).comp (qExpand ℚ M)).comp
              (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots
          ≤ ((minpoly ℚ⟮jq⟯ (jqN M)).map
            (((coeffEmb K).comp (qExpand ℚ M)).comp
              (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).natDegree := Polynomial.card_roots' _
        _ = dedekindPsi M := hPdeg
    have hsp : Polynomial.Splits ((minpoly ℚ⟮jq⟯ (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ M)).comp
          (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) := by
      rw [Polynomial.splits_iff_card_roots, hroots_eq, card_slotValues hM0 _ (card_slotFilter_eq_dedekindPsi M hM0), hPdeg]
    have hfact := hsp.eq_prod_roots_of_monic ((minpoly.monic hα).map _)
    rw [hfact, hroots_eq]
    exact prod_slotValues M (fun a b => sv K ζ a b)

end RValCore

/-! ## The public node -/

/-- **The slot product**: the mapped minimal polynomial of `jqN M` is the product
of `(X - C (sv K ζ a b))` over the slots. This is the `Inputs` field
`minpoly_jqN_map_eq_prod_slots`. Verbatim from
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
  rval_aux M ζ hζ hall

/-! ## The `M`-arbitrary non-membership

`j(q ^ p) ∉ F_M^full` for `p ∤ M`, from `Hall M`. The `hall` at `d = p` uses
T18's `gen_prime` (and `tight_one`/`gen_one` at `d = 1`) instead of the pin's
`functionFieldGeneration_of_squarefree p`, so no squarefree-block declaration is
pulled in; `mem_range_of_eval_eq_const` is T4's engine from
`FieldTheory/CommonRoot.lean`, not restated.

The slot product at `M` for the primitive root `ζ ^ p` gives the `ψ(M)` roots of the
pushed minimal polynomial, and they are exactly the `ψ(M)` distinct slot values
(`hroots`). Reading `j(q ^ p) = g (j(q ^ M))` with `deg g < ψ(M)`, the polynomial `g`
is constant on those slots (`eval_map_eq_of_mem_slotValues`), so its value lies in the
image of `(coeffEmb K).comp (qExpand ℚ (M * p))` (`mem_range_of_eval_eq_const`), which
forces `j(q ^ p)` into the base field. -/

section NonMem0

open IntermediateField

/-- **A conjugate maps the adjoin into the `qExpand K p`-image**: if `y` lies in the image of
`qExpand K p`, the push of scalars along `ψy` is the `coeffEmb` map, and
`qExpand K p` of a `coeffEmb`-image is a `coeffEmb`-image (`hιS`), then `ψy` sends *every*
element of `ℚ⟮jq⟯⟮jqN M⟯` into that image. The induction is over the simple extension. -/
private theorem map_mem_fieldRange {M p : ℕ} [NeZero M] [NeZero p] {y : LaurentSeries K}
    [Algebra ℚ⟮jq⟯ (LaurentSeries K)]
    {ψy : ℚ⟮jq⟯⟮jqN M⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K}
    (hψgen : ∀ h : jqN M ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)),
      ψy ⟨jqN M, h⟩ = y)
    (hyS : y ∈ (qExpand K p).fieldRange)
    (hιS : ∀ w : LaurentSeries ℚ, coeffEmb K (qExpand ℚ (M * p) w)
      = qExpand K p (coeffEmb K (qExpand ℚ M w)))
    (halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) :
    ∀ (x : LaurentSeries ℚ)
      (hx : x ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))),
      ψy ⟨x, hx⟩ ∈ (qExpand K p).fieldRange := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hψgen]
      exact hyS
  | algebraMap z =>
      show ψy (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN M⟯ z) ∈ (qExpand K p).fieldRange
      rw [AlgHom.commutes, halg]
      show coeffEmb K (qExpand ℚ (M * p)
        ((algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) z)) ∈ (qExpand K p).fieldRange
      rw [hιS]
      exact RingHom.mem_fieldRange.mpr ⟨_, rfl⟩
  | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      show ψy ⟨x₁ + x₂, add_mem hx₁ hx₂⟩ ∈ (qExpand K p).fieldRange
      rw [show (⟨x₁ + x₂, add_mem hx₁ hx₂⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ from rfl, map_add]
      exact Subfield.add_mem _ ih₁ ih₂
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      show ψy ⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ ∈ (qExpand K p).fieldRange
      rw [show (⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        = ⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩ from rfl, map_mul]
      exact Subfield.mul_mem _ ih₁ ih₂
  | inv x₁ hx₁ ih₁ =>
      show ψy ⟨x₁⁻¹, inv_mem hx₁⟩ ∈ (qExpand K p).fieldRange
      rw [show (⟨x₁⁻¹, inv_mem hx₁⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        = (⟨x₁, hx₁⟩ : ℚ⟮jq⟯⟮jqN M⟯)⁻¹ from rfl, map_inv₀]
      exact Subfield.inv_mem _ ih₁
/-- **The `hall` hypothesis at the prime `p`**: for each divisor `d` of `p` the degree and
function-field conditions hold — `tight_one`/`gen_one` at `d = 1`, and
`finrank_adjoin_jqN_eq_of_prime`/`gen_prime` at `d = p`. -/
private theorem hall_prime (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∀ d : ℕ, d ∣ p → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d := by
  intro d hd _
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out d hd) with h1 | h2
  · subst h1
    exact ⟨tight_one, gen_one⟩
  · have h2' := h2.symm
    subst h2'
    constructor
    · rw [dedekindPsi_prime hp.out]
      exact finrank_adjoin_jqN_eq_of_prime p
    · exact gen_prime p

/-- **`g` is constant on the slots**: if `j(q ^ p)` lies in `ℚ⟮jq⟯⟮jqN M⟯` and is
represented there by a polynomial `g'` (`hg'`), then `g'` takes the same value
`coeffEmb K (qExpand ℚ (M * p) (jqN p))` at every slot of the `ζ ^ p`-slot product. The
proof evaluates `g'` through a conjugate `ψy` at each slot `y`; `ψy` maps the whole field
into the image of `qExpand K p`, where the `Φ_p`-factorisation pins the value down. The
`Algebra` instance and `halg` are the pin's `letI`: the `(coeffEmb K ∘ qExpand ℚ (M * p))`
push of scalars. -/
private theorem eval_map_eq_of_mem_slotValues {M p : ℕ} [NeZero M] [NeZero p]
    [hp : Fact (Nat.Prime p)] {ζ : Kˣ} (hpM : ¬ p ∣ M)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) (M * p))
    (hα : IsIntegral ℚ⟮jq⟯ (jqN M))
    (hroots : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots
      = slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b)))
    (hmem : jqN p ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)))
    [Algebra ℚ⟮jq⟯ (LaurentSeries K)]
    (halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
    {g' : Polynomial ℚ⟮jq⟯}
    (hg' : Polynomial.aeval (jqN M) g' = jqN p)
    {y : LaurentSeries K}
    (hy : y ∈ slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))) :
    Polynomial.aeval y g' = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  have hζM : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  have hζp : IsPrimitiveRoot ((ζ ^ M : Kˣ) : K) p := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨M, Nat.mul_comm M p⟩ : p ∣ M * p)
    have h2 : M * p / p = M := Nat.mul_div_cancel M (Nat.pos_of_ne_zero hp0)
    rwa [h2] at h1
  have hιS : ∀ w : LaurentSeries ℚ, coeffEmb K (qExpand ℚ (M * p) w)
      = qExpand K p (coeffEmb K (qExpand ℚ M w)) := by
    intro w
    rw [← coeffEmb_qExpand, qExpand_qExpand]
    exact congrArg (coeffEmb K) (qExpand_congr (Nat.mul_comm M p) w)
  have hidpB := map_qExpand_minpoly_eq M rfl (ζ ^ M) (rval_aux p (ζ ^ M) hζp (hall_prime p))
  obtain ⟨a₀, b₀, ha₀, hb₀, hyval⟩ := mem_slotValues.mp hy
  have hyS : y ∈ (qExpand K p).fieldRange := by
    rw [hyval]
    exact RingHom.mem_fieldRange.mpr ⟨sv K (ζ ^ p) a₀ b₀, rfl⟩
  have hy_ar : y ∈ (minpoly ℚ⟮jq⟯ (jqN M)).aroots (LaurentSeries K) := by
    rw [Polynomial.aroots_def, halg, hroots]
    exact hy
  obtain ⟨ψy, hψy⟩ : ∃ ψy : ℚ⟮jq⟯⟮jqN M⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K,
      ψy (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) = y :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv ℚ⟮jq⟯ hα).symm ⟨y, hy_ar⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ⟮jq⟯ hα ⟨y, hy_ar⟩⟩
  have hψgen : ∀ h : jqN M ∈ IntermediateField.adjoin ℚ⟮jq⟯
      ({jqN M} : Set (LaurentSeries ℚ)), ψy ⟨jqN M, h⟩ = y := by
    intro h
    exact hψy
  have himg := map_mem_fieldRange (K := K) hψgen hyS hιS halg
  have hx_pS : ψy ⟨jqN p, hmem⟩ ∈ (qExpand K p).fieldRange := himg _ hmem
  have hx_proot : ((minpoly ℚ⟮jq⟯ (jqN p)).map (((coeffEmb K).comp
      (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (ψy ⟨jqN p, hmem⟩) := by
    have h1 : Polynomial.aeval (⟨jqN p, hmem⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        (minpoly ℚ⟮jq⟯ (jqN p)) = 0 := by
      refine aeval_intermediateField_eq_zero ?_
      show Polynomial.aeval (jqN p) (minpoly ℚ⟮jq⟯ (jqN p)) = 0
      exact minpoly.aeval _ _
    have h2 := Polynomial.aeval_algHom_apply ψy (⟨jqN p, hmem⟩ : ℚ⟮jq⟯⟮jqN M⟯)
      (minpoly ℚ⟮jq⟯ (jqN p))
    rw [h1, map_zero] at h2
    rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map] at h2
    exact h2
  rw [hidpB, Polynomial.IsRoot, Polynomial.eval_prod] at hx_proot
  obtain ⟨α, hαmem, hα0⟩ := Finset.prod_eq_zero_iff.mp hx_proot
  rw [Polynomial.eval_prod] at hα0
  obtain ⟨β, hβmem, hβ0⟩ := Finset.prod_eq_zero_iff.mp hα0
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hβ0
  obtain ⟨hαdvd, -⟩ := Nat.mem_divisors.mp hαmem
  obtain ⟨hβr, -⟩ := Finset.mem_filter.mp hβmem
  rw [Finset.mem_range] at hβr
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out α hαdvd) with hα1 | hα2
  ·
    -- `α = 1`: the conjugate is `TS K M (ζ ^ (M * β))`, whose `-(M)`-coefficient is a unit,
    -- but any value in the image of `qExpand K p` vanishes there (`p ∤ M`).
    subst hα1
    exfalso
    haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
    have hv1 : qExpand K M (sv K (ζ ^ M) 1 β) = TS K M ((ζ ^ M) ^ (β * 1)) := by
      rw [sv_eq_TS, qExpand_TS]
      exact TS_congr' (by ring) rfl
    obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hx_pS
    have hw2 : qExpand K p w = TS K M ((ζ ^ M) ^ (β * 1)) := by
      rw [hw, hβ0, hv1]
    have hnd : ¬ ((p : ℤ) ∣ (-(M : ℤ))) := by
      rw [dvd_neg, Int.natCast_dvd_natCast]
      exact hpM
    have hz1 : (qExpand K p w).coeff (-(M : ℤ)) = 0 :=
      qExpand_coeff_of_not_dvd (R := K) (N := p) w hnd
    have hz2 : (TS K M ((ζ ^ M) ^ (β * 1))).coeff (-(M : ℤ))
        = ((((ζ ^ M) ^ (β * 1))⁻¹ : Kˣ) : K) :=
      TS_coeff_neg M _
    rw [hw2, hz2] at hz1
    exact Units.ne_zero _ hz1
  ·
    -- `α = p`, `β = 0`: the conjugate is the distinguished slot, and `g'` evaluates to it.
    have hα2' := hα2.symm
    subst hα2'
    have hβ0' : β = 0 := by
      have h3 : p / p = 1 := Nat.div_self hp.out.pos
      omega
    subst hβ0'
    have hsp : qExpand K M (sv K (ζ ^ M) p 0) = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
      rw [sv_eq_TS, qExpand_TS, iota_jqN (M * p) p]
      exact TS_congr' (by ring) (by rw [zero_mul, pow_zero])
    have hx_pval : ψy ⟨jqN p, hmem⟩ = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
      rw [hβ0, hsp]
    have hgE : Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g'
        = (⟨jqN p, hmem⟩ : ℚ⟮jq⟯⟮jqN M⟯) := by
      have h3 := Polynomial.aeval_algHom_apply (IntermediateField.val ℚ⟮jq⟯⟮jqN M⟯)
        (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g'
      refine Subtype.ext ?_
      show ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g' :
        ℚ⟮jq⟯⟮jqN M⟯) : LaurentSeries ℚ) = jqN p
      rw [show ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g' :
        ℚ⟮jq⟯⟮jqN M⟯) : LaurentSeries ℚ)
        = (IntermediateField.val ℚ⟮jq⟯⟮jqN M⟯)
          (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g')
        from rfl, ← h3]
      exact hg'
    rw [← hψy, Polynomial.aeval_algHom_apply, hgE, hx_pval]

/-- **Prime non-membership in the adjoin**: for `p ∤ M` and `hall M`, `jqN p` is not in
`ℚ⟮jq⟯⟮jqN M⟯`. The `ψ(M)` distinct slots of `rval_aux M (ζ ^ p)` are the roots of the
pushed minimal polynomial; `g'` of degree `< ψ(M)` is constant on them
(`eval_map_eq_of_mem_slotValues`), so `jqN p` is the image of a scalar. -/
private theorem jqN_prime_not_mem_adjoin (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) :
    jqN p ∉ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
  classical
  intro hmem
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  set K := CyclotomicField (M * p) ℚ with hK
  have hζ : IsPrimitiveRoot ((cycUnit (M * p) : Kˣ) : K) (M * p) := cycUnit_spec (M * p)
  have hζM : IsPrimitiveRoot (((cycUnit (M * p) : Kˣ) ^ p : Kˣ) : K) M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  obtain ⟨htM, -⟩ := hall M dvd_rfl
  have hα : IsIntegral ℚ⟮jq⟯ (jqN M) := isIntegral_adjoin_jqN htM
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M := natDegree_minpoly_jqN htM
  have hidMB := map_qExpand_minpoly_eq p (show M * p = p * M from Nat.mul_comm M p)
    ((cycUnit (M * p) : Kˣ) ^ p)
    (rval_aux M ((cycUnit (M * p) : Kˣ) ^ p) hζM hall)
  letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
  have halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) :=
    RingHom.algebraMap_toAlgebra _
  have hroots : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp
      (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots
      = slotValues M (fun a b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b)) := by
    rw [hidMB, ← prod_slotValues (K := K)]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hTcard : (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).card = dedekindPsi M :=
    card_slotValues hM0 _ (card_slotFilter_eq_dedekindPsi M hM0)
  have hTnodup : (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).Nodup :=
    nodup_slotValues_qExpand hM0 hζM
  have hscard : (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset.card = dedekindPsi M := by
    rw [Multiset.toFinset_card_of_nodup hTnodup]
    exact hTcard
  obtain ⟨g, hg⟩ : ∃ g : Polynomial ℚ⟮jq⟯, Polynomial.aeval (jqN M) g = jqN p := by
    have h1 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic
    have h2 : jqN p ∈ Algebra.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
      rw [← h1]
      exact hmem
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h2
    obtain ⟨g, hg⟩ := h2
    exact ⟨g, hg⟩
  set g' := g %ₘ (minpoly ℚ⟮jq⟯ (jqN M)) with hg'def
  have hg' : Polynomial.aeval (jqN M) g' = jqN p := by
    have hsplit := Polynomial.modByMonic_add_div g (minpoly ℚ⟮jq⟯ (jqN M))
    have h4 := congrArg (Polynomial.aeval (jqN M)) hsplit
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h4
    rw [hg'def, h4]
    exact hg
  have hdegpos : 0 < (minpoly ℚ⟮jq⟯ (jqN M)).natDegree := by
    rw [hdeg]
    exact dedekindPsi_pos _ hM0
  have hg'deg : g'.natDegree < (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset.card := by
    rw [hscard, ← hdeg]
    rcases eq_or_ne g' 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hdegpos
    · exact Polynomial.natDegree_lt_natDegree h0
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hα))
  have hval : ∀ y ∈ (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset,
      Polynomial.aeval y g' = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
    intro y hy
    exact eval_map_eq_of_mem_slotValues (K := K) hpM hζ hα hroots hmem halg hg'
      (Multiset.mem_toFinset.mp hy)
  obtain ⟨z, hz⟩ := mem_range_of_eval_eq_const g'
    (coeffEmb K (qExpand ℚ (M * p) (jqN p)))
    (slotValues M (fun a b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset
    hg'deg hval
  rw [halg] at hz
  have hzval : (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) z = jqN p := by
    apply RingHom.injective ((coeffEmb K).comp (qExpand ℚ (M * p)))
    exact hz
  have hjpF : jqN p ∈ ℚ⟮jq⟯ := by
    rw [← hzval]
    exact z.2
  have hbot : IntermediateField.adjoin ℚ⟮jq⟯ ({jqN p} : Set (LaurentSeries ℚ))
      = (⊥ : IntermediateField ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
    exact ⟨⟨jqN p, hjpF⟩, rfl⟩
  have h1 : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN p} : Set (LaurentSeries ℚ))) = 1 := by
    rw [hbot]
    exact IntermediateField.finrank_bot
  have h2 := finrank_adjoin_jqN_eq_of_prime p
  rw [h1] at h2
  have h3 := hp.out.two_le
  omega

end NonMem0

/-! ## The public node -/

/-- **Prime non-membership**: `j(q ^ p) ∉ F_M^full` for `p ∤ M`. This is the last
`Inputs` field. Verbatim from
`Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean` (explicit `hall`
conjunction). -/
theorem jqN_prime_not_mem_full (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) :
    jqN p ∉ modularFunctionFieldFull M := by
  intro hmem0
  obtain ⟨-, hgM⟩ := hall M dvd_rfl
  have hmem : jqN p ∈ IntermediateField.adjoin
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      ({jqN M} : Set (LaurentSeries ℚ)) := by
    rw [← hgM] at hmem0
    exact mem_adjoin_jqN_of_mem_mff hmem0
  exact jqN_prime_not_mem_adjoin M p hpM hall hmem

end ModularCurve

end
