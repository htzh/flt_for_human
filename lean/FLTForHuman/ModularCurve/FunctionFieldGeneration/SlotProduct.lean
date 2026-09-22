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
-/
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.NatDivisors
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

/-- The closed form's value function: `(d / gcd a d) * φ (gcd a d)`. -/
private def slotH (x : ℕ × ℕ) : ℕ :=
  (x.2 / Nat.gcd x.1 x.2) * Nat.totient (Nat.gcd x.1 x.2)

/-- A full block of `g * m` consecutive residues contains `m * φ(g)` coprime to
`g`: `Coprime g` is `g`-periodic and each period has `φ(g)` of them. -/
private theorem card_filter_coprime_range_mul (g m : ℕ) :
    ((Finset.range (g * m)).filter (fun b => Nat.Coprime g b)).card = m * Nat.totient g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.count_eq_card_filter_range] at ih ⊢
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.totient_eq_card_coprime]
    refine congrArg Finset.card (Finset.filter_congr (fun k _ => ?_))
    have hper := (Nat.periodic_coprime g).nat_mul m
    rw [Nat.cast_id] at hper
    rw [show g * m + k = k + m * g by ring]
    exact Iff.of_eq (hper k)

/-- The fibre count: `b < d` with `Coprime (gcd a d) b` is `h (a, d)`. -/
private theorem card_fibre (a d : ℕ) :
    ((Finset.range d).filter (fun b => Nat.Coprime (Nat.gcd a d) b)).card = slotH (a, d) := by
  set g := Nat.gcd a d with hg
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  obtain ⟨m, hm⟩ := hgd
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    have hd0 : d = 0 := by rw [hm, hg0, zero_mul]
    simp [slotH, hd0]
  · conv_lhs => rw [hm]
    rw [card_filter_coprime_range_mul, slotH]
    simp only
    rw [← hg, hm, Nat.mul_div_cancel_left m hgpos]

/-- **The closed form**: `slotAt n d = (d / gcd (n/d) d) * φ (gcd (n/d) d)`. -/
private theorem slotAt_eq (n d : ℕ) : slotAt n d = slotH (n / d, d) := by
  unfold slotAt
  rw [Finset.filter_congr (fun b _ => slotCond_iff (n / d) d b)]
  exact card_fibre (n / d) d

/-- Multiplicativity of `slotH` under coprime `(a d)`-products. -/
private theorem slotH_mul (a₁ d₁ a₂ d₂ : ℕ) (hcop : Nat.Coprime (a₁ * d₁) (a₂ * d₂)) :
    slotH (a₁ * a₂, d₁ * d₂) = slotH (a₁, d₁) * slotH (a₂, d₂) := by
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
  simp only [slotH]
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

/-- `ψ (p ^ (j + 1)) = p ^ (j + 1) + p ^ j`, the prime-power form of the public
`Defs/Jq.lean` `dedekindPsi_prime_pow`. -/
private theorem dedekindPsi_prime_pow_succ {p : ℕ} (hp : p.Prime) (j : ℕ) :
    dedekindPsi (p ^ (j + 1)) = p ^ (j + 1) + p ^ j := by
  rw [dedekindPsi_prime_pow p (j + 1) hp (Nat.succ_ne_zero j)]
  simp

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
  exact slotH_mul (M / d₁) d₁ (M' / d₂) d₂
    (by rw [Nat.div_mul_cancel (Nat.mem_divisors.mp hd₁).1,
            Nat.div_mul_cancel (Nat.mem_divisors.mp hd₂).1]; exact hco)

private theorem slots_eq_dedekindPsi : ∀ n : ℕ, n ≠ 0 → slots n = dedekindPsi n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [slots_prime_pow hp j, dedekindPsi_prime_pow_succ hp j]
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
    sv K ζ a b = TS K (a * a) (ζ ^ (b * a)) :=
  sv_eq ζ a b

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

/-! ## The slot product `rval_aux`

The strong induction on `M`: the `ψ(M)` values `sv K ζ a b` are exactly the roots
of the mapped minimal polynomial. Transcribed from the pin; the closed-form slot
count and the public `ψ` lemmas are the only route changes. -/

section RValCore

/-- The prime-power step of `ψ` when `p` divides `m`. -/
private theorem dedekindPsi_mul_prime_dvd {m p : ℕ} [NeZero m] (hp : p.Prime) (hpm : p ∣ m) :
    dedekindPsi (m * p) = dedekindPsi m * p := by
  rw [dedekindPsi_mul_prime m p hp, ite_eq_left hpm, mul_comm]

/-- The prime-power step of `ψ` when `p` does not divide `m`. -/
private theorem dedekindPsi_mul_prime_not_dvd {m p : ℕ} [NeZero m] (hp : p.Prime)
    (hpm : ¬ p ∣ m) : dedekindPsi (m * p) = dedekindPsi m * (p + 1) := by
  rw [dedekindPsi_mul_prime m p hp, ite_eq_right hpm, mul_comm]

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
  have hM0 : M ≠ 0 := NeZero.ne M

  have hslot_root : ∀ a b : ℕ, a ∈ M.divisors →
      b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) →
      ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot (sv K ζ a b) := by
    intro a b ha hb
    obtain ⟨haM, -⟩ := Nat.mem_divisors.mp ha
    obtain ⟨hbr, hbc⟩ := Finset.mem_filter.mp hb
    rw [Finset.mem_range] at hbr
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hM0 (Nat.eq_zero_of_zero_dvd haM)
    haveI : NeZero a := ⟨ha0⟩
    have had : a * (M / a) = M := Nat.mul_div_cancel' haM
    by_cases hd1 : M / a = 1
    ·
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
    ·
      have hd0 : M / a ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at had
        exact hM0 had.symm
      have hpp : (M / a).minFac.Prime := Nat.minFac_prime hd1
      haveI : Fact (M / a).minFac.Prime := ⟨hpp⟩
      haveI : NeZero (M / a).minFac := ⟨hpp.ne_zero⟩
      obtain ⟨d'', hdd⟩ : (M / a).minFac ∣ M / a := Nat.minFac_dvd _
      set p := (M / a).minFac with hp_def
      have hd''0 : d'' ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hdd
        exact hd0 hdd
      haveI : NeZero d'' := ⟨hd''0⟩
      have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero ha0 hd''0
      haveI : NeZero (a * d'') := ⟨hM'0⟩
      have hMM' : M = a * d'' * p := by rw [← had, hdd]; ring
      have hM'M : a * d'' ∣ M := ⟨p, hMM'⟩
      have hM'lt : a * d'' < M := by
        calc a * d'' = a * d'' * 1 := by ring
          _ < a * d'' * p :=
              (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hM'0)).mpr hpp.one_lt
          _ = M := hMM'.symm
      have hpM : p ∣ M := by
        have hpd : p ∣ M / a := ⟨d'', hdd⟩
        exact hpd.trans (Nat.div_dvd_of_dvd haM)

      have hb''lt : b % d'' < d'' := Nat.mod_lt b (Nat.pos_of_ne_zero hd''0)
      have hbsplit : b % d'' + b / d'' * d'' = b := Nat.mod_add_div' b d''
      have hc₀p : b / d'' < p := by
        have h1 : b < d'' * p := by rw [Nat.mul_comm d'' p, ← hdd]; exact hbr
        exact Nat.div_lt_of_lt_mul h1
      have hprim' : Nat.gcd (Nat.gcd a (b % d'')) d'' = 1 := by
        have h1 : Nat.gcd (Nat.gcd a (b % d'')) d'' ∣ Nat.gcd (Nat.gcd a b) (M / a) := by
          refine Nat.dvd_gcd (Nat.dvd_gcd ?_ ?_) ?_
          · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a (b % d''))
          · have hgb'' : Nat.gcd (Nat.gcd a (b % d'')) d'' ∣ b % d'' :=
              (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a (b % d''))
            have hgd'' : Nat.gcd (Nat.gcd a (b % d'')) d'' ∣ d'' := Nat.gcd_dvd_right _ _
            have h2 : Nat.gcd (Nat.gcd a (b % d'')) d'' ∣ b % d'' + b / d'' * d'' :=
              Nat.dvd_add hgb'' (hgd''.mul_left _)
            rwa [hbsplit] at h2
          · rw [hdd]
            exact (Nat.gcd_dvd_right _ _).mul_left p
        rw [hbc] at h1
        exact Nat.dvd_one.mp h1

      have hζ' : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) (a * d'') := by
        have h1 := isPrimitiveRoot_pow_div hζ hM'M
        have h2 : M / (a * d'') = p := by
          rw [hMM']
          exact Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM'0)
        rwa [h2] at h1

      have hIH := IH (a * d'') hM'lt (ζ ^ p) hζ' (fun e he _ => hall e (he.trans hM'M))
      have hIHM := map_qExpand_minpoly_eq p (show M = p * (a * d'') from by rw [hMM']; ring)
        (ζ ^ p) hIH
      have hroot' : ((minpoly ℚ⟮jq⟯ (jqN (a * d''))).map (((coeffEmb K).comp
          (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
          (qExpand K p (sv K (ζ ^ p) a (b % d''))) := by
        rw [hIHM, Polynomial.IsRoot, Polynomial.eval_prod]
        refine Finset.prod_eq_zero (Nat.mem_divisors.mpr ⟨⟨d'', rfl⟩, hM'0⟩) ?_
        rw [Polynomial.eval_prod]
        have hM'a : a * d'' / a = d'' := Nat.mul_div_cancel_left d'' (Nat.pos_of_ne_zero ha0)
        refine Finset.prod_eq_zero (i := b % d'') ?_ ?_
        · rw [hM'a]
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb''lt, hprim'⟩
        · rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

      letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
        (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
      have halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
          = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) :=
        RingHom.algebraMap_toAlgebra _
      obtain ⟨htM', hgM'⟩ := hall (a * d'') hM'M
      haveI hfd' : FiniteDimensional ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (a * d'')} : Set (LaurentSeries ℚ))) :=
        FiniteDimensional.of_finrank_pos (htM' ▸ dedekindPsi_pos _ hM'0)
      have hα' : IsIntegral ℚ⟮jq⟯ (jqN (a * d'')) :=
        IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite ℚ⟮jq⟯
          (⟨jqN (a * d''), IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl⟩ :
            IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (a * d'')} : Set (LaurentSeries ℚ))))
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

      obtain ⟨dp, hdpirr, hdpsym⟩ := exists_phiIrreducible_evalSymm p
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

      haveI : Module.Free ℚ⟮jq⟯⟮jqN (a * d'')⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯ :=
        Module.Free.of_divisionRing _ _
      have htow := Module.finrank_mul_finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯
        ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯
      have habs : IntermediateField.adjoin ℚ⟮jq⟯
          (({jqN (a * d'')} : Set (LaurentSeries ℚ)) ∪ {jqN M})
          = IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
        obtain ⟨-, hgM⟩ := hall M dvd_rfl
        refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
          (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
        rintro z (hz | hz)
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          have h1 : jqN (a * d'') ∈ modularFunctionFieldFull M := jqd_mem_full M hM'M
          rw [← hgM] at h1
          exact mem_adjoin_jqN_of_mem_mff h1
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          exact IntermediateField.subset_adjoin _ _ rfl
      have htop : Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯ = dedekindPsi M := by
        obtain ⟨htM, -⟩ := hall M dvd_rfl
        have h1 := IntermediateField.adjoin_adjoin_left ℚ⟮jq⟯
          ({jqN (a * d'')} : Set (LaurentSeries ℚ)) {jqN M}
        have h2 : Module.finrank ℚ⟮jq⟯
            (IntermediateField.restrictScalars ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯)
            = Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯ := rfl
        rw [← h2, h1, habs]
        exact htM
      have hstep_deg : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯
          * dedekindPsi (a * d'') = dedekindPsi M := by
        rw [← htM', ← htop, Nat.mul_comm]
        exact htow

      have hseed : qExpand K p (sv K (ζ ^ p) a (b % d''))
          = qExpand K (p * (a * a)) (qTwist ((ζ ^ (b % d'' * a)) ^ p) (coeffEmb K jq)) := by
        rw [sv_eq_TS, qExpand_TS]
        show TS K (p * (a * a)) ((ζ ^ p) ^ (b % d'' * a))
          = TS K (p * (a * a)) ((ζ ^ (b % d'' * a)) ^ p)
        exact TS_congr' rfl (by rw [← pow_mul, ← pow_mul, Nat.mul_comm])
      have hC5 := PhiGen.splits_prime_at_slot M ζ hζ p hpM dp (a * a)
        (ζ ^ (b % d'' * a))
      have hΦfact : phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))
          = (Polynomial.X - Polynomial.C (qExpand K (p * (p * (a * a)))
              (qTwist ((ζ ^ (b % d'' * a)) ^ (p * p)) (coeffEmb K jq))))
            * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K (a * a)
              (qTwist (ζ ^ (b % d'' * a) * ζ ^ (c * (M / p))) (coeffEmb K jq)))) := by
        rw [hseed]
        exact hC5
      have hMp : M / p = a * d'' := by
        rw [hMM']
        exact Nat.mul_div_cancel _ hpp.pos
      have htarget : qExpand K (a * a) (qTwist (ζ ^ (b % d'' * a) * ζ ^ (b / d'' * (M / p)))
          (coeffEmb K jq)) = sv K ζ a b := by
        rw [sv_eq]
        show TS K (a * a) (ζ ^ (b % d'' * a) * ζ ^ (b / d'' * (M / p)))
          = TS K (a * a) (ζ ^ (b * a))
        refine TS_congr' rfl ?_
        rw [hMp, ← pow_add]
        congr 1
        rw [show b % d'' * a + b / d'' * (a * d'')
          = (b % d'' + b / d'' * d'') * a from by ring, hbsplit]

      by_cases hpM' : p ∣ a * d''
      ·
        have hψM : dedekindPsi M = dedekindPsi (a * d'') * p := by
          rw [hMM']
          exact dedekindPsi_mul_prime_dvd hpp hpM'
        have he : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯ = p := by
          have h1 : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯
              * dedekindPsi (a * d'') = p * dedekindPsi (a * d'') := by
            rw [hstep_deg, hψM]
            ring
          exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos _ hM'0) h1

        obtain ⟨m'', hm''⟩ := hpM'
        have hm''0 : m'' ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm''
          exact hM'0 hm''
        haveI : NeZero m'' := ⟨hm''0⟩
        have hm''M : m'' ∣ M := ⟨p * p, by rw [hMM', hm'']; ring⟩
        have hm''lt : m'' < M := by
          calc m'' ≤ a * d'' := by rw [hm'']; exact Nat.le_mul_of_pos_left m'' hpp.pos
            _ < M := hM'lt
        have hdown : (phiAtSeed dp (jqN (a * d''))).eval (jqN m'') = 0 := by
          rw [phiAtSeed_eval_symm dp hdpsym]
          have h1 := phiAtSeed_jqN_eval p dp m''
          rwa [show jqN (m'' * p) = jqN (a * d'') from jqN_congr (by rw [hm'']; ring)] at h1
        have hmem'' : jqN m'' ∈ ℚ⟮jq⟯⟮jqN (a * d'')⟯ := by
          have h1 : jqN m'' ∈ modularFunctionFieldFull (a * d'') :=
            jqd_mem_full (a * d'') ⟨p, by rw [hm'']; ring⟩
          rw [← hgM'] at h1
          exact mem_adjoin_jqN_of_mem_mff h1
        have hdownF₁ : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯
            (jqN (a * d'')))).eval (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) = 0 :=
          phiAtSeed_eval_of_injective dp _ _
            (algebraMap ℚ⟮jq⟯⟮jqN (a * d'')⟯ (LaurentSeries ℚ)) (RingHom.injective _) hdown
        have hψx'' : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
            (ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)) := by
          have h1 := phiAtSeed_eval_map dp _ _
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K) hdownF₁
          rw [show (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
            = qExpand K p (sv K (ζ ^ p) a (b % d'')) from hψ₁] at h1
          exact h1
        have hx''notmin : ¬ (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).IsRoot
            (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) := by
          intro hcon
          obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hcon
          have hirr := minpoly.irreducible hα₁
          rcases hirr.isUnit_or_isUnit hq with hu | hu
          · exact Polynomial.not_isUnit_X_sub_C _ hu
          · have hq0 : q ≠ 0 := by
              rintro rfl
              rw [mul_zero] at hq
              exact minpoly.ne_zero hα₁ hq
            have hdm : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).natDegree = 1 := by
              rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
                Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu]
            have hdm' : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).natDegree = p := by
              rw [← IntermediateField.adjoin.finrank hα₁]
              exact he
            rw [hdm] at hdm'
            exact (Nat.ne_of_lt hpp.one_lt) hdm'
        have hψx''notmin : ¬ ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)).IsRoot
            (ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)) := by
          intro hcon
          refine hx''notmin ?_
          rw [Polynomial.IsRoot, Polynomial.eval_map,
            show ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)
              = (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
                (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) from rfl,
            Polynomial.eval₂_hom] at hcon
          exact (injective_iff_map_eq_zero _).mp
            (RingHom.injective (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)) _ hcon

        have htarget_ne : sv K ζ a b ≠ ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) := by
          intro hcon
          have hroot'' : ((minpoly ℚ⟮jq⟯ (jqN m'')).map (((coeffEmb K).comp
              (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
              (ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)) := by
            have h1 : Polynomial.aeval (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯)
                (minpoly ℚ⟮jq⟯ (jqN m'')) = 0 := by
              refine aeval_intermediateField_eq_zero ?_
              show Polynomial.aeval (jqN m'') (minpoly ℚ⟮jq⟯ (jqN m'')) = 0
              exact minpoly.aeval _ _
            have h2 := Polynomial.aeval_algHom_apply ψ₁
              (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) (minpoly ℚ⟮jq⟯ (jqN m''))
            rw [h1, map_zero] at h2
            rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map] at h2
            exact h2
          have hζ'' : IsPrimitiveRoot ((ζ ^ (p * p) : Kˣ) : K) m'' := by
            have h1 := isPrimitiveRoot_pow_div hζ hm''M
            have h2 : M / m'' = p * p := by
              rw [hMM', hm'', show p * m'' * p = m'' * (p * p) from by ring]
              exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm''0)
            rwa [h2] at h1
          have hIH'' := IH m'' hm''lt (ζ ^ (p * p)) hζ''
            (fun e he'' _ => hall e (he''.trans hm''M))
          have hIHM'' := map_qExpand_minpoly_eq (p * p)
            (show M = p * p * m'' from by rw [hMM', hm'']; ring) (ζ ^ (p * p)) hIH''
          rw [hIHM''] at hroot''
          rw [Polynomial.IsRoot, Polynomial.eval_prod] at hroot''
          obtain ⟨α, hαmem, hα0⟩ := Finset.prod_eq_zero_iff.mp hroot''
          rw [Polynomial.eval_prod] at hα0
          obtain ⟨β, hβmem, hβ0⟩ := Finset.prod_eq_zero_iff.mp hα0
          rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hβ0
          obtain ⟨hαdvd, -⟩ := Nat.mem_divisors.mp hαmem
          obtain ⟨hβr, -⟩ := Finset.mem_filter.mp hβmem
          rw [Finset.mem_range] at hβr
          have hα0' : α ≠ 0 := by
            rintro rfl
            exact hm''0 (Nat.eq_zero_of_zero_dvd hαdvd)
          haveI : NeZero α := ⟨hα0'⟩
          have hcoll : TS K (a * a) (ζ ^ (b * a))
              = TS K (p * p * (α * α)) (ζ ^ (p * p * (β * α))) := by
            calc TS K (a * a) (ζ ^ (b * a)) = sv K ζ a b := (sv_eq_TS ζ a b).symm
              _ = ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯) := hcon
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
                (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr
              _ = M := by rw [Nat.mul_comm] at had; exact had
          have hppβα : p * p * (β * α) < M := by
            have h1 : β * α < m'' := by
              calc β * α < m'' / α * α :=
                  (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hα0')).mpr hβr
                _ ≤ m'' := Nat.div_mul_le_self m'' α
            calc p * p * (β * α) < p * p * m'' :=
                (Nat.mul_lt_mul_left (Nat.mul_pos hpp.pos hpp.pos)).mpr h1
              _ = M := by rw [hMM', hm'']; ring
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

        have hQ : (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
            ℚ⟮jq⟯⟮jqN (a * d'')⟯))) * (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
            (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯))))
            = phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) :=
          Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hψx''
        have hΦmonic : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).Monic :=
          phiAtSeed_monic dp _
        have hQmonic : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
            (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
              ℚ⟮jq⟯⟮jqN (a * d'')⟯)))).Monic :=
          Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C _)
            (by rw [hQ]; exact hΦmonic)
        have hΦdeg : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).natDegree
            = p + 1 := by
          rw [phiAtSeed_natDegree]
          exact dedekindPsi_prime hpp
        have hQdeg : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
            (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
              ℚ⟮jq⟯⟮jqN (a * d'')⟯)))).natDegree = p := by
          have h1 : p + 1 = 1 + (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
              (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
                ℚ⟮jq⟯⟮jqN (a * d'')⟯)))).natDegree := by
            rw [← hΦdeg]
            conv_lhs => rw [← hQ]
            rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hQmonic.ne_zero,
              Polynomial.natDegree_X_sub_C]
          omega
        have hP₁dvd : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            ∣ phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) := by
          have h1 := Polynomial.map_dvd (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K) hmindvd
          rwa [phiAtSeed_map, show (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
            = qExpand K p (sv K (ζ ^ p) a (b % d'')) from hψ₁] at h1
        have hcop : IsCoprime (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
            ℚ⟮jq⟯⟮jqN (a * d'')⟯)))
            ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
              (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)) := by
          rw [(Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd]
          intro hcon
          exact hψx''notmin (Polynomial.dvd_iff_isRoot.mp hcon)
        have hP₁dvdQ : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            ∣ phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
              (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
                ℚ⟮jq⟯⟮jqN (a * d'')⟯))) := by
          have h1 := hP₁dvd
          rw [← hQ] at h1
          exact (hcop.symm).dvd_of_dvd_mul_left h1
        have hdeg₁ : ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)).natDegree = p := by
          rw [Polynomial.Monic.natDegree_map (minpoly.monic hα₁),
            ← IntermediateField.adjoin.finrank hα₁]
          exact he
        have hmineqQ : (minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            = phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
              (Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
                ℚ⟮jq⟯⟮jqN (a * d'')⟯))) :=
          Polynomial.eq_of_monic_of_dvd_of_natDegree_le ((minpoly.monic hα₁).map _)
            hQmonic hP₁dvdQ (le_of_eq (hQdeg.trans hdeg₁.symm)) |>.symm
        have htargetΦ : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
            (sv K ζ a b) := by
          rw [hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
          refine mul_eq_zero.mpr (Or.inr ?_)
          rw [Polynomial.eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
          rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
        have hroot_step : ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)).IsRoot (sv K ζ a b) := by
          rw [hmineqQ, Polynomial.IsRoot]
          have h1 : ((Polynomial.X - Polynomial.C (ψ₁ (⟨jqN m'', hmem''⟩ :
              ℚ⟮jq⟯⟮jqN (a * d'')⟯))) * (phiAtSeed dp (qExpand K p
              (sv K (ζ ^ p) a (b % d''))) /ₘ (Polynomial.X - Polynomial.C
              (ψ₁ (⟨jqN m'', hmem''⟩ : ℚ⟮jq⟯⟮jqN (a * d'')⟯))))).eval (sv K ζ a b) = 0 := by
            rw [hQ]
            exact htargetΦ
          rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C] at h1
          rcases mul_eq_zero.mp h1 with h2 | h2
          · exact absurd (sub_eq_zero.mp h2) htarget_ne
          · exact h2

        have htowdvd : minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
            ∣ (minpoly ℚ⟮jq⟯ (jqN M)).map (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯) :=
          minpoly.dvd_map_of_isScalarTower ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
        have h1 := Polynomial.map_dvd (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K) htowdvd
        rw [Polynomial.map_map] at h1
        have h2 : (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K).comp
            (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯)
            = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
          rw [AlgHom.comp_algebraMap]
          exact halg
        rw [h2] at h1
        exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h1 hroot_step
      ·
        have hψM : dedekindPsi M = dedekindPsi (a * d'') * (p + 1) := by
          rw [hMM']
          exact dedekindPsi_mul_prime_not_dvd hpp hpM'
        have he : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯
            = p + 1 := by
          have h1 : Module.finrank ℚ⟮jq⟯⟮jqN (a * d'')⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯⟮jqN M⟯
              * dedekindPsi (a * d'') = (p + 1) * dedekindPsi (a * d'') := by
            rw [hstep_deg, hψM]
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
        have hroot_step : ((minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)).map
            (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)).IsRoot (sv K ζ a b) := by
          rw [hmineq, phiAtSeed_map, show (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K)
            (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN (a * d'')))
            = qExpand K p (sv K (ζ ^ p) a (b % d'')) from hψ₁]
          rw [hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
          refine mul_eq_zero.mpr (Or.inr ?_)
          rw [Polynomial.eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
          rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
        have htowdvd : minpoly ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
            ∣ (minpoly ℚ⟮jq⟯ (jqN M)).map (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯) :=
          minpoly.dvd_map_of_isScalarTower ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯ (jqN M)
        have h1 := Polynomial.map_dvd (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K) htowdvd
        rw [Polynomial.map_map] at h1
        have h2 : (ψ₁ : ℚ⟮jq⟯⟮jqN (a * d'')⟯ →+* LaurentSeries K).comp
            (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN (a * d'')⟯)
            = ((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
          rw [AlgHom.comp_algebraMap]
          exact halg
        rw [h2] at h1
        exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h1 hroot_step

  by_cases hM1 : M = 1
  · subst hM1
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
      rw [h3, TS, qTwist_one_apply, qExpand_one_apply]
    rw [h2]
  · obtain ⟨htM, -⟩ := hall M dvd_rfl
    haveI hfd : FiniteDimensional ℚ⟮jq⟯
        (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) :=
      FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ hM0)
    have hα : IsIntegral ℚ⟮jq⟯ (jqN M) :=
      IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite ℚ⟮jq⟯
        (⟨jqN M, IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl⟩ :
          IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))))
    have hdeg : (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M := by
      rw [← IntermediateField.adjoin.finrank hα]
      exact htM

    set T : Multiset (LaurentSeries K) := M.divisors.val.bind
      (fun a => ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map (fun b => sv K ζ a b)) with hT
    have hTcard : Multiset.card T = dedekindPsi M := by
      rw [hT, Multiset.card_bind]
      have h2 : M.divisors.val.map (Multiset.card ∘ fun a => (((Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map (fun b => sv K ζ a b)))
          = M.divisors.val.map (fun a => slotAt M (M / a)) := by
        refine Multiset.map_congr rfl ?_
        intro a ha
        show Multiset.card (((Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map (fun b => sv K ζ a b))
          = slotAt M (M / a)
        rw [Multiset.card_map]
        show ((Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card = slotAt M (M / a)
        unfold slotAt
        rw [Nat.div_div_self (Nat.mem_divisors.mp (Finset.mem_val.mp ha)).1 hM0]
      rw [h2]
      show (∑ a ∈ M.divisors, slotAt M (M / a)) = dedekindPsi M
      rw [Nat.sum_div_divisors M (slotAt M)]
      exact slots_eq_dedekindPsi M hM0
    have hmem_unpack : ∀ x ∈ T, ∃ a b : ℕ, a ∈ M.divisors ∧
        b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) ∧
        x = sv K ζ a b := by
      intro x hx
      rw [hT, Multiset.mem_bind] at hx
      obtain ⟨a, ha, hx2⟩ := hx
      rw [Multiset.mem_map] at hx2
      obtain ⟨b, hb, rfl⟩ := hx2
      exact ⟨a, b, ha, hb, rfl⟩
    have hTnodup : T.Nodup := by
      rw [hT]
      rw [Multiset.nodup_bind]
      constructor
      · intro a ha
        refine Multiset.Nodup.map_on ?_ (Finset.filter _ _).nodup
        intro b hb b' hb' hvv
        have ha0 : a ≠ 0 := by
          rintro rfl
          exact hM0 (Nat.eq_zero_of_zero_dvd (Nat.mem_divisors.mp (by exact ha)).1)
        have hbr := Finset.mem_range.mp (Finset.mem_filter.mp (by exact hb)).1
        have hbr' := Finset.mem_range.mp (Finset.mem_filter.mp (by exact hb')).1
        have haM := (Nat.mem_divisors.mp (by exact ha)).1
        have had : M / a * a = M := Nat.div_mul_cancel haM
        have hba : b * a < M := by
          calc b * a < M / a * a :=
              (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr
            _ = M := had
        have hba' : b' * a < M := by
          calc b' * a < M / a * a :=
              (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr'
            _ = M := had
        exact (sv_inj hζ ha0 ha0 hba hba' hvv).2
      ·
        refine Multiset.Nodup.pairwise ?_ M.divisors.nodup
        intro a ha a' ha' hne
        show Disjoint (((Finset.range (M / a)).filter
            (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map (fun b => sv K ζ a b))
          (((Finset.range (M / a')).filter
            (fun b => Nat.gcd (Nat.gcd a' b) (M / a') = 1)).val.map (fun b => sv K ζ a' b))
        rw [Multiset.disjoint_left]
        intro x hx hx'
        rw [Multiset.mem_map] at hx hx'
        obtain ⟨b, hb, hxb⟩ := hx
        obtain ⟨b', hb', hxb'⟩ := hx'
        have haM := (Nat.mem_divisors.mp (Finset.mem_val.mp ha)).1
        have haM' := (Nat.mem_divisors.mp (Finset.mem_val.mp ha')).1
        have ha0 : a ≠ 0 := by
          rintro rfl
          exact hM0 (Nat.eq_zero_of_zero_dvd haM)
        have ha0' : a' ≠ 0 := by
          rintro rfl
          exact hM0 (Nat.eq_zero_of_zero_dvd haM')
        have hbr := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb)).1
        have hbr' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb')).1
        have hba : b * a < M := by
          calc b * a < M / a * a :=
              (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr
            _ = M := Nat.div_mul_cancel haM
        have hba' : b' * a' < M := by
          calc b' * a' < M / a' * a' :=
              (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0')).mpr hbr'
            _ = M := Nat.div_mul_cancel haM'
        have hvv : sv K ζ a b = sv K ζ a' b' := by rw [hxb, ← hxb']
        exact hne (sv_inj hζ ha0 ha0' hba hba' hvv).1

    have hPne : (minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) ≠ 0 :=
      ((minpoly.monic hα).map _).ne_zero
    have hPdeg : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).natDegree = dedekindPsi M := by
      rw [Polynomial.Monic.natDegree_map (minpoly.monic hα)]
      exact hdeg
    have hTle : T ≤ ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ T
      · have h1 : Multiset.count x T ≤ 1 := Multiset.nodup_iff_count_le_one.mp hTnodup x
        have h2 : 1 ≤ Multiset.count x (((minpoly ℚ⟮jq⟯ (jqN M)).map
            (((coeffEmb K).comp (qExpand ℚ M)).comp
              (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots) := by
          rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots']
          obtain ⟨a, b, ha, hb, rfl⟩ := hmem_unpack x hx
          exact ⟨hPne, hslot_root a b ha hb⟩
        omega
      · rw [Multiset.count_eq_zero.mpr hx]
        exact Nat.zero_le _
    have hroots_eq : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots = T := by
      refine (Multiset.eq_of_le_of_card_le hTle ?_).symm
      rw [hTcard]
      calc Multiset.card (((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp
            (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots)
          ≤ ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp
            (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).natDegree := Polynomial.card_roots' _
        _ = dedekindPsi M := hPdeg
    have hsp : Polynomial.Splits ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp
        (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) := by
      rw [Polynomial.splits_iff_card_roots, hroots_eq, hTcard, hPdeg]
    have hfact := hsp.eq_prod_roots_of_monic ((minpoly.monic hα).map _)
    rw [hfact, hroots_eq, hT, Multiset.map_bind, Multiset.prod_bind]
    show (M.divisors.val.map fun a => ((((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
        (fun b => sv K ζ a b)).map (fun r => Polynomial.X - Polynomial.C r)).prod).prod
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b))
    simp only [Multiset.map_map, Function.comp]
    rfl

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


/-! ## The M-arbitrary non-membership

`j(q ^ p) ∉ F_M^full` for `p ∤ M`, from `Hall M`. The `hallp` at `d = p` uses
T18's `gen_prime` (and `tight_one`/`gen_one` at `d = 1`) instead of the pin's
`functionFieldGeneration_of_squarefree p`, so no squarefree-block declaration is
pulled in; `mem_range_of_eval_eq_const` is T4's engine from
`FieldTheory/CommonRoot.lean`, not restated. -/

section NonMem0

open IntermediateField

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
  have hζp : IsPrimitiveRoot (((cycUnit (M * p) : Kˣ) ^ M : Kˣ) : K) p := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨M, Nat.mul_comm M p⟩ : p ∣ M * p)
    have h2 : M * p / p = M := Nat.mul_div_cancel M (Nat.pos_of_ne_zero hp0)
    rwa [h2] at h1

  obtain ⟨htM, -⟩ := hall M dvd_rfl
  haveI hfd : FiniteDimensional ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ hM0)
  have hα : IsIntegral ℚ⟮jq⟯ (jqN M) :=
    IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite ℚ⟮jq⟯
      (⟨jqN M, IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl⟩ :
        IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))))
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M := by
    rw [← IntermediateField.adjoin.finrank hα]
    exact htM

  have hallp : ∀ d : ℕ, d ∣ p → ∀ [NeZero d],
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

  have hidMB := map_qExpand_minpoly_eq p (show M * p = p * M from Nat.mul_comm M p)
    ((cycUnit (M * p) : Kˣ) ^ p)
    (rval_aux M ((cycUnit (M * p) : Kˣ) ^ p) hζM hall)
  have hidpB := map_qExpand_minpoly_eq M rfl ((cycUnit (M * p) : Kˣ) ^ M)
    (rval_aux p ((cycUnit (M * p) : Kˣ) ^ M) hζp hallp)

  letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
  have halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) :=
    RingHom.algebraMap_toAlgebra _

  have hιS : ∀ w : LaurentSeries ℚ, coeffEmb K (qExpand ℚ (M * p) w)
      = qExpand K p (coeffEmb K (qExpand ℚ M w)) := by
    intro w
    rw [← coeffEmb_qExpand, qExpand_qExpand]
    exact congrArg (coeffEmb K) (qExpand_congr (Nat.mul_comm M p) w)

  set T' : Multiset (LaurentSeries K) := M.divisors.val.bind
    (fun a => ((Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
      (fun b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))) with hT'
  have hT'card : Multiset.card T' = dedekindPsi M := by
    rw [hT', Multiset.card_bind]
    have h2 : M.divisors.val.map (Multiset.card ∘ fun a => (((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
        (fun b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))))
        = M.divisors.val.map (fun a => slotAt M (M / a)) := by
      refine Multiset.map_congr rfl ?_
      intro a ha
      show Multiset.card (((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
        (fun b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b)))
        = slotAt M (M / a)
      rw [Multiset.card_map]
      show ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card = slotAt M (M / a)
      unfold slotAt
      rw [Nat.div_div_self (Nat.mem_divisors.mp (Finset.mem_val.mp ha)).1 hM0]
    rw [h2]
    show (∑ a ∈ M.divisors, slotAt M (M / a)) = dedekindPsi M
    rw [Nat.sum_div_divisors M (slotAt M)]
    exact slots_eq_dedekindPsi M hM0
  have hT'nodup : T'.Nodup := by
    rw [hT', Multiset.nodup_bind]
    constructor
    · intro a ha
      refine Multiset.Nodup.map_on ?_ (Finset.filter _ _).nodup
      intro b hb b' hb' hvv
      have haM := (Nat.mem_divisors.mp (Finset.mem_val.mp ha)).1
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hM0 (Nat.eq_zero_of_zero_dvd haM)
      have hbr := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb)).1
      have hbr' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb')).1
      have hba : b * a < M := by
        calc b * a < M / a * a :=
            (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr
          _ = M := Nat.div_mul_cancel haM
      have hba' : b' * a < M := by
        calc b' * a < M / a * a :=
            (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr'
          _ = M := Nat.div_mul_cancel haM
      have hsv : sv K ((cycUnit (M * p) : Kˣ) ^ p) a b
          = sv K ((cycUnit (M * p) : Kˣ) ^ p) a b' :=
        RingHom.injective (qExpand K p) hvv
      exact (sv_inj hζM ha0 ha0 hba hba' hsv).2
    · refine Multiset.Nodup.pairwise ?_ M.divisors.nodup
      intro a ha a' ha' hne
      show Disjoint (((Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
          (fun b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b)))
        (((Finset.range (M / a')).filter
          (fun b => Nat.gcd (Nat.gcd a' b) (M / a') = 1)).val.map
          (fun b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a' b)))
      rw [Multiset.disjoint_left]
      intro x hx hx'
      rw [Multiset.mem_map] at hx hx'
      obtain ⟨b, hb, hxb⟩ := hx
      obtain ⟨b', hb', hxb'⟩ := hx'
      have haM := (Nat.mem_divisors.mp (Finset.mem_val.mp ha)).1
      have haM' := (Nat.mem_divisors.mp (Finset.mem_val.mp ha')).1
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hM0 (Nat.eq_zero_of_zero_dvd haM)
      have ha0' : a' ≠ 0 := by
        rintro rfl
        exact hM0 (Nat.eq_zero_of_zero_dvd haM')
      have hbr := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb)).1
      have hbr' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb')).1
      have hba : b * a < M := by
        calc b * a < M / a * a :=
            (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hbr
          _ = M := Nat.div_mul_cancel haM
      have hba' : b' * a' < M := by
        calc b' * a' < M / a' * a' :=
            (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0')).mpr hbr'
          _ = M := Nat.div_mul_cancel haM'
      have hvv : qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b)
          = qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a' b') := by
        rw [hxb, ← hxb']
      exact hne (sv_inj hζM ha0 ha0' hba hba'
        (RingHom.injective (qExpand K p) hvv)).1

  have hglue : ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
      (Polynomial.X - Polynomial.C (qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b)))
      = (T'.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
    rw [hT', Multiset.map_bind, Multiset.prod_bind]
    show (∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
        (Polynomial.X - Polynomial.C (qExpand K p
          (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))))
      = (M.divisors.val.map fun a => ((((Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
          (fun b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).map
          (fun r => Polynomial.X - Polynomial.C r)).prod).prod
    simp only [Multiset.map_map, Function.comp]
    rfl
  have hroots : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp
      (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots = T' := by
    rw [hidMB, hglue]
    exact Polynomial.roots_multiset_prod_X_sub_C T'

  set s : Finset (LaurentSeries K) := T'.toFinset with hs
  have hscard : s.card = dedekindPsi M := by
    rw [hs, Multiset.toFinset_card_of_nodup hT'nodup]
    exact hT'card

  obtain ⟨g, hg⟩ : ∃ g : Polynomial ℚ⟮jq⟯, Polynomial.aeval (jqN M) g = jqN p := by
    have h1 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      hα.isAlgebraic
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
  have hg'deg : g'.natDegree < s.card := by
    rw [hscard, ← hdeg]
    rcases eq_or_ne g' 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hdegpos
    · exact Polynomial.natDegree_lt_natDegree h0
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hα))

  have hval : ∀ y ∈ s, Polynomial.aeval y g'
      = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
    intro y hy
    have hyT' : y ∈ T' := Multiset.mem_toFinset.mp hy
    obtain ⟨a₀, ha₀, hy2⟩ := Multiset.mem_bind.mp hyT'
    obtain ⟨b₀, hb₀, hyval⟩ := Multiset.mem_map.mp hy2
    have hyS : y ∈ (qExpand K p).fieldRange := by
      rw [← hyval]
      exact RingHom.mem_fieldRange.mpr ⟨sv K ((cycUnit (M * p) : Kˣ) ^ p) a₀ b₀, rfl⟩

    have hy_ar : y ∈ (minpoly ℚ⟮jq⟯ (jqN M)).aroots (LaurentSeries K) := by
      rw [Polynomial.aroots_def, halg, hroots]
      exact hyT'
    obtain ⟨ψy, hψy⟩ : ∃ ψy : ℚ⟮jq⟯⟮jqN M⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K,
        ψy (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) = y :=
      ⟨(IntermediateField.algHomAdjoinIntegralEquiv ℚ⟮jq⟯ hα).symm ⟨y, hy_ar⟩,
        IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ⟮jq⟯ hα ⟨y, hy_ar⟩⟩

    have hψgen : ∀ h : jqN M ∈ IntermediateField.adjoin ℚ⟮jq⟯
        ({jqN M} : Set (LaurentSeries ℚ)), ψy ⟨jqN M, h⟩ = y := by
      intro h
      exact hψy

    have himg : ∀ (x : LaurentSeries ℚ)
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
      subst hα1
      exfalso
      haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
      have hv1 : qExpand K M (sv K ((cycUnit (M * p) : Kˣ) ^ M) 1 β)
          = TS K M (((cycUnit (M * p) : Kˣ) ^ M) ^ (β * 1)) := by
        rw [sv_eq_TS, qExpand_TS]
        exact TS_congr' (by ring) rfl
      obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hx_pS
      have hw2 : qExpand K p w = TS K M (((cycUnit (M * p) : Kˣ) ^ M) ^ (β * 1)) := by
        rw [hw, hβ0, hv1]
      have hnd : ¬ ((p : ℤ) ∣ (-(M : ℤ))) := by
        rw [dvd_neg, Int.natCast_dvd_natCast]
        exact hpM
      have hz1 : (qExpand K p w).coeff (-(M : ℤ)) = 0 :=
        qExpand_coeff_of_not_dvd (R := K) (N := p) w hnd
      have hz2 : (TS K M (((cycUnit (M * p) : Kˣ) ^ M) ^ (β * 1))).coeff (-(M : ℤ))
          = (((((cycUnit (M * p) : Kˣ) ^ M) ^ (β * 1))⁻¹ : Kˣ) : K) :=
        TS_coeff_neg M _
      rw [hw2, hz2] at hz1
      exact Units.ne_zero _ hz1
    ·
      have hα2' := hα2.symm
      subst hα2'
      have hβ0' : β = 0 := by
        have h3 : p / p = 1 := Nat.div_self hp.out.pos
        omega
      subst hβ0'
      have hsp : qExpand K M (sv K ((cycUnit (M * p) : Kˣ) ^ M) p 0)
          = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
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

  obtain ⟨z, hz⟩ := mem_range_of_eval_eq_const g'
    (coeffEmb K (qExpand ℚ (M * p) (jqN p))) s hg'deg hval
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
