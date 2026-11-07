/-
  The slot values of the level-`M` modular equation: the slot count, the multiset
  `slotValues M F` over the divisor/coprime grid, its counting, its product, its
  distinctness, and the descent data and prime-degree facts the slot argument needs.

  `slotValues M F` is `M.divisors`-indexed: for each divisor `a`, the `b < M / a` coprime to
  `M / a`, with value `F a b`. It is deliberately **generic in `F`** — a slot value is
  `sv K ζ a b` (`Defs/TS.lean`), but nothing here looks inside it, so both slot-product modules
  (`FunctionFieldGeneration/SlotProduct.lean` over `ℚ`, `FunctionFieldGeneration/SlotProductAnyField.lean`
  over an arbitrary field) share this one API and instantiate it at their own `sv`. The pin has no
  declaration for any of it: these are the named sub-goals of its monolithic `rval_aux`
  (`P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` 832–1494), promoted once here.

  ## The slot count lives here

  `slotAt n d` counts the `b < d` with `gcd (gcd (n/d) b) d = 1`; `slots n` sums it over the
  divisors of `n`; `slots_eq_dedekindPsi` closes the chain at `ψ(n)` from
  `NumberTheory/DedekindPsi.card_fibre`, and `card_slotFilter_eq_dedekindPsi` is the divisor sum
  a consumer of the slot list cites. It is here, not in `SlotProduct.lean`, because
  `card_slotValues` — which lives here — needs it: the count is *derived*, not taken as a
  hypothesis. The arithmetic is `M`-only (`slotAt`, `slots`, the `dedekindPsiFibre`
  multiplicativity and the prime-power evaluation) and mentions no slot value.

  One note on a statement. `nodup_slotValues` takes the distinguishability of slot parameters as
  a hypothesis: proving it is `sv_inj`, which mentions `sv` and therefore lives with the slot
  value in each module, not here.

  Assumes `LaurentSeries` (`Defs/Laurent.lean`) and `dedekindPsi` (`NumberTheory/DedekindPsi.lean`).

  ## Tier 3, deliberately

  This module carries no `spec-pin:` line and no `decl_markers.tsv` rows. Every declaration is the
  port's own — the pin has no counterpart to diff against — so a wire plus an `own:` row per
  declaration would record "ours" every time and diff nothing. It is registered instead:
  `spec/unwired_register.py` lists the public declarations with "the port's own, no pin source"
  and both importers, and `--check` keeps that register fresh. What pins the statements is use: the two
  slot-product modules cite every one of them at specific arguments, so any drift breaks their
  builds. Wire it only if a pin-derived statement is ever added here.

-/
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Defs
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.NumberTheory.DedekindPsi
import FLTForHuman.ModularCurve.Defs.DedekindPsi

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve

variable {K : Type*} [Field K]

/-! ## The slot count

`slotAt n d` counts the `b < d` with `gcd (gcd (n/d) b) d = 1`; `slots n` sums it
over the divisors of `n`. The endpoint is `slots n = ψ(n)`, by
`Nat.recOnPosPrimePosCoprime`. -/

private def slotAt (n d : ℕ) : ℕ :=
  ((Finset.range d).filter fun b => Nat.gcd (Nat.gcd (n / d) b) d = 1).card

def slots (n : ℕ) : ℕ := ∑ d ∈ n.divisors, slotAt n d

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

/-- The slot multiset: for each divisor `a` of `M`, the slot values `F a b` over the
`b < M / a` coprime to `M / a`. -/
def slotValues (M : ℕ) (F : ℕ → ℕ → LaurentSeries K) : Multiset (LaurentSeries K) :=
  M.divisors.val.bind fun a =>
    ((Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map
      (fun b => F a b)

/-- **Membership in the slot multiset**: `x` is the slot value `F a b` of some divisor
`a` of `M` and some `b` in the coprime slot range. -/
theorem mem_slotValues {M : ℕ} {F : ℕ → ℕ → LaurentSeries K} {x : LaurentSeries K} :
    x ∈ slotValues M F ↔ ∃ a b : ℕ, a ∈ M.divisors ∧
      b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) ∧
      x = F a b := by
  simp only [slotValues, Multiset.mem_bind, Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨a, ha, b, hb, hxb⟩
    exact ⟨a, b, ha, hb, hxb.symm⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- **The slot count**: the slot multiset has `ψ(M)` elements. The count of the
divisor/coprime grid is `card_slotFilter_eq_dedekindPsi`, proved above from
`card_fibre`; this reads it off the multiset. -/
theorem card_slotValues {M : ℕ} (hM0 : M ≠ 0) (F : ℕ → ℕ → LaurentSeries K) :
    (slotValues M F).card = dedekindPsi M := by
  rw [slotValues, Multiset.card_bind]
  have h2 : M.divisors.val.map (Multiset.card ∘ fun a =>
      ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).val.map (fun b => F a b))
      = M.divisors.val.map (fun a => ((Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card) := by
    refine Multiset.map_congr rfl ?_
    intro a _
    simp only [Function.comp_apply, Multiset.card_map, Finset.card]
  rw [h2]
  exact card_slotFilter_eq_dedekindPsi M hM0

/-- **The slot product factors over the slot multiset**: the iterated Finset product
`∏ a ∈ M.divisors, ∏ b ∈ …, (X - C (F a b))` is the product of `X - C r` over the slot
values `r`. -/
theorem prod_slotValues (M : ℕ) (F : ℕ → ℕ → LaurentSeries K) :
    ((slotValues M F).map (fun r => Polynomial.X - Polynomial.C r)).prod
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (F a b)) := by
  rw [slotValues, Multiset.map_bind, Multiset.prod_bind]
  simp only [Multiset.map_map, Function.comp]
  rfl

/-- **Distinct slots**: if two slot parameters with equal values are equal, the slot
multiset has no repetitions. (A slot value depends only on its parameter pair.) -/
theorem nodup_slotValues {M : ℕ} {F : ℕ → ℕ → LaurentSeries K}
    (hinj : ∀ a b a' b', a ∈ M.divisors → a' ∈ M.divisors →
      b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) →
      b' ∈ (Finset.range (M / a')).filter (fun b' => Nat.gcd (Nat.gcd a' b') (M / a') = 1) →
      F a b = F a' b' → a = a' ∧ b = b') :
    (slotValues M F).Nodup := by
  rw [slotValues, Multiset.nodup_bind]
  constructor
  · intro a ha
    refine Multiset.Nodup.map_on ?_ (Finset.filter _ _).nodup
    intro b hb b' hb' hvv
    exact (hinj a b a b' (Finset.mem_val.mp ha) (Finset.mem_val.mp ha)
      (Finset.mem_val.mp hb) (Finset.mem_val.mp hb') hvv).2
  · refine Multiset.Nodup.pairwise ?_ M.divisors.nodup
    intro a ha a' ha' hne
    change Disjoint _ _
    rw [Multiset.disjoint_left]
    intro x hx hx'
    rw [Multiset.mem_map] at hx hx'
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨b', hb', hxb'⟩ := hx'
    exact hne (hinj a b a' b' (Finset.mem_val.mp ha) (Finset.mem_val.mp ha')
      (Finset.mem_val.mp hb) (Finset.mem_val.mp hb') (by rw [hxb, ← hxb'])).1

/-- **The slot values sit inside the roots**: if the slot values are distinct (`nodup`), the
polynomial is nonzero, and every slot value is a root of it, then the slot multiset is
contained in the root multiset. Counting: a multiset element has count at most `1` on the left
and at least `1` on the right. -/
theorem slotValues_le_roots {M : ℕ} {F : ℕ → ℕ → LaurentSeries K}
    {q : Polynomial (LaurentSeries K)} (hne : q ≠ 0) (hnd : (slotValues M F).Nodup)
    (hroot : ∀ a b, a ∈ M.divisors →
      b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) →
      F a b ∈ q.roots) :
    slotValues M F ≤ q.roots := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ slotValues M F
  · refine le_trans (Multiset.nodup_iff_count_le_one.mp hnd x) ?_
    rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots']
    obtain ⟨a, b, ha, hb, rfl⟩ := mem_slotValues.mp hx
    exact ⟨hne, (Polynomial.mem_roots'.mp (hroot a b ha hb)).2⟩
  · rw [Multiset.count_eq_zero.mpr hx]
    exact Nat.zero_le _

/-- **The descent data of a slot**: for `a ∣ M` with `M / a ≠ 1`, let `p = (M / a).minFac` and
`M / a = p * d''`. Then `p` is prime and the slot `(a, b)` descends to the slot `(a, b % d'')` at
the level `a * d''`, with companion index `b / d'' < p`; the descent stays coprime to the
complementary divisor. -/
theorem exists_slot_descent_data {M a b : ℕ} (hM0 : M ≠ 0) (haM : a ∣ M)
    (hd1 : M / a ≠ 1) (hb : b < M / a) (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) :
    ∃ p d'' : ℕ, p.Prime ∧ d'' ≠ 0 ∧ M / a = p * d'' ∧ b % d'' < d'' ∧ b / d'' < p ∧
      Nat.gcd (Nat.gcd a (b % d'')) d'' = 1 ∧ b % d'' + b / d'' * d'' = b := by
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  have hd0 : M / a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at had
    exact hM0 had.symm
  have hpp : (M / a).minFac.Prime := Nat.minFac_prime hd1
  obtain ⟨d'', hdd⟩ : (M / a).minFac ∣ M / a := Nat.minFac_dvd _
  have hd''0 : d'' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hdd
    exact hd0 hdd
  have hb''lt : b % d'' < d'' := Nat.mod_lt b (Nat.pos_of_ne_zero hd''0)
  have hbsplit : b % d'' + b / d'' * d'' = b := Nat.mod_add_div' b d''
  have hc₀p : b / d'' < (M / a).minFac := by
    have h1 : b < d'' * (M / a).minFac := by
      rw [Nat.mul_comm d'' (M / a).minFac, ← hdd]
      exact hb
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
        exact (Nat.gcd_dvd_right _ _).mul_left (M / a).minFac
    rw [hbc] at h1
    exact Nat.dvd_one.mp h1
  exact ⟨(M / a).minFac, d'', hpp, hd''0, hdd, hb''lt, hc₀p, hprim', hbsplit⟩

/-- **A prime-degree irreducible minimal polynomial has no roots in its base field**: if
`minpoly E x` has prime degree `p > 1`, it is not rooted at any element of `E` — a root
would exhibit it as `X - C y`, of degree `1`. -/
theorem not_isRoot_minpoly_of_prime_deg {E L : Type*} [Field E] [Field L] [Algebra E L]
    {x : L} (p : ℕ) (hpp : p.Prime) (hα : IsIntegral E x)
    (hdeg : (minpoly E x).natDegree = p) (y : E) :
    ¬ (minpoly E x).IsRoot y := by
  intro hcon
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hcon
  rcases (minpoly.irreducible hα).isUnit_or_isUnit hq with hu | hu
  · exact Polynomial.not_isUnit_X_sub_C _ hu
  · have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact minpoly.ne_zero hα hq
    have hdm : (minpoly E x).natDegree = 1 := by
      rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu]
    rw [hdm] at hdeg
    exact (Nat.ne_of_lt hpp.one_lt) hdeg

end ModularCurve

end
