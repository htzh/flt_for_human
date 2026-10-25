/-
  The slot values of the level-`M` modular equation: the multiset `slotValues M F` over the
  divisor/coprime grid, its counting, its product, its distinctness, and the descent data and
  prime-degree facts the slot argument needs.

  `slotValues M F` is `M.divisors`-indexed: for each divisor `a`, the `b < M / a` coprime to
  `M / a`, with value `F a b`. It is deliberately **generic in `F`** — a slot value is
  `sv K ζ a b` (`Defs/TS.lean`), but nothing here looks inside it, so both slot-product modules
  (`FunctionFieldGeneration/SlotProduct.lean` over `ℚ`, `FunctionFieldGeneration/SlotProductAnyField.lean`
  over an arbitrary field) share this one API and instantiate it at their own `sv`. The pin has no
  declaration for any of it: these are the named sub-goals of its monolithic `rval_aux`
  (`P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` 832–1494), promoted once here.

  Two notes on the statements.

  * `card_slotValues` takes the slot **count** as a hypothesis rather than proving it: the count
    `∑ a ∈ M.divisors, card ((range (M / a)).filter …) = ψ(M)` is
    `card_slotFilter_eq_dedekindPsi`, whose home is `SlotProduct.lean` (downstream of here, where
    the arithmetic core lives). Stating it as a hypothesis keeps this module upstream and leaves
    one home for the count.
  * `nodup_slotValues` takes the distinguishability of slot parameters as a hypothesis, for the
    same reason: proving it is `sv_inj`, which mentions `sv` and therefore lives with the slot
    value in each module, not here.

  Assumes `LaurentSeries` (`Defs/Laurent.lean`) and `dedekindPsi` (`NumberTheory/DedekindPsi.lean`).

  ## Tier 3, deliberately

  This module carries no `spec-pin:` line and no `decl_markers.tsv` rows. Every declaration is the
  port's own — the pin has no counterpart to diff against — so a wire plus seven `own:` rows would
  record "ours" seven times and diff nothing. It is registered instead:
  `spec/unwired_register.py` lists the seven declarations with "the port's own, no pin source" and
  both importers, and `--check` keeps that register fresh. What pins the statements is use: the two
  slot-product modules cite every one of them at specific arguments, so any drift breaks their
  builds. Wire it only if a pin-derived statement is ever added here.

-/
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

/-- **The slot count**: given the slot-count identity
`∑ a ∈ M.divisors, card ((range (M / a)).filter …) = ψ(M)` — `card_slotFilter_eq_dedekindPsi` —
the slot multiset has `ψ(M)` elements. -/
theorem card_slotValues {M : ℕ} (_hM0 : M ≠ 0) (F : ℕ → ℕ → LaurentSeries K)
    (hcount : (∑ a ∈ M.divisors,
      ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card) = dedekindPsi M) :
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
  exact hcount

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
