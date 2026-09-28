/-
  The counting core of the Dedekind `ψ` function: a block of coprime residues and
  the fibre of the primitive-coset projection.

  `card_filter_coprime_range_mul` is the block count
  `#{b < g * m | b coprime to g} = m * φ(g)`; mathlib has its three ingredients
  (`Nat.totient_eq_card_coprime`, `Nat.periodic_coprime`,
  `Nat.count_eq_card_filter_range`) but not the block statement, so it is owned
  here. `dedekindPsiFibre (a, d) = (d / gcd a d) * φ(gcd a d)` is the summand of
  `ψ`, and `card_fibre` counts the `b < d` coprime to `gcd a d`.

  This is generic number theory, not modular forms (the sibling
  `TsumDivisorsAntidiagonal.lean` records the same rule), so it gets its own
  module rather than being exported from either consumer. Both the `Φ`-degree
  slot count (`ModularCurve/FunctionFieldGeneration/SlotProduct.lean`) and the
  `Γ₀`-index `primCosetReps` count (`ModularCurve/Gamma0Index.lean`) import it;
  before this module each carried a private copy of all three declarations.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`: the pin writes these `private` in
  `P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean` (as `h`,
  `card_filter_coprime_range_mul`, `card_fibre`) and, under the port's re-derived
  closed form, in `S_ModularCurve_jqN_prime_not_mem_full.lean` (as `slotH`). The
  port renames the value function to `dedekindPsiFibre` because the name `slotH`
  is already taken publicly by `ModularCurve.QExpN.slotH` (the Hecke slot
  function, a different object).
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false

open Finset

/-- A full block of `g * m` consecutive residues contains `m * φ(g)` coprime to
`g`: `Coprime g` is `g`-periodic and each period has `φ(g)` of them. -/
theorem card_filter_coprime_range_mul (g m : ℕ) :
    ((range (g * m)).filter (fun b => Nat.Coprime g b)).card = m * Nat.totient g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.count_eq_card_filter_range] at ih ⊢
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.totient_eq_card_coprime]
    refine congrArg card (filter_congr (fun k _ => ?_))
    have hper := (Nat.periodic_coprime g).nat_mul m
    rw [Nat.cast_id] at hper
    rw [show g * m + k = k + m * g by ring]
    exact Iff.of_eq (hper k)

/-- The Dedekind-`ψ` fibre value `(d / gcd a d) * φ(gcd a d)`. -/
abbrev dedekindPsiFibre (x : ℕ × ℕ) : ℕ :=
  (x.2 / Nat.gcd x.1 x.2) * Nat.totient (Nat.gcd x.1 x.2)

/-- The fibre count: the `b < d` coprime to `gcd a d` number `dedekindPsiFibre (a, d)`. -/
theorem card_fibre (a d : ℕ) :
    ((range d).filter (fun b => Nat.Coprime (Nat.gcd a d) b)).card =
      dedekindPsiFibre (a, d) := by
  set g := Nat.gcd a d with hg
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  obtain ⟨m, hm⟩ := hgd
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    have hd0 : d = 0 := by rw [hm, hg0, zero_mul]
    simp [dedekindPsiFibre, hd0]
  · conv_lhs => rw [hm]
    rw [card_filter_coprime_range_mul, dedekindPsiFibre]
    simp only
    rw [← hg, hm, Nat.mul_div_cancel_left m hgpos]
