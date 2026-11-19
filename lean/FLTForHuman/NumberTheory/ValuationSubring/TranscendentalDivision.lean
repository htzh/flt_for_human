/-
  Division of `aeval` values at a transcendental element.

  `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv`: over an algebraically
  closed field `L` with a valuation subring `A`, for a transcendental `f` over `L` and polynomials
  `p t : L[X]` with `A`-integral coefficients, where `t` has a unique coefficient of valuation exactly
  `1`, the quotient `aeval f p / aeval f t` splits into a principal part `aeval f p₁ / aeval f t₁` with
  `A`-integral coefficients and unit leading valuations, a term
  `(f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s)` of order `m` at infinity, and a remainder `aeval f⁻¹ r` of
  degree `< m`.

  Transcribed from the pin `S_` file below (pinned `aa2d8b3`, 138 lines).

  The pin's `E4Sol` block (`S_` file `:8-114`) is the pipeline's solution-stage namespace and is
  dropped as a label. Seventeen of its nineteen public declarations are already public in the port's
  shared partial-fraction block (`FieldTheory/ValuationSubringPartialFraction.lean`, namespace
  `P1aSol`, ported from the sibling pin
  `S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div`) and arrive through this
  module's one import; the two it lacks — `ACoeff.X_pow` (`S_` file `:22`) and
  `IsLam.exists_eq_aeval_add_pow_mul` (`S_` file `:95`) — are the pin's own additions and are declared
  here, **public**, as in the pin (the surface gate reads all three declarations `ok` at the pin's
  statements and section-variable shape), so the module's public surface is `3 ok`.

  Imports: the scaffold's `FieldTheory/ValuationSubringPartialFraction` is the row's premise and the
  shared block; no import line was added (the row's `Transcendental`/`Polynomial` vocabulary is all in
  that module's closure).

  Heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file): silent at
  `N = 4000`, fails at `N = 2000`. Nothing is installed — the edit loop runs at the playbook's
  `200000` and the module carries no `set_option maxHeartbeats`.

  spec-pin: P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.lean
-/
import FLTForHuman.FieldTheory.ValuationSubringPartialFraction

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ValuationSubring

open P1aSol

/-! ### The two engines the pin adds to the partial-fraction block

`ACoeff.X_pow` and `IsLam.exists_eq_aeval_add_pow_mul` are this row's own lemmas: the integrality of
`X ^ n`, and the `m`-step remainder recursion that peels an `A`-integral constant off an `IsLam` term.
Both are public, as in the pin, and stated with the pin's section variables
(`variable {L} [Field L] (A : ValuationSubring L)`, then `variable {F} [Field F] [Algebra L F]`): the
checker hashes the statement text, and the pin's own shape is a section, not spelled binders (FR-0218).
-/

section

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem ACoeff.X_pow (n : ℕ) : ACoeff A ((Polynomial.X : L[X]) ^ n) := fun j => by
  rw [coeff_X_pow]; split_ifs <;> simp [A.one_mem, A.zero_mem]

variable {F : Type*} [Field F] [Algebra L F]

theorem IsLam.exists_eq_aeval_add_pow_mul {g x : F} (hg : Transcendental L g)
    (hx : IsLam A g x) (m : ℕ) :
    ∃ r : L[X], ACoeff A r ∧ r.degree < m ∧ ∃ x', IsLam A g x' ∧ x = aeval g r + g ^ m * x' := by
  induction m with
  | zero =>
    exact ⟨0, ACoeff.zero A, by simp, x, hx, by simp⟩
  | succ m ih =>
    obtain ⟨r, hr, hrdeg, x', hx', hxe⟩ := ih
    obtain ⟨a, haA, x'', hx'', hx'e⟩ := hx'.exists_eq_add_mul A hg
    refine ⟨r + Polynomial.C a * X ^ m, ACoeff.add A hr (ACoeff.mul A (ACoeff.C A haA)
      (ACoeff.X_pow A m)), ?_, x'', hx'', ?_⟩
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le hrdeg (by exact_mod_cast Nat.le_succ m)
      · calc (Polynomial.C a * X ^ m).degree ≤ (m : WithBot ℕ) := degree_C_mul_X_pow_le m a
          _ < ((m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
    · rw [hxe, hx'e]
      simp only [map_add, map_mul, aeval_C, aeval_X_pow]
      ring

end

/-- **The division at a transcendental element.** A quotient of `aeval` values splits into a principal
part, an order-`m` tail at infinity and a remainder of degree `< m`. -/
theorem exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1)
    (m : ℕ) :
    ∃ p₁ t₁ q s r : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧ (∀ j, r.coeff j ∈ A) ∧ r.degree < m ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t =
        aeval f p₁ / aeval f t₁ + (f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s) + aeval f⁻¹ r := by
  have hfi : Transcendental L f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  obtain ⟨p₁, t₁, q₀, s₀, hp₁, hq₀, ht₁, hs₀, hdec⟩ :=
    ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div A hf p t hp ht

  have hlam : IsLam A f⁻¹ (aeval f⁻¹ q₀ / aeval f⁻¹ s₀) :=
    ⟨q₀, s₀, hq₀, hs₀, div_mul_cancel₀ _ (aeval_ne_zero_of_isGood A hfi hs₀)⟩
  -- the pin's `hlam.exists_eq_aeval_add_pow_mul A hfi m`, applied by name: the head constant is
  -- `P1aSol.IsLam`, whose namespace this module does not reopen, so dot notation does not reach it
  obtain ⟨r, hr, hrdeg, x', ⟨q, s, hq, hs, hx'e⟩, hxe⟩ :=
    IsLam.exists_eq_aeval_add_pow_mul A hfi hlam m
  refine ⟨p₁, t₁, q, s, r, hp₁, hq, hr, hrdeg, ht₁, hs, ?_⟩
  rw [hdec, hxe, eq_div_iff (aeval_ne_zero_of_isGood A hfi hs) |>.mpr hx'e]
  ring

end ValuationSubring
