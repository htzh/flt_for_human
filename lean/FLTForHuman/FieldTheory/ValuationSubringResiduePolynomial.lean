/-
A residue-nonvanishing polynomial multiplies the adjoined element into every valuation subring.

`ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem`: for a valuation subring `A` of
a field `L`, a finite extension `F = L(f)` and any `z : F`, there is a polynomial `q` over `A` whose
residue is non-zero and which multiplies `z` into **every** valuation subring `V` of `F` containing
`L` and `f`. It is the polynomial form of the weak-approximation step the gauss representation (order
A) takes as input, and its two premises are
`Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem`
(`RingTheory/IntegralClosure/FunctionField.lean`) and
`ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero`
(`FieldTheory/ValuationSubringValuedField.lean`).

The home is a new module because neither premise module is above the other: this one imports both,
which is why the row could not be inserted into `ValuationSubringPolynomial.lean` (it is unwired, so a
new declaration there would never be checked — the checker iterates the *module's* declarations, and
an unwired module's are unaccounted).

## The rows

* `ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem` — 42 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.lean>

spec-pin: Theorems/Thm_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.lean
spec-pin: P2M/Sol/S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.lean

**Landing (AF107H).**  The row is transcribed in full over its two premises — no new mathematics, the
pin's 32-line `S_` proof verbatim.  The scaffold's three imports sufficed:
`Algebra.adjoin_singleton_eq_range_aeval` arrives through
`FLTForHuman.RingTheory.IntegralClosure.FunctionField`, `Polynomial.eval₂_map` through
`Mathlib.RingTheory.Polynomial.Basic`.  No import added.

* Engine gate: **2** pin files (the wrapper and its `S_`), **2** pin decls; module **1** public decl,
  **1 by hash**, 0 by name, 0 unaccounted.
* `check_port` **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw** (`0 own` matters here: the pin's only
  row is the headline, so nothing but the headline may be declared).
* `#print axioms`: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* `dedup --within`: **0 clusters**; `move_dead --dry-run`: **0 declarations, 0 lines** (no helper at
  all — the proof is one `classical` block).
* Heartbeat probe pair (measured, **never installed**): **silent at `-DmaxHeartbeats=2000`**, **first
  fails at `1500`** (`whnf` timeout at line 62 and a `«tactic execution»` timeout at 64, both inside the
  headline's own `obtain ⟨q₁, hq₁⟩` / `heval` step); `1000` fails the same way.  2000 is 1 % of the
  200 000 edit-loop cap.  No `set_option maxHeartbeats` is installed — the pin's `set_option
  maxHeartbeats 8000000` is **not** transcribed.
* Two bare names need the port's spelling, both from the declaration's own prefix:
  * the pin's `open Polynomial` is not on the scaffold, so its bare `aeval_C` is written
    `Polynomial.aeval_C`;
  * the pin's bare `mul_mem` is the generic `MulMemClass` lemma; inside a declaration named
    `ValuationSubring.*` the bare name resolves instead to `ValuationSubring.mul_mem` (the
    valuation-valued statement, whose first explicit argument is the ring), so the port spells the
    closing step `V.mul_mem _ _ (hL c⁻¹) (hq₀T V hL hfV)` — FR-0310's class, read on the pin side.
-/


import FLTForHuman.FieldTheory.ValuationSubringValuedField
import FLTForHuman.RingTheory.IntegralClosure.FunctionField
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q : Polynomial A, (q.map (IsLocalRing.residue A)) ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V →
        (Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q) * z ∈ V := by
  classical
  obtain ⟨q₀, hq₀0, hq₀T⟩ :=
    Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem (L := L) f z
  have hmem : (↑q₀ : F) ∈ (Polynomial.aeval (R := L) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact q₀.2
  obtain ⟨q₁, hq₁⟩ := hmem
  have hq₁0 : q₁ ≠ 0 := by
    rintro rfl; simp only [map_zero] at hq₁
    exact hq₀0 (Subtype.ext hq₁.symm)
  obtain ⟨q, c, hc0, hqmap, hqbar⟩ :=
    ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero A q₁ hq₁0
  refine ⟨q, hqbar, fun V hL hfV => ?_⟩
  have heval : Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q =
      algebraMap L F c⁻¹ * (q₀ : F) := by
    have h1 : Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q =
        Polynomial.aeval f (q.map A.subtype) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [h1, hqmap, map_mul, Polynomial.aeval_C]
    exact congrArg _ hq₁
  rw [heval, mul_assoc]
  exact V.mul_mem _ _ (hL c⁻¹) (hq₀T V hL hfV)
