/-
The regular prolongation's residue and ord completion.

Two rows, and they close the `Fin (finrank)`-family SET-AF107A opened:

* `exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq` (237) — every element of `F` is
  `∑ (c_σ + μ_σ) z_σ` with `c_σ` integral over `A` and `μ_σ` of valuation `< 1`: the *multiplicative
  normal form* of the gauss representation, i.e. the clause the converse direction of the representation
  produces;
* `forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed` (206) — the residue span's orders are
  non-negative at every valuation subring containing `L` and `f`, and a monic polynomial of bounded degree
  exists for it.

The home is new because the first row's premises include SET-AF107A's
`RegularProlongationGaussRepresentation.lean` — the module a naive reading would insert into — so the same
FR-0037/FR-0038 shape applies as in that set: the home must sit **above** the basis module, and the
remaining premises (`RegularProlongationGaussDegree`, `FieldTheory/ValuationSubringResiduePolynomial`,
`Place/OrdCalculus`, `Defs/PlaceCalculus`, `DivisorPlaceReduction`, `FieldTheory/ValuationSubringFinrank`,
`NumberTheory/ValuationSubring/TranscendentalDivision`) are all below it.

## The rows

* `AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq` — 237 pin `S_` lines.
* `AlgebraicCurve.RegularProlongation.forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed` — 206 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq.lean
spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed.lean

## The engine diff and the two `def` suspects

The pin's two `S_` files carry two inner labels, `FF39` (row 206) and `H1Sol` (row 237), plus the
`P2MW.S_…` staging namespace. Both labels come off: `FF39`'s surviving declarations are stated at their
pin names in `AlgebraicCurve.RegularProlongation`, next to the four `constHom`-block declarations that
already landed there in `RegularProlongationFinrank.lean`; `H1Sol` becomes the subject namespace
`AlgebraicCurve.RegularProlongation.MultiplicativeNormalForm` (the block is the multiplicative normal
form's engine: the `IsGoodAt` polynomial-clearing predicate and the two `IsLam` predicates).

The advise pairs two `def`s **on their type only** (FR-0266). Both bodies were read:

* pin `IsLam (f x : F)` vs `ValuationSubring.ZfSol.IsW (f x : F)` — **different predicates, not
  substitutable.** Both write `∃ p q, (∀ j, p.coeff j ∈ A) ∧ (_) ∧ x * aeval f q = aeval f p`, but the
  denominator side differs: the pin's is `IsGoodAt d` — *one* coefficient of valuation exactly `1` and
  **every other coefficient strictly below** `1` — while `ZfSol.IsW`'s is the weaker "all coefficients
  `≤ 1`, and some coefficient `= 1`". The pin's predicate implies `IsW`, not conversely, so the two are
  not the same `def` and the pin's body is restated here (the `IsMW` shape SET-AF107A met). Note the
  engine gate cannot see this: `check_port` hashes the *type* of a `def`, and the types are identical.
* pin `IsLamPlus (g x : F)` vs `ValuationSubring.P1aSol.IsLam (g x : F)` — **the same predicate; the
  advise is right.** Both are `∃ p t, (∀ j, p.coeff j ∈ A) ∧ A.valuation (t.coeff 0) = 1 ∧
  (∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧ x * aeval g t = aeval g p` (`P1aSol.IsLam` spells the
  coefficient clause `ACoeff A p`, a `def` whose body is that `∀ j`). The pin's public name is kept —
  the pin declares `IsLamPlus` publicly and `main`'s statement mentions it — but the body is the port's
  existing predicate, not a second copy of the mathematics.

The first row also has an *upstream* `IsGoodAt d` generalising the port's `IsGood` (which is `d = 0`
only) — the advise's binder-spelling tier points `IsGoodAt.valuation_le` / `.coeff_mem` / `.ne_zero` at
`IsGood`'s, and indeed those three bodies are the port's `IsGood` three with `d` in place of `0`; the
`d`-general form is what `IsLam.mul_isLamPlus` needs (a `d`-good `t` times a `0`-good `s` is `d`-good),
so the block is transcribed at the pin's `d`.

Both verdicts were also *measured*, not only read: `IsLamPlus A g x ↔ ValuationSubring.P1aSol.IsLam A g x`
closes by `Iff.rfl` (the substitution is definitional), while `IsLam A f x → ValuationSubring.ZfSol.IsW A f x`
needs a real proof and the converse is not available — `ZfSol.IsW` is the weakening. The row-237 headline
is the decisive witness for `IsLam`: its last hypothesis writes the clause out as
`∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1`, and `main` takes
`IsLam A f x` in exactly that position, so `IsLam` **must** carry the pin's strict body or `main` would not
be definitionally the headline.

## The gates (measured)

* `check_port --force`: **16 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* Engine diff over the four `spec-pin:` sources: **4 pin sources, 22 pin declarations, 16 module
  declarations — 16 by hash, 0 by name, 0 unaccounted.** The six pin declarations the module does not carry
  are the four `constHom`-block members already landed in `RegularProlongationFinrank.lean` (`constHom`,
  `coe_constHom`, `subtype_comp_eval₂_constHom`, `residue_comp_eval₂_constHom`) and the two `solution`s:
  each `Theorems/Thm_…` wrapper and its `S_` twin carry the *same* statement, so the module declares it
  once, at the headline name (both read hash-equal to the wrapper's row).
* `lake env lean` at the 200 k edit-loop cap: **silent**; one `flock`ed
  `lake build FLTForHuman.AlgebraicCurve.RegularProlongationResidueOrd`: **0 warning lines from this file**.
* `#print axioms` on all **16** public declarations: `[propext, Classical.choice, Quot.sound]` in every
  case, **no `sorryAx`**.
* `dedup.py --within --module '*AlgebraicCurve/RegularProlongationResidueOrd*'`: **0 clusters** (16
  declarations); `move_dead.py --dry-run`: **0 declarations, 0 lines**.
* Heartbeat probe pair (measured, **never installed**): **silent at 10000**, **first fails at 5000** —
  `whnf` on `main`'s own elaboration (line 312), `isDefEq` inside `hsplit`'s `simp only [Algebra.smul_def]`
  (392) and inside `hures`'s `rw [heq, map_mul, …]` (506), `«tactic execution»` on the monic subgoal (517);
  1000 fails the same way. 10000 is 5 % of the 200 000 edit-loop cap. The pin's
  `set_option maxHeartbeats 8000000` is **not** transcribed, and no module floor was needed — the cheapest
  silent rung is already at 5 %.
* `private`: the pin has **no** `private` declaration in either `S_` file (all 20 are public), so the module
  has none and there is nothing for the surface gate to promote. No linter is silenced anywhere: the pin's
  `haveI := hfd` in `main` (and the `haveI := hfd` / `haveI := hι` the row-206 text would need) are
  **redundant in this toolchain** — instance search accepts the local hypotheses
  `hfd : FiniteDimensional … F` and `hι : Nonempty ι` directly (*measured*: the module elaborates with all
  three deleted), so the transcription drops them rather than silencing `linter.style.haveILetI`.
* Imports: **none added** — the scaffold's list elaborated everything (`Mathlib.Tactic` carries
  `linear_combination`, `gcongr`, `ring`, `omega`; `Polynomial.eval₂_map` arrives through
  `ValuationSubringResiduePolynomial`'s `Mathlib.RingTheory.Polynomial.Basic`).
* The substitution pass priced the order at 443 pin `S_` lines / 396 declaration lines, **150 already in the
  port** (the four `constHom`-block members), **net new 246**; the module is 531 lines — 16 declarations
  from line 153 on (379 lines), the first 152 being this header, the `spec-pin:` wires, imports and
  opens.

## Two body-level adaptations, both measured

* `Place.min_ord_le_ord_add`: the port's version (`Defs/PlaceCalculus.lean`) drops the pin's `f ≠ 0` and
  `g ≠ 0`, so the pin's two `eq_or_ne (a i) 0` / `eq_or_ne (b i) 0` splits in the `add` case of the
  `span_induction` go with them (6 pin lines); the call is `Place.min_ord_le_ord_add w h0` with the single
  `f + g ≠ 0`. Nothing was restated.
* `Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg w hint hw` and
  `Place.ord_smul_of_ne_zero w hc` are the port's, at the pin's application shapes.
-/

import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.DivisorPlaceReduction
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank
import FLTForHuman.AlgebraicCurve.RegularProlongationGaussDegree
import FLTForHuman.AlgebraicCurve.RegularProlongationGaussRepresentation
import FLTForHuman.FieldTheory.ValuationSubringFinrank
import FLTForHuman.FieldTheory.ValuationSubringResiduePolynomial
import FLTForHuman.NumberTheory.ValuationSubring.TranscendentalDivision
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

open AlgebraicCurve Polynomial IsLocalRing

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace RegularProlongation

/-! ### The residue of an `eval₂` at constants

The pin's `FF39.ConstHom` block declares `constHom`, `coe_constHom`, `subtype_comp_eval₂_constHom`,
`eval₂_mem_integers'`, `eval₂_mk`, `residue_comp_eval₂_constHom`, `residue_eval₂'`. The first four are
already in `RegularProlongationFinrank.lean` and are imported, not restated; the three below are the rest
of the block, at the pin's names and in its own namespace (that is where the pin's siblings live). -/

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem eval₂_mem_integers' (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q ∈ R.integers := by
  have h := congrArg (· q) (subtype_comp_eval₂_constHom R ⟨f, hf⟩)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom] at h
  exact h ▸ (eval₂ (constHom R) ⟨f, hf⟩ q).2

theorem eval₂_mk (R : RegularProlongation A F Fbar) (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    (⟨_, eval₂_mem_integers' R q f hf⟩ : R.integers) = eval₂ (constHom R) ⟨f, hf⟩ q := by
  apply Subtype.ext
  have h := congrArg (· q) (subtype_comp_eval₂_constHom R ⟨f, hf⟩)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom] at h
  exact h.symm

theorem residue_eval₂' (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    R.residue ⟨_, eval₂_mem_integers' R q f hf⟩ =
      Polynomial.aeval (R.residue ⟨f, hf⟩) (q.map (IsLocalRing.residue A)) := by
  rw [eval₂_mk R q f hf]
  have h := congrArg (· q) (residue_comp_eval₂_constHom R ⟨f, hf⟩)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, coe_mapRingHom] at h
  rw [h, Polynomial.aeval_def, eval₂_map]

/-- The residue of an element lying in every valuation subring that contains `L` and `f` is integral
over the residue adjoin of the residue of `f`. -/
theorem isIntegral_residue_of_mem_T
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (u : F)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V)
    (huO : ∀ i, u ∈ (R i).integers) (i : ι) :
    IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R i).residue ⟨f, hf i⟩})
      ((R i).residue ⟨u, huO i⟩) := by
  obtain ⟨m, h₂⟩ := ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin f u h₁
  have h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i).integers)) → u ∈ V := by
    intro V hV
    obtain ⟨j, hj⟩ :=
      RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
        A Fb R hR f hf htr heq i V hV
    rw [hj]; exact huO j
  obtain ⟨p, hpmon, _hpdeg, hpev⟩ :=
    RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring A (R i) ⟨f, hf i⟩
      (htr i) u m h₁ h₂ h₃
  exact RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero A (R i)
    ⟨f, hf i⟩ ⟨u, huO i⟩ ⟨p, hpmon, hpev⟩

/-! ### The multiplicative normal form's engine (the pin's `H1Sol` block) -/

namespace MultiplicativeNormalForm

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- A polynomial that is `d`-good: the `d`-th coefficient has valuation exactly `1`, every other
coefficient strictly less than `1`. The port's `ValuationSubring.ZfSol.IsGood` is the `d = 0` case. -/
def IsGoodAt (d : ℕ) (t : L[X]) : Prop :=
  A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1

theorem IsGoodAt.valuation_le {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = d
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGoodAt.coeff_mem {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) : t.coeff j ∈ A :=
  (A.valuation_le_one_iff _).mp (ht.valuation_le A j)

theorem IsGoodAt.ne_zero {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) : t ≠ 0 := by
  intro h
  have := ht.1
  rw [h, coeff_zero, map_zero] at this
  exact zero_ne_one this

theorem IsGoodAt.mul_zero_good {d : ℕ} {t s : L[X]} (ht : IsGoodAt A d t) (hs : IsGoodAt A 0 s) :
    IsGoodAt A d (t * s) := by
  classical
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_mul, ← Finset.add_sum_erase _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero d) :
      (d, 0) ∈ Finset.HasAntidiagonal.antidiagonal d)]
    have hmain : A.valuation (t.coeff d * s.coeff 0) = 1 := by rw [map_mul, ht.1, hs.1, one_mul]
    have hrest : A.valuation (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal d).erase (d, 0), t.coeff x.1 * s.coeff x.2) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro x hx
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [map_mul]
      have h2 : x.2 ≠ 0 := by
        intro h0
        apply hx.1
        ext
        · simpa [h0] using hx.2
        · exact h0
      calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ 1 * A.valuation (s.coeff x.2) := by gcongr; exact ht.valuation_le A _
        _ < 1 := by rw [one_mul]; exact hs.2 _ h2
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]
  · rw [coeff_mul]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    by_cases h1 : x.1 = d
    · have h2 : x.2 ≠ 0 := by omega
      calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ 1 * A.valuation (s.coeff x.2) := by gcongr; exact ht.valuation_le A _
        _ < 1 := by rw [one_mul]; exact hs.2 _ h2
    · calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ A.valuation (t.coeff x.1) * 1 := by gcongr; exact hs.valuation_le A _
        _ < 1 := by rw [mul_one]; exact ht.2 _ h1

variable {F : Type*} [Field F] [Algebra L F]

theorem aeval_ne_zero_of_isGoodAt {g : F} (hg : Transcendental L g) {d : ℕ} {t : L[X]}
    (ht : IsGoodAt A d t) : aeval g t ≠ 0 := fun h =>
  ht.ne_zero A (transcendental_iff.mp hg _ h)

/-- `x` is in the pin's `IsLam` local ring at `f`: `x` clears a `d`-good denominator. The port's
`ValuationSubring.ZfSol.IsW` is *not* this predicate (its denominator only needs coefficients `≤ 1`), so
it is restated here at the pin's body; `ValuationSubring.P1aSol.IsLam` *is* this predicate with the
denominator pinned at `d = 0`, i.e. the `IsLamPlus` below. -/
def IsLam (f x : F) : Prop :=
  ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
    (∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) ∧
    x * aeval f t = aeval f p

def IsLamPlus (g x : F) : Prop :=
  ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
    (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
    x * aeval g t = aeval g p

theorem IsLam.mul_isLamPlus {f x y : F} (hx : IsLam A f x) (hy : IsLamPlus A f y) :
    IsLam A f (x * y) := by
  obtain ⟨p, t, hp, ⟨d, hd⟩, hxe⟩ := hx
  obtain ⟨q, s, hq, hs, hye⟩ := hy
  refine ⟨p * q, t * s, fun j => ?_, ⟨d, IsGoodAt.mul_zero_good A hd hs⟩, ?_⟩
  · rw [coeff_mul]; exact sum_mem fun x _ => mul_mem (hp _) (hq _)
  · simp only [map_mul]
    linear_combination (y * aeval f s) * hxe + (aeval f p) * hye

end MultiplicativeNormalForm

namespace MultiplicativeNormalForm

section Main

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

theorem main (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F) (m₀ : ℕ),
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
        (f⁻¹) ^ m₀ * z σ ∈ V) ∧
      ∀ (x s : F), IsLam A f x → (∀ i, s ∈ (R i).integers) →
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V) →
        ∃ (lp lm : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F)
          (a : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → Fin m₀ → L),
          (∀ σ, IsLamPlus A f (lp σ)) ∧ (∀ σ, IsLamPlus A f⁻¹ (lm σ)) ∧ (∀ σ k, a σ k ∈ A) ∧
          x * s = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) +
            ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) := by
  classical

  obtain ⟨z, hzO, hzT, hzind, hB, hres⟩ :=
    exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
      A Fb R hR f hf htrL hfd htr heq

  have hm : ∀ σ, ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∉ V →
      z σ * (f ^ m)⁻¹ ∈ V := fun σ =>
    ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin f (z σ) (hzT σ)
  choose m hmV using hm
  set m₀ : ℕ := Finset.univ.sup m + 1 with hm₀
  have hmle : ∀ σ, m σ ≤ m₀ := fun σ =>
    (Finset.le_sup (f := m) (Finset.mem_univ σ)).trans (Nat.le_succ _)
  have hzT' : ∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      (f⁻¹) ^ m₀ * z σ ∈ V := by
    intro σ V hV hfV
    by_cases hfV' : f ∈ V
    · exact mul_mem (pow_mem hfV _) (hzT σ V hV hfV')
    · have h := hmV σ V hV hfV'
      have heq' : (f⁻¹) ^ m₀ * z σ = (f⁻¹) ^ (m₀ - m σ) * (z σ * (f ^ m σ)⁻¹) := by
        have hpow : (f⁻¹) ^ m₀ = (f⁻¹) ^ (m₀ - m σ) * (f ^ m σ)⁻¹ := by
          rw [← inv_pow, ← pow_add, Nat.sub_add_cancel (hmle σ)]
        rw [hpow]; ring
      rw [heq']
      exact mul_mem (pow_mem hfV _) h
  refine ⟨z, m₀, hzO, hzT, hzT', ?_⟩

  intro x s hx hsO hsT
  obtain ⟨w, hw, hsw⟩ := hB s hsO

  have hwplus : ∀ σ, IsLamPlus A f (w σ) := by
    intro σ
    obtain ⟨p, t, hp, ht, hwe⟩ :=
      ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul A htrL z hzT hzind
        hres s w hsT hw hsw σ
    refine ⟨p, t, hp, ht, ?_⟩
    rw [hwe, div_mul_cancel₀ _ (aeval_ne_zero_of_isGoodAt A htrL (d := 0) ht)]

  have hsplit : ∀ σ, ∃ (lp lm : F) (a : Fin m₀ → L), IsLamPlus A f lp ∧ IsLamPlus A f⁻¹ lm ∧
      (∀ k, a k ∈ A) ∧
      x * w σ = lp + lm * (f⁻¹) ^ m₀ + ∑ k : Fin m₀, algebraMap L F (a k) * (f⁻¹) ^ (k : ℕ) := by
    intro σ
    obtain ⟨p, t, hp, ⟨d, hd⟩, hxe⟩ := IsLam.mul_isLamPlus A hx (hwplus σ)
    obtain ⟨p₁, t₁, q, s', r, hp₁, hq, hr, hrdeg, ht₁, hs', hdec⟩ :=
      ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv A htrL p t hp
        ⟨d, hd⟩ m₀
    have htrinv : Transcendental L f⁻¹ := fun h => htrL (IsAlgebraic.inv_iff.mp h)
    have ht0 : aeval f t ≠ 0 := aeval_ne_zero_of_isGoodAt A htrL hd
    have ht₁0 : aeval f t₁ ≠ 0 := aeval_ne_zero_of_isGoodAt A htrL (d := 0) ht₁
    have hs'0 : aeval f⁻¹ s' ≠ 0 := aeval_ne_zero_of_isGoodAt A htrinv (d := 0) hs'
    have hxw : x * w σ = aeval f p / aeval f t := by
      rw [← hxe, mul_div_cancel_right₀ _ ht0]
    have hrnat : r.natDegree < m₀ := by
      by_cases hr0 : r = 0
      · rw [hr0, natDegree_zero, hm₀]; exact Nat.succ_pos _
      · exact (natDegree_lt_iff_degree_lt hr0).mpr hrdeg
    refine ⟨aeval f p₁ / aeval f t₁, aeval f⁻¹ q / aeval f⁻¹ s', fun k => r.coeff k,
      ⟨p₁, t₁, hp₁, ht₁, div_mul_cancel₀ _ ht₁0⟩, ⟨q, s', hq, hs', div_mul_cancel₀ _ hs'0⟩,
      fun k => hr k, ?_⟩
    rw [hxw, hdec, aeval_eq_sum_range' hrnat, Finset.sum_range]
    simp only [Algebra.smul_def]
    ring
  choose lp lm a hlp hlm ha hsplitσ using hsplit
  refine ⟨lp, lm, a, hlp, hlm, ha, ?_⟩
  rw [hsw, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, hsplitσ σ, add_mul, add_mul, Finset.sum_mul]
  refine congrArg₂ _ (congrArg₂ _ rfl (by ring)) (Finset.sum_congr rfl fun k _ => by ring)

end Main

end MultiplicativeNormalForm

theorem exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F) (m₀ : ℕ),
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
        (f⁻¹) ^ m₀ * z σ ∈ V) ∧
      ∀ (x s : F),
        (∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
          (∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) ∧
          x * aeval f t = aeval f p) →
        (∀ i, s ∈ (R i).integers) →
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V) →
        ∃ (lp lm : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F)
          (a : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → Fin m₀ → L),
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lp σ * aeval f t = aeval f p) ∧
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lm σ * aeval f⁻¹ t = aeval f⁻¹ p) ∧
          (∀ σ k, a σ k ∈ A) ∧
          x * s = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) +
            ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) :=
  MultiplicativeNormalForm.main R hR f hf htrL hfd htr heq

theorem forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    (∀ h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i},
      ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
        0 ≤ w.ord ((R i).residue ⟨f, hf i⟩) → 0 ≤ w.ord (h i)) ∧
    ∀ h : ∀ i, Fb i, ∃ c : Polynomial (IsLocalRing.ResidueField A), c.Monic ∧
      (fun i => Polynomial.aeval ((R i).residue ⟨f, hf i⟩) c * h i) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  refine ⟨fun h hh => ?_, fun h => ?_⟩
  · rcases isEmpty_or_nonempty ι with hι | hι
    · exact fun i => hι.elim i
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨u, huO, h₁, hres⟩ := hg
      intro i w hw
      have hint := isIntegral_residue_of_mem_T A Fb R hR f hf htr heq u h₁ huO i
      rw [← hres i]
      exact Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg w hint hw
    | zero => intro i w _; rw [Pi.zero_apply, Place.ord_zero]
    | add a b _ _ ha hb =>
      intro i w hw
      -- The port's `Place.min_ord_le_ord_add` (Defs/PlaceCalculus.lean) drops the pin's `f ≠ 0`
      -- and `g ≠ 0`, so the pin's two `eq_or_ne (a i) 0` / `eq_or_ne (b i) 0` splits go with them.
      rcases eq_or_ne (a i + b i) 0 with h0 | h0
      · rw [Pi.add_apply, h0, Place.ord_zero]
      exact (le_min (ha i w hw) (hb i w hw)).trans
        (by rw [Pi.add_apply]; exact Place.min_ord_le_ord_add w h0)
    | smul c a _ ha =>
      intro i w hw
      rcases eq_or_ne c 0 with rfl | hc
      · rw [zero_smul, Pi.zero_apply, Place.ord_zero]
      rw [Pi.smul_apply, Place.ord_smul_of_ne_zero w hc]
      exact ha i w hw
  · obtain ⟨z, hz⟩ := exists_forall_residue_eq A Fb R hR h
    have hzO : ∀ i, z ∈ (R i).integers := fun i => (hz i).choose
    have hzres : ∀ i, (R i).residue ⟨z, hzO i⟩ = h i := fun i => (hz i).choose_spec
    obtain ⟨q, hq0, hqT⟩ := ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem A f z
    set qbar : Polynomial (IsLocalRing.ResidueField A) := q.map (IsLocalRing.residue A) with hqbar
    have hqbar0 : qbar ≠ 0 := hq0
    set qf : F := Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q with hqf
    have hqfO : ∀ i, qf ∈ (R i).integers := fun i => eval₂_mem_integers' (R i) q f (hf i)
    have huO : ∀ i, qf * z ∈ (R i).integers := fun i => mul_mem (hqfO i) (hzO i)
    have hures : ∀ i, (R i).residue ⟨qf * z, huO i⟩ =
        Polynomial.aeval ((R i).residue ⟨f, hf i⟩) qbar * h i := by
      intro i
      have heq : (⟨qf * z, huO i⟩ : (R i).integers) = ⟨qf, hqfO i⟩ * ⟨z, hzO i⟩ := rfl
      rw [heq, map_mul, hzres i, hqbar]
      congr 1
      exact residue_eval₂' (R i) q f (hf i)

    have hmem : (fun i => Polynomial.aeval ((R i).residue ⟨f, hf i⟩) qbar * h i) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} :=
      Submodule.subset_span ⟨qf * z, huO, hqT, fun i => hures i⟩

    set lc := qbar.leadingCoeff with hlc
    have hlc0 : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hqbar0
    refine ⟨C lc⁻¹ * qbar, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact inv_mul_cancel₀ hlc0
    · have heq' : (fun i => aeval ((R i).residue ⟨f, hf i⟩) (C lc⁻¹ * qbar) * h i) =
          lc⁻¹ • (fun i => aeval ((R i).residue ⟨f, hf i⟩) qbar * h i) := by
        funext i
        rw [map_mul, aeval_C, Pi.smul_apply, Algebra.smul_def, mul_assoc]
      rw [heq']
      exact Submodule.smul_mem _ _ hmem

end RegularProlongation

end AlgebraicCurve
