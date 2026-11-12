/-
  Consumer zone for `FLTForHuman/FieldTheory/ValuationSubringPolynomial.lean` (order AF44A).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`, and it is checked by
  `lake env lean spec/FieldTheorySetAF44AConsumer.lean` (it never enters the build).

  The module's two headlines are a *normalization* of a `∑ w i * z i` and a *constancy criterion* for
  multiplication by `aeval f t`, `aeval f⁻¹ t'`. Each is stated at a general `ι` resp. general `t`,
  `t'`, so each can be read at the smallest data that still fires it.

  * **Zone 1 — the constancy criterion on the rational function field.** `F = RatFunc L`,
    `f = RatFunc.X`, so the transcendence hypothesis is the pin's own `RatFunc.transcendental_X` and
    the `f` of the criterion is the generator. Three readings: the good-polynomial witness that makes
    the criterion's hypothesis `IsGood A t` inhabitable (`§1.1`); the criterion itself with its two
    membership families assumed (`§1.2`); and the criterion at `x = algebraMap a`, where *both*
    families are discharged from `f ∈ V` / `f⁻¹ ∈ V` and the returned constant is shown to be `a`
    itself (`§1.3`) — i.e. the criterion recovers the constant it started from.

  * **Zone 2 — the normalization at `ι = Fin 1`.** `Fin 1` has one index, so `∑ i, w i * z i` is the
    single term `w 0 * z 0` and the conclusion is read at the only index `0`. The `w i`-hypothesis is
    *fed* rather than assumed: at `w ≡ 1` it is discharged outright (`§2.1`, numerator and denominator
    both `1`), the sum collapses by `Fin.sum_univ_one` (`§2.2`), and the normalized quotient
    `p(f)/t(f) = 1` is read back as `t = p` by injectivity of `aeval f` (`§2.3`). Only the two deep
    hypotheses of the headline (`hzind`, the linear independence, and `hres`, the residue rewrite)
    stay assumed — they are the theorem's content, not its parameters.

  **Substitution recorded.** The order suggested reading the constancy criterion at `t = X` and
  `t' = X` *the polynomials*. That cannot be typed: the criterion's hypothesis on `t` is
  `A.valuation (t.coeff 0) = 1 ∧ ∀ j ≠ 0, A.valuation (t.coeff j) < 1`, whose first conjunct is
  `A.valuation ((X : L[X]).coeff 0) = A.valuation 0 = 0 ≠ 1` for *every* valuation subring `A` — no
  `t = X` is good. The replacement is the pin's own good shape `t = t' = 1 - C c * X` with
  `A.valuation c < 1` (pin `:84`, `IsGood.one_sub`), a linear polynomial with unit constant
  coefficient and one small coefficient, and the "concrete `X`" is kept where it belongs, as the
  *generator* `f = RatFunc.X` of the rational function field. Nothing else of the order's suggestion
  changes.
-/
import FLTForHuman.FieldTheory.ValuationSubringPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option autoImplicit false

noncomputable section

open Polynomial

namespace FieldTheorySetAF44AConsumer

/-! ## 1. The constancy criterion at `f = RatFunc.X` and `t = t' = 1 - C c * X` -/

section Constancy

variable {L : Type*} [Field L] (A : ValuationSubring L) {c : L}

/-- **§1.1.** `1 - C c * X` is a good polynomial as soon as `A.valuation c < 1`.

This is the criterion's hypothesis `IsGood A t`, obtained from the module's `IsGood.one_sub` (pin
`:84`) rather than assumed — the substitution for the untypeable `t = X` of the order. -/
theorem one_sub_coeff_conditions (hc : A.valuation c < 1) :
    A.valuation ((1 - C c * X : L[X]).coeff 0) = 1 ∧
      ∀ j, j ≠ 0 → A.valuation ((1 - C c * X : L[X]).coeff j) < 1 :=
  ValuationSubring.ZfSol.IsGood.one_sub A hc

variable [IsAlgClosed L]

/-- **§1.2.** The constancy criterion, read at `F = RatFunc L`, `f = RatFunc.X` and
`t = t' = 1 - C c * X`: if `x * (1 - c f)` lies in every valuation subring of `RatFunc L` containing
`L` and `f`, and `x * (1 - c f⁻¹)` in every one containing `L` and `f⁻¹`, then `x` is a constant
of `L`. -/
theorem constancy_at_ratFunc_X (hc : A.valuation c < 1) {x : RatFunc L}
    (hx : ∀ V : ValuationSubring (RatFunc L), (∀ d : L, algebraMap L (RatFunc L) d ∈ V) →
      RatFunc.X ∈ V → x * aeval RatFunc.X (1 - C c * X : L[X]) ∈ V)
    (hx' : ∀ V : ValuationSubring (RatFunc L), (∀ d : L, algebraMap L (RatFunc L) d ∈ V) →
      (RatFunc.X)⁻¹ ∈ V → x * aeval ((RatFunc.X)⁻¹) (1 - C c * X : L[X]) ∈ V) :
    ∃ c₀ : L, x = algebraMap L (RatFunc L) c₀ :=
  ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
    (A := A) (f := RatFunc.X) RatFunc.transcendental_X (1 - C c * X) (1 - C c * X)
    (one_sub_coeff_conditions A hc) (one_sub_coeff_conditions A hc) x hx hx'

/-- **§1.3.** The criterion at `x = algebraMap L (RatFunc L) a`, with *both* membership families
discharged: `V` contains `algebraMap a` and `1 - algebraMap c * f` (from `f ∈ V`), so it contains
their product, and likewise on the `f⁻¹` side. The constant the criterion returns is `a`. -/
theorem constancy_at_ratFunc_X_self (hc : A.valuation c < 1) (a : L) :
    ∃ c₀ : L, c₀ = a := by
  obtain ⟨c₀, hc₀⟩ :=
    constancy_at_ratFunc_X A hc (x := algebraMap L (RatFunc L) a)
      (fun V hV hf => by
        have h1 : aeval RatFunc.X (1 - C c * X : L[X]) =
            1 - algebraMap L (RatFunc L) c * RatFunc.X := by
          simp
        rw [h1]
        exact mul_mem (hV a) (sub_mem V.one_mem (mul_mem (hV c) hf)))
      (fun V hV hf => by
        have h1 : aeval ((RatFunc.X)⁻¹) (1 - C c * X : L[X]) =
            1 - algebraMap L (RatFunc L) c * (RatFunc.X)⁻¹ := by
          simp
        rw [h1]
        exact mul_mem (hV a) (sub_mem V.one_mem (mul_mem (hV c) hf)))
  exact ⟨c₀, (FaithfulSMul.algebraMap_injective L (RatFunc L) hc₀).symm⟩

end Constancy

/-! ## 2. The normalization at `ι = Fin 1`: the sum is a single term -/

section Normalization

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F] {f : F}

/-- **§2.1.** The normalization's `w i`-hypothesis at `w ≡ 1`, discharged: numerator `1` (coefficient-
wise in `A`) over denominator `1` (a `IsPrim` polynomial, unit at `0`). -/
theorem one_satisfies_w_hypothesis :
    ∀ _i : Fin 1, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
      ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
      (1 : F) * aeval f q = aeval f p := by
  intro _
  refine ⟨1, 1, ValuationSubring.ZfSol.ACoeff.one A,
    ⟨fun j => ValuationSubring.ZfSol.ACoeff.valuation_le A
      (ValuationSubring.ZfSol.ACoeff.one A) j, 0, ?_⟩, ?_⟩
  · simp
  · simp

variable [IsAlgClosed L]

/-- **§2.2.** The normalization's conclusion at `ι = Fin 1` for the single term `w ≡ 1`: the sum
`∑ i, w i * z i` collapses to `z 0`, the `w i`-hypothesis is `§2.1`, and the normalized form of the
only scalar is a quotient `p(f)/t(f)` with `p` coefficient-wise in `A` and `t` good. -/
theorem normalization_at_unit (hf : Transcendental L f) {z : Fin 1 → F}
    (hzT : ∀ i, ∀ V : ValuationSubring F, (∀ d : L, algebraMap L F d ∈ V) → f ∈ V → z i ∈ V)
    (hzind : LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z)
    (hres : ∀ (y : F) (w : Fin 1 → F),
      (∀ V : ValuationSubring F, (∀ d : L, algebraMap L F d ∈ V) → f ∈ V → y ∈ V) →
      (∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
        ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
        w i * aeval f q = aeval f p) →
      y = ∑ i, w i * z i →
      ∃ (C₁ : Fin 1 → L[X]) (μ : Fin 1 → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧
        (∀ i, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          μ i * aeval f q = aeval f p) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i) :
    ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
      (1 : F) = aeval f p / aeval f t := by
  have hs : z 0 = ∑ i : Fin 1, (fun _ => (1 : F)) i * z i := by
    rw [Fin.sum_univ_one]
    simp
  exact ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
    (A := A) hf z hzT hzind hres (z 0) (fun _ => 1) (hzT 0)
    (one_satisfies_w_hypothesis A) hs 0

/-- **§2.3.** Reading the normalized form back at `w ≡ 1`: `1 = p(f)/t(f)` forces `t = p`, because
`t` is good hence nonzero, so `aeval f t ≠ 0` and `aeval f` is injective at the transcendental `f`.
So the single-term normalization returns its quotient in lowest form, numerator equal to the good
denominator. -/
theorem normalization_at_unit_eq (hf : Transcendental L f) {z : Fin 1 → F}
    (hzT : ∀ i, ∀ V : ValuationSubring F, (∀ d : L, algebraMap L F d ∈ V) → f ∈ V → z i ∈ V)
    (hzind : LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z)
    (hres : ∀ (y : F) (w : Fin 1 → F),
      (∀ V : ValuationSubring F, (∀ d : L, algebraMap L F d ∈ V) → f ∈ V → y ∈ V) →
      (∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
        ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
        w i * aeval f q = aeval f p) →
      y = ∑ i, w i * z i →
      ∃ (C₁ : Fin 1 → L[X]) (μ : Fin 1 → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧
        (∀ i, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          μ i * aeval f q = aeval f p) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i) :
    ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
      t = p := by
  obtain ⟨p, t, hp, ht, hpt⟩ := normalization_at_unit A hf hzT hzind hres
  have htne : aeval f t ≠ 0 :=
    ValuationSubring.ZfSol.aeval_ne_zero_of_ne_zero hf
      (ValuationSubring.ZfSol.IsGood.ne_zero A ht)
  have haev : aeval f t = aeval f p := by
    rw [eq_div_iff htne] at hpt
    simpa using hpt
  exact ⟨p, t, hp, ht, ValuationSubring.ZfSol.aeval_injective hf haev⟩

end Normalization

end FieldTheorySetAF44AConsumer
