/-
  SET-AF44B consumer: partial fractions at infinity, and strong approximation.

  **The zone.** Two independent rows, hence two compositions.

  Row 2 (`exists_aeval_div_eq_aeval_div_add_aeval_inv_div`) decomposes `aeval f p / aeval f t` into
  a polynomial-in-`f` part `aeval f p₁ / aeval f t₁` and a polynomial-in-`f⁻¹` part
  `aeval f⁻¹ q / aeval f⁻¹ s`, with both numerators coefficient-wise in `A` and both denominators
  units at `0` with small higher coefficients. The order asked for this at `t = 1 + X`; a literal
  `1 + X` cannot be typed against the hypothesis — `(1 + X).coeff 1 = 1` has valuation `1`, never
  `< 1`, and no valuation subring of a field can make `1` small. The substitution recorded here is
  `t = 1 + C c * X` with `A.valuation c < 1`: the smallest instance of "unit at `0` with small
  higher coefficients", and the honest reading of `1 + X` with a small `X`-coefficient.

  The composition reads the conclusion twice. First, the `f⁻¹`-side denominator `s` is *again* of the
  same form: it is `IsGood`, so it re-satisfies the headline's hypothesis with `d = 0` — the
  decomposition can be iterated on the `f⁻¹` chart. Second, both denominators are non-zero at the
  transcendental point (`aeval_ne_zero_of_isGood`), so each fraction cancels against its own
  denominator.

  Row 4 (`exists_forall_mem_and_sub_mem_nonunits`) produces one `z` that is integral in every `R i`
  and congruent to `a i` modulo the non-units of `R i`. Composed at `ι = Fin 1` it is the
  single-ring statement read in the order: `z ∈ R 0`, `z - a 0 ∈ (R 0).nonunits`, and — through
  `ValuationSubring.mem_nonunits_iff` — `(R 0).valuation (z - a 0) < 1`.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.FieldTheory.ValuationSubringPartialFraction
import FLTForHuman.FieldTheory.ValuationSubringApproximation

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ValuationSubring

namespace P1aSol

/-- **Zone B.** The row-2 decomposition read at `t = 1 + C c * X` (`A.valuation c < 1`): the
`f⁻¹`-side denominator is again of that form (`IsGood`, hence a witness for the headline's
hypothesis with `d = 0`), and both denominators invert at the transcendental point. -/
theorem consumer_zoneB_partialFraction_div {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F] {f : F}
    (hf : Transcendental L f) (p : L[X]) (hp : ACoeff A p) {c : L} (hc : A.valuation c < 1) :
    ∃ p₁ t₁ q s : L[X],
      ACoeff A p₁ ∧ ACoeff A q ∧ IsGood A t₁ ∧ IsGood A s ∧
      aeval f p / aeval f (1 + C c * X) = aeval f p₁ / aeval f t₁ + aeval f⁻¹ q / aeval f⁻¹ s ∧
      (∃ d, A.valuation (t₁.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t₁.coeff j) < 1) ∧
      (∃ d, A.valuation (s.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (s.coeff j) < 1) ∧
      aeval f⁻¹ q / aeval f⁻¹ s * aeval f⁻¹ s = aeval f⁻¹ q ∧
      aeval f p₁ / aeval f t₁ * aeval f t₁ = aeval f p₁ := by
  have hc' : A.valuation (-c) < 1 := by rwa [Valuation.map_neg]
  have hpoly : (1 - C (-c) * X : L[X]) = 1 + C c * X := by rw [map_neg]; ring
  have hgood : IsGood A (1 + C c * X : L[X]) := by
    rw [← hpoly]
    exact IsGood.one_sub A hc'
  obtain ⟨p₁, t₁, q, s, hp₁, hq, ht₁, hs, hdec⟩ :=
    exists_aeval_div_eq_aeval_div_add_aeval_inv_div A hf p (1 + C c * X : L[X]) hp
      ⟨0, hgood.1, fun j hj => hgood.2 j hj⟩
  have hfi : Transcendental L f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  exact ⟨p₁, t₁, q, s, hp₁, hq, ht₁, hs, hdec, ⟨0, ht₁.1, fun j hj => ht₁.2 j hj⟩,
    ⟨0, hs.1, fun j hj => hs.2 j hj⟩,
    div_mul_cancel₀ _ (aeval_ne_zero_of_isGood A hfi hs),
    div_mul_cancel₀ _ (aeval_ne_zero_of_isGood A hf ht₁)⟩

end P1aSol

/-- **Zone C.** The row-4 approximation read at `ι = Fin 1`: one `z`, integral in `R 0` and
congruent to `a 0` modulo `(R 0).nonunits`, with the non-unit condition unfolded to the valuation
inequality. -/
theorem consumer_zoneC_approximation_fin_one {K : Type*} [Field K]
    (R : Fin 1 → ValuationSubring K) (hR : ∀ i j, R i ≤ R j → i = j)
    (a : Fin 1 → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, z ∈ R 0 ∧ z - a 0 ∈ (R 0).nonunits ∧ (R 0).valuation (z - a 0) < 1 ∧
      ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by
  obtain ⟨z, hz⟩ := exists_forall_mem_and_sub_mem_nonunits R hR a ha
  exact ⟨z, (hz 0).1, (hz 0).2, (mem_nonunits_iff (R 0)).mp (hz 0).2, hz⟩

end ValuationSubring
