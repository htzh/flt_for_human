/-
  Cross-module wire test for the degree identity `deg (x)_∞ = [F : K(x)]`.

  The set is four statements in two new modules:

  * `AlgebraicCurve/Place/Approximation.lean` — weak approximation at finitely many
    places (`Place.exists_forall_ord_eq`);
  * `AlgebraicCurve/Genus/DegreeIdentity.lean` — the two Riemann–Roch counts
    (`Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord`,
    `Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord`) and their `le_antisymm`
    (`Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord`).

  A `spec/` probe, not a library module: it is outside every lake target and is run with
  `lake env lean`, so a green library build stays meaningful.  Deleting either module
  breaks it.

  Executed zones (each a real composition, no `#check`, no unfinished proof):

  * zone 1 — **the approximation at the orders of an indicator**: the element which is a
    uniformizer at one place of a finite set and a unit at all the others, which is what
    the upper bound consumes (`exists_ord_one_at_and_zero_elsewhere`);
  * zone 2 — **the identity applied at a hypothesis-form `IsCurveOver` package**, reading
    off both inequalities and the equality from the same hypotheses;
  * zone 3 — **the identity substituted into Riemann's inequality**: `ℓ(D) ≤ [F : K(x)] +
    ℓ(0)` for the pole divisor of `x`, composing the equality with the landed
    `AlgebraicCurve.ell_le_degree_add_ellZero` (`Genus/Index.lean`).

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, the four `Theorems/Thm_AlgebraicCurve_*`
  wrappers the two modules carry.
-/
import FLTForHuman.AlgebraicCurve.Genus.DegreeIdentity
import FLTForHuman.AlgebraicCurve.Place.Approximation

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace DegreeIdentityConsumer

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

omit [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))] in
/-- **Zone 1.** Weak approximation at the indicator of a place: an element which is a
uniformizer at `v` and a unit at every other place of `T`. -/
theorem exists_ord_one_at_and_zero_elsewhere {v : Place K F} (T : Finset (Place K F))
    (hv : v ∈ T) :
    ∃ t : F, t ≠ 0 ∧ v.ord t = 1 ∧ ∀ w ∈ T, w ≠ v → w.ord t = 0 := by
  classical
  obtain ⟨t, ht0, htord⟩ := Place.exists_forall_ord_eq T (fun w => if w = v then 1 else 0)
  exact ⟨t, ht0, by simpa using htord v hv, fun w hw hne => by simpa [hne] using htord w hw⟩

/-- **Zone 2.** The identity at a hypothesis-form curve package: both inequalities and the
equality, from the same hypotheses. -/
theorem degree_eq_and_inequalities
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) ≤ Divisor.degree D ∧
      Divisor.degree D ≤ (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) ∧
      Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) :=
  ⟨Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord x hx D hD,
    Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord x hx D hD,
    Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx D hD⟩

/-- **Zone 3.** Riemann's inequality at the pole divisor of `x`, with the degree identity
substituted: `ℓ(D) ≤ [F : K(x)] + ℓ(0)`. -/
theorem ell_le_finrank_add_ellZero
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    (ell D : ℤ) ≤ (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ)
      + ell (0 : Divisor K F) := by
  have hDeff : ∀ v : Place K F, 0 ≤ D v := by
    intro v; rw [hD]; exact le_max_left 0 _
  have h := ell_le_degree_add_ellZero (K := K) (F := F) hDeff
  rwa [Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx D hD] at h

end DegreeIdentityConsumer
