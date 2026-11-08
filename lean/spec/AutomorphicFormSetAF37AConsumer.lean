/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/InducedSectionBorelIndicator.lean`.

  The headline is exercised in composition, never by `#check`. Its five conjuncts are read through
  the two modules the row is built above, and every step below deletes one of them if removed:

  * the `let α` of the headline is named `alphaOf`, and the `hα` it asks for is discharged from
    `distribHaarChar_pos` (`Mathlib.MeasureTheory.Measure.Haar.DistribChar`), so every composition
    below is at the headline's own character and not at a lookalike;
  * `phi0_empty_eq_flatOne`: at `S = ∅` the indicator condition is vacuous and the new section
    degenerates to the *imported* `FlatInducedSection.flatOne` of
    `AutomorphicForm/Adelic/InducedSectionFlat.lean` (the pin's height/`flatOne` prelude). Its
    pointwise form identifies it with the pin's own `((adelicHeight K g : ℝ) : ℂ) ^ (s + 1/2)`;
  * `isInducedSection_phi0_empty`: conjunct 1 at `S = ∅`, transported along that degeneration —
    i.e. the new headline *implies* the ported flat-section headline
    (`isInducedSection_adelicHeight_cpow`) at the empty set of places. This is the comparison the
    order asks for: the two `IsInducedSection` statements are the same section there;
  * `phi0_empty_apply_one`: the normalization `φ₀ 1 = 1` re-derived from the `S = ∅` degeneration
    plus the prelude's `flatOne_apply_one` — a second route to `phi0_one`;
  * `phi0_one_dichotomy`: the `0/1` law (conjunct 4) at the identity, decided by the normalization
    `phi0_one`, so the `1` of that dichotomy is pinned by the section's value at `1`;
  * `isArchKFinite_flatOne_from_phi0`: the archimedean-`K`-finiteness conjunct at `S = ∅`, giving
    the prelude's `isArchKFinite_flatOne` back through `phi0`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF37AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionBorelIndicator

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.BorelIndicator AutomorphicForm.FlatInducedSection
open AutomorphicForm.WindowedSiegel
open scoped NNReal Classical

namespace AutomorphicFormSetAF37AConsumer

variable {K : Type} [Field K] [NumberField K]

/-- The headline's `let α`, named so that the zone can instantiate it concretely. -/
def alphaOf : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
    (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits

/-- The positivity the headline asks of `alphaOf`, discharged from `distribHaarChar_pos`. -/
theorem alphaOf_pos : ∀ x, 0 < ((alphaOf (K := K) x : ℝˣ) : ℝ) := fun x => by
  show (0 : ℝ) < ((distribHaarChar (AdeleRing (𝓞 K) K) x : ℝ≥0) : ℝ)
  exact NNReal.coe_pos.mpr (distribHaarChar_pos (A := (AdeleRing (𝓞 K) K)) (g := x))

/-- At `S = ∅` the bottom-row condition is vacuous, so the indicator section is the pin's
`flatOne` — the imported `FlatInducedSection.flatOne`, not a copy of it. -/
theorem phi0_empty_eq_flatOne (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ) :
    BorelIndicator.phi0 (∅ : Finset (HeightOneSpectrum (𝓞 K))) n s
      = FlatInducedSection.flatOne K s := by
  funext g
  exact BorelIndicator.phi0_of_cond ∅ n s (by intro v hv; simp at hv)

/-- The same degeneration read at the pin's own height power: at `S = ∅` the section is
`g ↦ (adelicHeight K g : ℂ) ^ (s + 1/2)`. -/
theorem phi0_empty_apply (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ)
    (g : AdelicGL2 (𝓞 K) K) :
    BorelIndicator.phi0 (∅ : Finset (HeightOneSpectrum (𝓞 K))) n s g
      = ((adelicHeight K g : ℝ) : ℂ) ^ (s + 1 / 2) := by
  rw [phi0_empty_eq_flatOne]
  rfl

/-- Conjunct 1 at `S = ∅`: the new headline's induced-section law, transported along the
degeneration, is the ported flat-section headline — here at the imported `flatOne` itself, so the
two `IsInducedSection` statements are the same section at the empty set of places. -/
theorem isInducedSection_phi0_empty (hα : ∀ x, 0 < ((alphaOf (K := K) x : ℝˣ) : ℝ)) (s : ℂ)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    IsInducedSection (𝓞 K) K (etaFst 1 (alphaOf (K := K)) hα s)
      (etaSnd 1 (alphaOf (K := K)) hα s) (FlatInducedSection.flatOne K s) := by
  have h := (isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow K hα s
    (∅ : Finset (HeightOneSpectrum (𝓞 K))) n (by intro v hv; simp at hv)).1
  have h' : IsInducedSection (𝓞 K) K (etaFst 1 (alphaOf (K := K)) hα s)
      (etaSnd 1 (alphaOf (K := K)) hα s)
      (BorelIndicator.phi0 (∅ : Finset (HeightOneSpectrum (𝓞 K))) n s) := h
  rwa [phi0_empty_eq_flatOne] at h'

/-- The normalization, re-derived from the `S = ∅` degeneration and the prelude's
`flatOne_apply_one` (a second route to the module's own `phi0_one`). -/
theorem phi0_empty_apply_one (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ) :
    BorelIndicator.phi0 (∅ : Finset (HeightOneSpectrum (𝓞 K))) n s 1 = 1 := by
  rw [phi0_empty_eq_flatOne, FlatInducedSection.flatOne_apply_one]

/-- The `0/1` law (conjunct 4) at the identity, decided by the normalization: the disjunction the
headline states at an integral archimedean-row-isometry element is forced to the `1` branch by
`phi0_one`. -/
theorem phi0_one_dichotomy (hα : ∀ x, 0 < ((alphaOf (K := K) x : ℝˣ) : ℝ)) (s : ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
    (hn : ∀ v ∈ S, 0 < n v) :
    BorelIndicator.phi0 S n s (1 : AdelicGL2 (𝓞 K) K) = 1 := by
  have h := (isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow K hα s S n hn).2.2.2.2.2.2.2.1
    (1 : AdelicGL2 (𝓞 K) K) (by rw [map_one]; exact one_mem _) (by
      intro w
      rw [map_one, map_one]
      exact isRowIsometry_one)
  rcases h with h0 | h1
  · have h0' : BorelIndicator.phi0 S n s (1 : AdelicGL2 (𝓞 K) K) = 0 := h0
    rw [BorelIndicator.phi0_one S n s] at h0'
    exact absurd h0' one_ne_zero
  · exact h1

/-- `IsArchKFinite` (conjunct 3) at `S = ∅`: the prelude's `isArchKFinite_flatOne` recovered
through `phi0`, so the new module's archimedean conjunct is not vacuous at the degeneration. -/
theorem isArchKFinite_flatOne_from_phi0 (s : ℂ) :
    IsArchKFinite K (FlatInducedSection.flatOne K s) := by
  have h := BorelIndicator.isArchKFinite_phi0 (∅ : Finset (HeightOneSpectrum (𝓞 K)))
    (fun _ => 0) s
  rwa [phi0_empty_eq_flatOne] at h

end AutomorphicFormSetAF37AConsumer
