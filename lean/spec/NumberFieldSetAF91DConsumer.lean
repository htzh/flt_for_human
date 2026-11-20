/-
  SET-AF91D consumer: the box-counting finset and the finiteness of the points it covers.

  **The row.** `FLTForHuman/NumberTheory/AdelicLevel/LatticeCounting.lean` carries
  `NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact`: for a
  compact set `B` of finite adèles there is `M` such that every box `(R w)` admits a finset of
  algebraic integers covering the `k` with `(algebraMap k - a).2 ∈ B` and archimedean components
  bounded by `R`, with `card ≤ M · ∏ max 1 (R w) ^ w.mult`.

  **The reading.** The covering finset is paired with the finiteness of the covered set (the
  `Set.Finite` follows from the finset), which is the form the box arguments use when they sum over
  the lattice points and then bound the number of terms.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF91DConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.AdelicLevel.LatticeCounting

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm Matrix NumberField.StandardAddChar

namespace NumberFieldSetAF91DConsumer

/-- **The reading.** The counting finset, its cardinality bound, and the finiteness of the set of
points it covers. -/
theorem exists_finset_and_finite_of_isCompact
    (K : Type) [Field K] [NumberField K]
    {B : Set (FiniteAdeleRing (𝓞 K) K)} (hB : IsCompact B) :
    ∃ M : ℝ, ∀ (a : AdeleRing (𝓞 K) K) (R : InfinitePlace K → ℝ),
      ∃ s : Finset K,
        (∀ k : K, (algebraMap K (AdeleRing (𝓞 K) K) k - a).2 ∈ B →
          (∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w) → k ∈ s) ∧
        (s.card : ℝ) ≤ M * ∏ w : InfinitePlace K, max 1 (R w) ^ w.mult ∧
        ({k : K | (algebraMap K (AdeleRing (𝓞 K) K) k - a).2 ∈ B ∧
          ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w}.Finite) := by
  obtain ⟨M, hM⟩ := AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact K hB
  refine ⟨M, fun a R => ?_⟩
  obtain ⟨s, hs, hcard⟩ := hM a R
  exact ⟨s, hs, hcard, s.finite_toSet.subset (fun k hk => hs k hk.1 hk.2)⟩

end NumberFieldSetAF91DConsumer
