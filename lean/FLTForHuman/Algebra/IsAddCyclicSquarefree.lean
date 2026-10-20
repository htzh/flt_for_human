/-
  A finite additive group of squarefree cardinality is cyclic:

      `Squarefree (Nat.card A) → IsAddCyclic A`.

  The port of the pin leaf `IsAddCyclic.of_squarefree_natCard`
  (`Theorems/Thm_IsAddCyclic_of_squarefree_natCard.lean` and
  `P2M/Sol/S_IsAddCyclic_of_squarefree_natCard.lean`, pinned `aa2d8b3`; 14 pin
  lines). The statement is the wrapper's verbatim, the proof the `S_` file's
  `solution` body; the pin's `solution` wrapper is not ported.

  The mathematics is a two-step reduction: `Nat.finite_of_card_ne_zero` upgrades
  the hypothesis to `Finite A`, `isCyclic_multiplicative_iff` moves to
  `Multiplicative A`, and mathlib's `IsZGroup.of_squarefree` +
  `IsZGroup.exponent_eq_card` + `IsCyclic.of_exponent_eq_card` finish. The pin's
  `set_option autoImplicit false` is the module's; it carries no other option.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.
  Mathlib has the multiplicative form `IsZGroup.of_squarefree`
  (`Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:57`) and the bridge
  `isCyclic_multiplicative_iff`
  (`Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean:58`), but no additive
  squarefree-cardinality corollary: `rg "IsAddCyclic.of_squarefree|squarefree_natCard"
  Mathlib/` is empty (2026-10-20). So this is a supplement, transcribed as the pin
  states it rather than re-derived from a mathlib lemma of the same name.

  spec-pin: Theorems/Thm_IsAddCyclic_of_squarefree_natCard.lean
  spec-pin: P2M/Sol/S_IsAddCyclic_of_squarefree_natCard.lean
-/

import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false

theorem IsAddCyclic.of_squarefree_natCard
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by
  have : Finite A := Nat.finite_of_card_ne_zero hA.ne_zero
  rw [← isCyclic_multiplicative_iff]
  have hM : Squarefree (Nat.card (Multiplicative A)) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  have : IsZGroup (Multiplicative A) := IsZGroup.of_squarefree hM
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card (Multiplicative A))
