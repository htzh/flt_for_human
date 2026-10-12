/-
  Countability of the cofinite filter's sets.

  For a countable index type `ι`, the sets of the cofinite filter `Filter.cofinite`
  are countable (`Filter.cofinite.sets.countable`), and `Countable (cofinite).sets`
  is an instance. This is the index set of the countable open cover in
  `TopologicalSpace.secondCountableTopology_of_countable_cover'` and hence of
  `RestrictedProduct.secondCountableTopology`.

  Transcribed verbatim from `Definitions/Def_Mathlib_Order_Filter_Cofinite.lean`
  (pinned `aa2d8b3`, 12 lines / 2 declarations), with one proof-level deprecation fix
  (`Set.Countable.setOf_finite` → `Set.Countable.ofPred_finite`). A mathlib gap:
  mathlib `v4.34.0` has neither declaration (its `Filter.cofinite` API has no
  `sets`-countability lemma), so both are residue rather than substitutions. The pin's
  `import Mathlib` is replaced by the specific sources; the pin's `Filter.cofinite.sets`
  namespace is kept for checker fidelity.
-/
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Set.Countable

set_option autoImplicit false

section

lemma Filter.cofinite.sets.countable (ι : Type*) [Countable ι] :
    (Filter.cofinite : Filter ι).sets.Countable :=
  Set.Countable.mono (fun _ h ↦ h) <|
  Set.Countable.preimage_of_injOn Set.Countable.ofPred_finite compl_bijective.1.injOn

instance (ι : Type*) [Countable ι] : Countable (.cofinite : Filter ι).sets := by
  rw [Set.countable_coe_iff]
  exact Filter.cofinite.sets.countable ι

end
