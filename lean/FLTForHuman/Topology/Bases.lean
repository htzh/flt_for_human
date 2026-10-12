/-
  Second countability from a countable cover by open embeddings.

  `TopologicalSpace.secondCountableTopology_of_countable_cover'` is the
  type-indexed form of mathlib's `secondCountableTopology_of_countable_cover`: a
  countable family of open embeddings `f i : U i → α` covering `α` makes `α` second
  countable when each `U i` is. This is the glue used by
  `RestrictedProduct.secondCountableTopology`, where the cover is the family of
  principal inclusions.

  Transcribed verbatim from `Definitions/Def_Mathlib_Topology_Bases.lean` (pinned
  `aa2d8b3`, 16 lines / 1 declaration), with one proof-level drift adaptation:
  `v4.34.0` moved the homeomorphism of an embedding from
  `IsOpenEmbedding.toHomeomorph` to `IsEmbedding.toHomeomorph`
  (`Mathlib.Topology.Homeomorph.Lemmas`), so the proof writes
  `(hf i).toIsEmbedding.toHomeomorph`. A mathlib gap: `v4.34.0` has only the
  set-indexed `secondCountableTopology_of_countable_cover` (`U : ι → Set α`), not
  this type-indexed `'` variant, so it is residue rather than a substitution. The
  pin's `import Mathlib` is replaced by `Mathlib.Topology.Bases`.
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

section

lemma TopologicalSpace.secondCountableTopology_of_countable_cover' {α : Type*}
    [TopologicalSpace α] {ι : Sort*} [Countable ι] {U : ι → Type*} [∀ i, TopologicalSpace (U i)]
    [∀ (i : ι), SecondCountableTopology (U i)]
    (f : ∀ i, U i → α) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hc : ∀ a, ∃ (i : ι) (u : U i), f i u = a) : SecondCountableTopology α :=
  let V i := Set.range (f i)
  have (i : ι) : SecondCountableTopology (V i) :=
    (hf i).toIsEmbedding.toHomeomorph.symm.secondCountableTopology
  have Vo (i : ι) : IsOpen (V i) := (hf i).isOpen_range
  have hV : ⋃ i, V i = Set.univ := Set.eq_univ_of_forall fun a =>
    (hc a).elim fun i hi => Set.mem_iUnion_of_mem i (Set.mem_range.2 hi)
  secondCountableTopology_of_countable_cover Vo hV

end
