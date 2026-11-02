window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.IntermediateField.Adjoin.Defs"] = {
  "module": "Mathlib.FieldTheory.IntermediateField.Adjoin.Defs",
  "cards": {
    "IntermediateField.adjoin": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"Set.range","module":"Mathlib.Data.Set.Operations","kind":"def"},{"where":"body","name":"Subfield","module":"Mathlib.Algebra.Field.Subfield.Defs","kind":"inductive"},{"where":"body","name":"Subfield.closure","module":"Mathlib.Algebra.Field.Subfield.Basic","kind":"def"}],
      "range": {"start":{"line":32,"column":0},"end":{"line":36,"column":89}},
      "name": "IntermediateField.adjoin",
      "module": "Mathlib.FieldTheory.IntermediateField.Adjoin.Defs",
      "kind": "def",
      "elaborated_type": "(F : Type u_1) →\n  [inst : Field F] → {E : Type u_2} → [inst_1 : Field E] → [inst_2 : Algebra F E] → Set E → IntermediateField F E",
      "doc": "`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. ",
      "short": "adjoin",
      "signature_source": "@[stacks 09FZ \"first part\"]\ndef adjoin : IntermediateField F E :=",
      "body_source": "{ Subfield.closure (Set.range (algebraMap F E) ∪ S) with\n    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
