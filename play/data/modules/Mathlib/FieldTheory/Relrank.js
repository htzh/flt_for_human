window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.Relrank"] = {
  "module": "Mathlib.FieldTheory.Relrank",
  "cards": {
    "IntermediateField.relfinrank": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Subfield.relfinrank","module":"Mathlib.FieldTheory.Relrank","kind":"def"}],
      "range": {"start":{"line":294,"column":0},"end":{"line":296,"column":68}},
      "name": "IntermediateField.relfinrank",
      "module": "Mathlib.FieldTheory.Relrank",
      "kind": "def",
      "elaborated_type": "{F : Type u} →\n  {E : Type v} →\n    [inst : Field F] → [inst_1 : Field E] → [inst_2 : Algebra F E] → IntermediateField F E → IntermediateField F E → ℕ",
      "doc": "The `Nat` version of `IntermediateField.relrank`.\nIf `B / A ⊓ B` is an infinite extension, then it is zero. ",
      "short": "relfinrank",
      "signature_source": "noncomputable def relfinrank :=",
      "body_source": "A.toSubfield.relfinrank B.toSubfield",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean",
      "has_source": true,
      "has_refs": true
    },
    "Subfield.relfinrank": {
      "refs": [{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Subfield","module":"Mathlib.Algebra.Field.Subfield.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"body","name":"IntermediateField.module'","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"def"},{"where":"body","name":"Module.finrank","module":"Mathlib.LinearAlgebra.Dimension.Finrank","kind":"def"},{"where":"body","name":"Subfield.extendScalars","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"def"},{"where":"body","name":"Min.min","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":47,"column":0},"end":{"line":49,"column":91}},
      "name": "Subfield.relfinrank",
      "module": "Mathlib.FieldTheory.Relrank",
      "kind": "def",
      "elaborated_type": "{E : Type v} → [inst : Field E] → Subfield E → Subfield E → ℕ",
      "doc": "The `Nat` version of `Subfield.relrank`.\nIf `B / A ⊓ B` is an infinite extension, then it is zero. ",
      "short": "relfinrank",
      "signature_source": "noncomputable def relfinrank :=",
      "body_source": "finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
