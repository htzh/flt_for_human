window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.IntermediateField.Basic"] = {
  "module": "Mathlib.FieldTheory.IntermediateField.Basic",
  "cards": {
    "IntermediateField": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":53,"column":41}},
      "name": "IntermediateField",
      "module": "Mathlib.FieldTheory.IntermediateField.Basic",
      "kind": "inductive",
      "elaborated_type": "(K : Type u_1) → (L : Type u_2) → [inst : Field K] → [inst_1 : Field L] → [Algebra K L] → Type u_2",
      "doc": "`S : IntermediateField K L` is a subset of `L` such that there is a field\ntower `L / S / K`. ",
      "short": "IntermediateField",
      "signature_source": "structure IntermediateField extends Subalgebra K L where\n  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "IntermediateField.algebra'": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"IntermediateField.module'","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"def"},{"where":"body","name":"RingHom.codRestrict","module":"Mathlib.Algebra.Ring.Subsemiring.Basic","kind":"def"},{"where":"body","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"}],
      "range": {"start":{"line":408,"column":0},"end":{"line":410,"column":45}},
      "name": "IntermediateField.algebra'",
      "module": "Mathlib.FieldTheory.IntermediateField.Basic",
      "kind": "def",
      "elaborated_type": "{R' : Type u_4} →\n  {K : Type u_5} →\n    {L : Type u_6} →\n      [inst : Field K] →\n        [inst_1 : Field L] →\n          [inst_2 : Algebra K L] →\n            (S : IntermediateField K L) →\n              [inst_3 : CommSemiring R'] →\n                [inst_4 : SMul R' K] → [inst_5 : Algebra R' L] → [IsScalarTower R' K L] → Algebra R' ↥S",
      "doc": "",
      "short": "algebra'",
      "signature_source": "instance algebra' {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)\n    [CommSemiring R'] [SMul R' K] [Algebra R' L] [IsScalarTower R' K L] : Algebra R' S :=",
      "body_source": "inferInstanceAs (Algebra R' S.toSubalgebra)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
