window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Equiv.Defs"] = {
  "module": "Mathlib.Algebra.Group.Equiv.Defs",
  "cards": {
    "AddEquiv": {
      "refs": [{"where":"type","name":"Add","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":57,"column":0},"end":{"line":58,"column":74}},
      "name": "AddEquiv",
      "module": "Mathlib.Algebra.Group.Equiv.Defs",
      "kind": "inductive",
      "elaborated_type": "(A : Type u_9) → (B : Type u_10) → [Add A] → [Add B] → Type (max u_10 u_9)",
      "doc": "`AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition. ",
      "short": "AddEquiv",
      "signature_source": "structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Equiv/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
