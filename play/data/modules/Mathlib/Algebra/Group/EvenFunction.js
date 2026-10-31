window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.EvenFunction"] = {
  "module": "Mathlib.Algebra.Group.EvenFunction",
  "cards": {
    "Function.Odd": {
      "refs": [{"where":"type","name":"Neg","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":34,"column":0},"end":{"line":35,"column":68}},
      "name": "Function.Odd",
      "module": "Mathlib.Algebra.Group.EvenFunction",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → {β : Type u_2} → [Neg α] → [Neg β] → (α → β) → Prop",
      "doc": "A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`. ",
      "short": "Odd",
      "signature_source": "protected def Odd [Neg β] (f : α → β) : Prop :=",
      "body_source": "∀ a, f (-a) = -(f a)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/EvenFunction.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
