window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Core"] = {
  "module": "Init.Core",
  "cards": {
    "InvImage": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":1344,"column":0},"end":{"line":1349,"column":30}},
      "name": "InvImage",
      "module": "Init.Core",
      "kind": "def",
      "elaborated_type": "{α : Sort u} → {β : Sort v} → (β → β → Prop) → (α → β) → α → α → Prop",
      "doc": "The inverse image of `r : β → β → Prop` by a function `α → β` is the relation\n`s : α → α → Prop` defined by `s a b = r (f a) (f b)`.\n",
      "short": "InvImage",
      "signature_source": "@[implicit_reducible] def InvImage {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) : α → α → Prop :=",
      "body_source": "fun a₁ a₂ => r (f a₁) (f a₂)",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Core.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "Ne": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":871,"column":0},"end":{"line":876,"column":10}},
      "name": "Ne",
      "module": "Init.Core",
      "kind": "def",
      "elaborated_type": "{α : Sort u} → α → α → Prop",
      "doc": "`a ≠ b`, or `Ne a b` is defined as `¬ (a = b)` or `a = b → False`,\nand asserts that `a` and `b` are not equal.\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `≠` in identifiers is `ne`.",
      "short": "Ne",
      "signature_source": "@[reducible] def Ne {α : Sort u} (a b : α) :=",
      "body_source": "¬(a = b)",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Core.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
