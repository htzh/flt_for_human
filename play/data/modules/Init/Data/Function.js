window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Function"] = {
  "module": "Init.Data.Function",
  "cards": {
    "Function.Injective": {
      "refs": [],
      "range": {"start":{"line":51,"column":0},"end":{"line":54,"column":34}},
      "name": "Function.Injective",
      "module": "Init.Data.Function",
      "kind": "def",
      "elaborated_type": "{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop",
      "doc": "A function `f : α → β` is called injective if `f x = f y` implies `x = y`. ",
      "short": "Injective",
      "signature_source": "@[expose]\ndef Injective (f : α → β) : Prop :=",
      "body_source": "∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Function.lean",
      "has_source": true,
      "has_refs": false
    },
    "Function.Surjective": {
      "refs": [],
      "range": {"start":{"line":59,"column":0},"end":{"line":63,"column":30}},
      "name": "Function.Surjective",
      "module": "Init.Data.Function",
      "kind": "def",
      "elaborated_type": "{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop",
      "doc": "A function `f : α → β` is called surjective if every `b : β` is equal to `f a`\nfor some `a : α`. ",
      "short": "Surjective",
      "signature_source": "@[expose]\ndef Surjective (f : α → β) : Prop :=",
      "body_source": "∀ b, Exists fun a => f a = b",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Function.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
