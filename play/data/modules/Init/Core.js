window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Core"] = {
  "module": "Init.Core",
  "cards": {
    "Eq.mpr": {
      "refs": [{"where":"body","name":"Eq.symm","module":"Init.Prelude","kind":"theorem"}],
      "range": {"start":{"line":854,"column":0},"end":{"line":862,"column":7}},
      "name": "Eq.mpr",
      "module": "Init.Core",
      "kind": "def",
      "elaborated_type": "{α β : Sort u} → α = β → β → α",
      "doc": "If `h : α = β` is a proof of type equality, then `h.mpr : β → α` is the induced\n\"cast\" operation in the reverse direction, mapping elements of `β` to elements of `α`.\n\nYou can prove theorems about the resulting element by induction on `h`, since\n`rfl.mpr` is definitionally the identity function.\n",
      "short": "mpr",
      "signature_source": "@[macro_inline] def Eq.mpr {α β : Sort u} (h : α = β) (b : β) : α :=",
      "body_source": "h ▸ b",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Core.lean",
      "has_source": true,
      "has_refs": true
    },
    "InvImage": {
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
      "has_refs": false
    },
    "Ne": {
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
      "has_refs": false
    },
    "Subsingleton": {
      "refs": [],
      "range": {"start":{"line":1256,"column":0},"end":{"line":1267,"column":27}},
      "name": "Subsingleton",
      "module": "Init.Core",
      "kind": "inductive",
      "elaborated_type": "Sort u → Prop",
      "doc": "A _subsingleton_ is a type with at most one element. It is either empty or has a unique element.\n\nAll propositions are subsingletons because of proof irrelevance: false propositions are empty, and\nall proofs of a true proposition are equal to one another. Some non-propositional types are also\nsubsingletons.\n",
      "short": "Subsingleton",
      "signature_source": "class Subsingleton (α : Sort u) : Prop where\n  /-- Prove that `α` is a subsingleton by showing that any two elements are equal. -/\n  intro ::\n  /-- Any two elements of a subsingleton are equal. -/\n  allEq : (a b : α) → a = b",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Core.lean",
      "has_source": true,
      "has_refs": false
    },
    "Subtype.ext": {
      "refs": [],
      "range": {"start":{"line":1380,"column":0},"end":{"line":1381,"column":30}},
      "name": "Subtype.ext",
      "module": "Init.Core",
      "kind": "theorem",
      "elaborated_type": "∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 = ↑a2 → a1 = a2",
      "doc": "",
      "short": "ext",
      "signature_source": "protected theorem ext : ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2\n  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Core.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
