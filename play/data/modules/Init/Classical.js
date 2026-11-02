window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Classical"] = {
  "module": "Init.Classical",
  "cards": {
    "Classical.choose": {
      "refs": [{"where":"body","name":"Classical.indefiniteDescription","module":"Init.Classical","kind":"def"}],
      "range": {"start":{"line":22,"column":0},"end":{"line":30,"column":33}},
      "name": "Classical.choose",
      "module": "Init.Classical",
      "kind": "def",
      "elaborated_type": "{α : Sort u} → {p : α → Prop} → (∃ x, p x) → α",
      "doc": "Given that there exists an element satisfying `p`, returns one such element.\n\nThis is a straightforward consequence of, and equivalent to, `Classical.choice`.\n\nSee also `choose_spec`, which asserts that the returned value has property `p`.\n",
      "short": "choose",
      "signature_source": "noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=",
      "body_source": "(indefiniteDescription p h).val",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Classical.lean",
      "has_source": true,
      "has_refs": true
    },
    "Classical.indefiniteDescription": {
      "refs": [],
      "range": {"start":{"line":19,"column":0},"end":{"line":20,"column":39}},
      "name": "Classical.indefiniteDescription",
      "module": "Init.Classical",
      "kind": "def",
      "elaborated_type": "{α : Sort u} → (p : α → Prop) → (∃ x, p x) → { x // p x }",
      "doc": "",
      "short": "indefiniteDescription",
      "signature_source": "noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=",
      "body_source": "choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Classical.lean",
      "has_source": true,
      "has_refs": false
    },
    "Classical.propDecidable": {
      "refs": [],
      "range": {"start":{"line":80,"column":0},"end":{"line":84,"column":29}},
      "name": "Classical.propDecidable",
      "module": "Init.Classical",
      "kind": "def",
      "elaborated_type": "(a : Prop) → Decidable a",
      "doc": "All propositions are `Decidable`. ",
      "short": "propDecidable",
      "signature_source": "noncomputable scoped instance (priority := low) propDecidable (a : Prop) : Decidable a :=",
      "body_source": "choice <| match em a with\n    | Or.inl h => ⟨isTrue h⟩\n    | Or.inr h => ⟨isFalse h⟩",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Classical.lean",
      "has_source": true,
      "has_refs": false
    },
    "Exists.choose": {
      "refs": [{"where":"body","name":"Classical.choose","module":"Init.Classical","kind":"def"}],
      "range": {"start":{"line":206,"column":0},"end":{"line":208,"column":100}},
      "name": "Exists.choose",
      "module": "Init.Classical",
      "kind": "def",
      "elaborated_type": "{α : Sort u_1} → {p : α → Prop} → (∃ a, p a) → α",
      "doc": "Extract an element from an existential statement, using `Classical.choose`. ",
      "short": "choose",
      "signature_source": "-- This enables projection notation.\n@[reducible] noncomputable def Exists.choose {p : α → Prop} (P : ∃ a, p a) : α :=",
      "body_source": "Classical.choose P",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Classical.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
