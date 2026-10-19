window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Classical"] = {
  "module": "Init.Classical",
  "cards": {
    "Classical.propDecidable": {
      "seed": false,
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
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
