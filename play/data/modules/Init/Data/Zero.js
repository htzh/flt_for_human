window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Zero"] = {
  "module": "Init.Data.Zero",
  "cards": {
    "Zero.ofOfNat0": {
      "refs": [{"where":"type","name":"OfNat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":20,"column":0},"end":{"line":21,"column":11}},
      "name": "Zero.ofOfNat0",
      "module": "Init.Data.Zero",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → [OfNat α 0] → Zero α",
      "doc": "",
      "short": "ofOfNat0",
      "signature_source": "instance (priority := 200) Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where\n  zero := 0",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Zero.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
