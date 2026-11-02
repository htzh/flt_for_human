window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Basic.ExistsUnique"] = {
  "module": "Mathlib.Basic.ExistsUnique",
  "cards": {
    "ExistsUnique": {
      "refs": [],
      "range": {"start":{"line":21,"column":0},"end":{"line":22,"column":62}},
      "name": "ExistsUnique",
      "module": "Mathlib.Basic.ExistsUnique",
      "kind": "def",
      "elaborated_type": "{α : Sort u_1} → (α → Prop) → Prop",
      "doc": "For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` with `p x`. ",
      "short": "ExistsUnique",
      "signature_source": "def ExistsUnique (p : α → Prop) :=",
      "body_source": "∃ x, p x ∧ ∀ y, p y → y = x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Basic/ExistsUnique.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
