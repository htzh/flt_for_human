window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.Parity"] = {
  "module": "Mathlib.Algebra.Ring.Parity",
  "cards": {
    "Odd": {
      "refs": [{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":98,"column":0},"end":{"line":99,"column":44}},
      "name": "Odd",
      "module": "Mathlib.Algebra.Ring.Parity",
      "kind": "def",
      "elaborated_type": "{α : Type u_2} → [Semiring α] → α → Prop",
      "doc": "An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. ",
      "short": "Odd",
      "signature_source": "def Odd (a : α) : Prop :=",
      "body_source": "∃ k, a = 2 * k + 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Parity.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
