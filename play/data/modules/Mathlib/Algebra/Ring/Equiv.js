window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.Equiv"] = {
  "module": "Mathlib.Algebra.Ring.Equiv",
  "cards": {
    "RingEquiv": {
      "refs": [{"where":"type","name":"Add","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Mul","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":68,"column":0},"end":{"line":70,"column":95}},
      "name": "RingEquiv",
      "module": "Mathlib.Algebra.Ring.Equiv",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_7) → (S : Type u_8) → [Mul R] → [Mul S] → [Add R] → [Add S] → Type (max u_7 u_8)",
      "doc": "An equivalence between two (non-unital non-associative semi)rings that preserves the\nalgebraic structure. ",
      "short": "RingEquiv",
      "signature_source": "structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
