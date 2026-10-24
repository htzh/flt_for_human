window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Nat.Prime.Defs"] = {
  "module": "Mathlib.Data.Nat.Prime.Defs",
  "cards": {
    "Nat.Prime": {
      "refs": [{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Irreducible","module":"Mathlib.Algebra.Group.Irreducible.Defs","kind":"inductive"}],
      "range": {"start":{"line":38,"column":0},"end":{"line":43,"column":15}},
      "name": "Nat.Prime",
      "module": "Mathlib.Data.Nat.Prime.Defs",
      "kind": "def",
      "elaborated_type": "ℕ → Prop",
      "doc": "`Nat.Prime p` means that `p` is a prime number, that is, a natural number\nat least 2 whose only divisors are `p` and `1`.\nThe theorem `Nat.prime_def` witnesses this description of a prime number. ",
      "short": "Prime",
      "signature_source": "@[pp_nodot, wikidata Q49008]\ndef Prime (p : ℕ) :=",
      "body_source": "Irreducible p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Nat/Prime/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
