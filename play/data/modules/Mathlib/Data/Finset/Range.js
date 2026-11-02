window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finset.Range"] = {
  "module": "Mathlib.Data.Finset.Range",
  "cards": {
    "Finset.range": {
      "refs": [{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Multiset.nodup_range","module":"Mathlib.Data.Multiset.Range","kind":"theorem"},{"where":"body","name":"Multiset.range","module":"Mathlib.Data.Multiset.Range","kind":"def"}],
      "range": {"start":{"line":52,"column":0},"end":{"line":54,"column":20}},
      "name": "Finset.range",
      "module": "Mathlib.Data.Finset.Range",
      "kind": "def",
      "elaborated_type": "ℕ → Finset ℕ",
      "doc": "`range n` is the set of natural numbers less than `n`. ",
      "short": "range",
      "signature_source": "def range (n : ℕ) : Finset ℕ :=",
      "body_source": "⟨_, nodup_range n⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finset/Range.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
