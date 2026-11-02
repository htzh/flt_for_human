window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finset.Card"] = {
  "module": "Mathlib.Data.Finset.Card",
  "cards": {
    "Finset.card": {
      "refs": [{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Finset.val","module":"Mathlib.Data.Finset.Defs","kind":"abbrev"},{"where":"body","name":"Multiset.card","module":"Mathlib.Data.Multiset.Defs","kind":"def"}],
      "range": {"start":{"line":44,"column":0},"end":{"line":48,"column":19}},
      "name": "Finset.card",
      "module": "Mathlib.Data.Finset.Card",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → Finset α → ℕ",
      "doc": "`s.card` is the number of elements of `s`, aka its cardinality.\n\nThe notation `#s` can be accessed in the `Finset` locale. ",
      "short": "card",
      "signature_source": "def card (s : Finset α) : ℕ :=",
      "body_source": "Multiset.card s.1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finset/Card.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
