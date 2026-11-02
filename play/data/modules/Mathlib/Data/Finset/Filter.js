window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finset.Filter"] = {
  "module": "Mathlib.Data.Finset.Filter",
  "cards": {
    "Finset.filter": {
      "refs": [{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"type","name":"DecidablePred","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"Finset.val","module":"Mathlib.Data.Finset.Defs","kind":"abbrev"},{"where":"body","name":"Multiset.filter","module":"Mathlib.Data.Multiset.Filter","kind":"def"}],
      "range": {"start":{"line":48,"column":0},"end":{"line":53,"column":19}},
      "name": "Finset.filter",
      "module": "Mathlib.Data.Finset.Filter",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α",
      "doc": "`Finset.filter p s` is the set of elements of `s` that satisfy `p`.\n\nFor example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`\nas a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). ",
      "short": "filter",
      "signature_source": "def filter (s : Finset α) : Finset α :=",
      "body_source": "⟨_, s.2.filter p⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finset/Filter.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
