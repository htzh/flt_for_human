window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Set.Operations"] = {
  "module": "Mathlib.Data.Set.Operations",
  "cards": {
    "Set.range": {
      "refs": [{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Set.ofPred","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":169,"column":0},"end":{"line":173,"column":51}},
      "name": "Set.range",
      "module": "Mathlib.Data.Set.Operations",
      "kind": "def",
      "elaborated_type": "{α : Type u} → {ι : Sort u_1} → (ι → α) → Set α",
      "doc": "Range of a function.\n\nThis function is more flexible than `f '' univ`, as the image requires that the domain is in Type\nand not an arbitrary Sort. ",
      "short": "range",
      "signature_source": "def range (f : ι → α) : Set α :=",
      "body_source": "{x | ∃ y, f y = x}",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Set/Operations.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
