window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Order.WellFounded"] = {
  "module": "Mathlib.Order.WellFounded",
  "cards": {
    "WellFounded.min": {
      "refs": [{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Set.Nonempty","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"WellFounded","module":"Init.WF","kind":"inductive"},{"where":"body","name":"WellFounded.has_min","module":"Mathlib.Order.WellFounded","kind":"theorem"},{"where":"body","name":"Classical.choose","module":"Init.Classical","kind":"def"}],
      "range": {"start":{"line":108,"column":0},"end":{"line":114,"column":34}},
      "name": "WellFounded.min",
      "module": "Mathlib.Order.WellFounded",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → {r : α → α → Prop} → WellFounded r → (s : Set α) → s.Nonempty → α",
      "doc": "A minimal element of a nonempty set in a well-founded order.\n\nIf you're working with a nonempty linear order, consider defining a\n`ConditionallyCompleteLinearOrderBot` instance via\n`WellFoundedLT.conditionallyCompleteLinearOrderBot` and using `Inf` instead. ",
      "short": "min",
      "signature_source": "noncomputable def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=",
      "body_source": "Classical.choose (H.has_min s h)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Order/WellFounded.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
