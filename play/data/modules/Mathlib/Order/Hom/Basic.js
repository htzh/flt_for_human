window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Order.Hom.Basic"] = {
  "module": "Mathlib.Order.Hom.Basic",
  "cards": {
    "OrderEmbedding": {
      "refs": [{"where":"type","name":"LE","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"RelEmbedding","module":"Mathlib.Order.RelIso.Basic","kind":"inductive"}],
      "range": {"start":{"line":91,"column":0},"end":{"line":94,"column":35}},
      "name": "OrderEmbedding",
      "module": "Mathlib.Order.Hom.Basic",
      "kind": "abbrev",
      "elaborated_type": "(α : Type u_6) → (β : Type u_7) → [LE α] → [LE β] → Type (max u_6 u_7)",
      "doc": "An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.\nThis definition is an abbreviation of `RelEmbedding (≤) (≤)`. ",
      "short": "OrderEmbedding",
      "signature_source": "abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=",
      "body_source": "@RelEmbedding α β (· ≤ ·) (· ≤ ·)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
