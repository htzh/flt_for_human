window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Order.Defs.PartialOrder"] = {
  "module": "Mathlib.Order.Defs.PartialOrder",
  "cards": {
    "Preorder": {
      "refs": [],
      "range": {"start":{"line":40,"column":0},"end":{"line":49,"column":82}},
      "name": "Preorder",
      "module": "Mathlib.Order.Defs.PartialOrder",
      "kind": "inductive",
      "elaborated_type": "Type u_2 → Type u_2",
      "doc": "A preorder is a reflexive, transitive relation `≤`.\nIn a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by default.\nYou can override this definition to set a better def-eq.\n",
      "short": "Preorder",
      "signature_source": "class Preorder (α : Type*) extends LE α, LT α where\n  protected le_refl : ∀ a : α, a ≤ a\n  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c\n  lt := fun a b => a ≤ b ∧ ¬b ≤ a\n  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean",
      "has_source": true,
      "has_refs": false
    },
    "le_trans": {
      "refs": [{"where":"type","name":"Preorder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"}],
      "range": {"start":{"line":68,"column":0},"end":{"line":69,"column":65}},
      "name": "le_trans",
      "module": "Mathlib.Order.Defs.PartialOrder",
      "kind": "theorem",
      "elaborated_type": "∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c",
      "doc": "The relation `≤` on a preorder is transitive. ",
      "short": "le_trans",
      "signature_source": "lemma le_trans : a ≤ b → b ≤ c → a ≤ c :=",
      "body_source": "Preorder.le_trans _ _ _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
