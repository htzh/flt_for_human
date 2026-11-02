window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Logic.Equiv.Defs"] = {
  "module": "Mathlib.Logic.Equiv.Defs",
  "cards": {
    "Equiv": {
      "refs": [],
      "range": {"start":{"line":66,"column":0},"end":{"line":77,"column":88}},
      "name": "Equiv",
      "module": "Mathlib.Logic.Equiv.Defs",
      "kind": "inductive",
      "elaborated_type": "Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)",
      "doc": "`α ≃ β` is the type of functions from `α → β` with a two-sided inverse. ",
      "short": "Equiv",
      "signature_source": "structure Equiv (α β : Sort*) where\n  /-- The forward map of an equivalence.\n\n  Do NOT use directly. Use the coercion instead. -/\n  protected toFun : α → β\n  /-- The backward map of an equivalence.\n\n  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/\n  protected invFun : β → α\n  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl\n  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean",
      "has_source": true,
      "has_refs": false
    },
    "Equiv.trans": {
      "refs": [{"where":"type","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"body","name":"Equiv.symm","module":"Mathlib.Logic.Equiv.Defs","kind":"def"},{"where":"body","name":"Function.comp","module":"Init.Prelude","kind":"def"}],
      "range": {"start":{"line":160,"column":0},"end":{"line":163,"column":92}},
      "name": "Equiv.trans",
      "module": "Mathlib.Logic.Equiv.Defs",
      "kind": "def",
      "elaborated_type": "{α : Sort u} → {β : Sort v} → {γ : Sort w} → α ≃ β → β ≃ γ → α ≃ γ",
      "doc": "Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. ",
      "short": "trans",
      "signature_source": "@[trans]\nprotected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=",
      "body_source": "⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
