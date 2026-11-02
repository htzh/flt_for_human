window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Nat.DvdSequence"] = {
  "module": "Mathlib.Data.Nat.DvdSequence",
  "cards": {
    "IsDvdSequence": {
      "refs": [{"where":"type","name":"Dvd","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":39,"column":0},"end":{"line":41,"column":26}},
      "name": "IsDvdSequence",
      "module": "Mathlib.Data.Nat.DvdSequence",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → {β : Type u_2} → [Dvd α] → [Dvd β] → (α → β) → Prop",
      "doc": "A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`. ",
      "short": "IsDvdSequence",
      "signature_source": "def IsDvdSequence [Dvd α] [Dvd β] (f : α → β) : Prop :=",
      "body_source": "∀ a b, a ∣ b → f a ∣ f b",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Nat/DvdSequence.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
