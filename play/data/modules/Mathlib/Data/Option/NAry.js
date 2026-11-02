window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Option.NAry"] = {
  "module": "Mathlib.Data.Option.NAry",
  "cards": {
    "Option.map₂": {
      "refs": [{"where":"type","name":"Option","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Option.bind","module":"Init.Data.Option.Basic","kind":"def"},{"where":"body","name":"Option.map","module":"Init.Prelude","kind":"def"}],
      "range": {"start":{"line":42,"column":0},"end":{"line":45,"column":30}},
      "name": "Option.map₂",
      "module": "Mathlib.Data.Option.NAry",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → (α → β → γ) → Option α → Option β → Option γ",
      "doc": "The image of a binary function `f : α → β → γ` as a function `Option α → Option β → Option γ`.\nMathematically this should be thought of as the image of the corresponding function `α × β → γ`. ",
      "short": "map₂",
      "signature_source": "def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=",
      "body_source": "a.bind fun a => b.map <| f a",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Option/NAry.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
