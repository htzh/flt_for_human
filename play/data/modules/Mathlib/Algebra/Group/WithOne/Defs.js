window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.WithOne.Defs"] = {
  "module": "Mathlib.Algebra.Group.WithOne.Defs",
  "cards": {
    "WithZero": {
      "refs": [{"where":"body","name":"Option","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":38,"column":2},"end":{"line":38,"column":55}},
      "name": "WithZero",
      "module": "Mathlib.Algebra.Group.WithOne.Defs",
      "kind": "def",
      "elaborated_type": "Type u_1 → Type u_1",
      "doc": "Add an extra element `0` to a type ",
      "short": "WithZero",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    },
    "WithZero.recZeroCoe": {
      "refs": [{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"body","name":"Unit","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":104,"column":0},"end":{"line":109,"column":26}},
      "name": "WithZero.recZeroCoe",
      "module": "Mathlib.Algebra.Group.WithOne.Defs",
      "kind": "def",
      "elaborated_type": "{α : Type u} → {motive : WithZero α → Sort u_1} → motive 0 → ((a : α) → motive ↑a) → (n : WithZero α) → motive n",
      "doc": "Recursor for `WithZero` using the preferred forms `0` and `↑a`. ",
      "short": "recZeroCoe",
      "signature_source": "@[elab_as_elim, induction_eliminator, cases_eliminator]\ndef _root_.WithZero.recZeroCoe {motive : WithZero α → Sort*} (zero : motive 0)\n    (coe : ∀ a : α, motive a) : ∀ n : WithZero α, motive n\n  | Option.none => zero\n  | Option.some x => coe x",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/WithOne/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
