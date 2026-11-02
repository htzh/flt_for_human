window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.GroupTheory.Congruence.Defs"] = {
  "module": "Mathlib.GroupTheory.Congruence.Defs",
  "cards": {
    "AddCon.Quotient": {
      "refs": [{"where":"type","name":"AddCon","module":"Mathlib.GroupTheory.Congruence.Defs","kind":"inductive"},{"where":"type","name":"Add","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Quotient","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":190,"column":2},"end":{"line":191,"column":15}},
      "name": "AddCon.Quotient",
      "module": "Mathlib.GroupTheory.Congruence.Defs",
      "kind": "def",
      "elaborated_type": "{M : Type u_1} → [inst : Add M] → AddCon M → Type u_1",
      "doc": "Defining the quotient by an additive congruence relation of a type with\nan addition. ",
      "short": "Quotient",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    },
    "addConGen": {
      "refs": [{"where":"type","name":"AddCon","module":"Mathlib.GroupTheory.Congruence.Defs","kind":"inductive"},{"where":"type","name":"Add","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"AddConGen.Rel","module":"Mathlib.GroupTheory.Congruence.Defs","kind":"inductive"}],
      "range": {"start":{"line":102,"column":2},"end":{"line":103,"column":27}},
      "name": "addConGen",
      "module": "Mathlib.GroupTheory.Congruence.Defs",
      "kind": "def",
      "elaborated_type": "{M : Type u_1} → [inst : Add M] → (M → M → Prop) → AddCon M",
      "doc": "The inductively defined smallest additive congruence relation containing\na given binary relation. ",
      "short": "addConGen",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
