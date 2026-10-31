window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Logic.Equiv.Prod"] = {
  "module": "Mathlib.Logic.Equiv.Prod",
  "cards": {
    "Equiv.punitProd": {
      "refs": [{"where":"type","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"type","name":"PUnit","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Prod","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Equiv.prodComm","module":"Mathlib.Logic.Equiv.Prod","kind":"def"},{"where":"body","name":"Equiv.prodPUnit","module":"Mathlib.Logic.Equiv.Prod","kind":"def"},{"where":"body","name":"Trans.trans","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":133,"column":0},"end":{"line":138,"column":24}},
      "name": "Equiv.punitProd",
      "module": "Mathlib.Logic.Equiv.Prod",
      "kind": "def",
      "elaborated_type": "(α : Type u_9) → PUnit.{u_10 + 1} × α ≃ α",
      "doc": "`PUnit` is a left identity for type product up to an equivalence. ",
      "short": "punitProd",
      "signature_source": "@[simps! (attr := grind =)]\ndef punitProd (α) : PUnit × α ≃ α :=",
      "body_source": "calc\n    PUnit × α ≃ α × PUnit := prodComm _ _\n    _ ≃ α := prodPUnit _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Prod.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
