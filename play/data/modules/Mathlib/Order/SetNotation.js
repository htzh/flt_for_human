window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Order.SetNotation"] = {
  "module": "Mathlib.Order.SetNotation",
  "cards": {
    "iSup": {
      "refs": [{"where":"type","name":"SupSet","module":"Mathlib.Order.SetNotation","kind":"inductive"},{"where":"body","name":"Set.range","module":"Mathlib.Data.Set.Operations","kind":"def"},{"where":"body","name":"SupSet.sSup","module":"Mathlib.Order.SetNotation","kind":"abbrev"}],
      "range": {"start":{"line":58,"column":0},"end":{"line":61,"column":16}},
      "name": "iSup",
      "module": "Mathlib.Order.SetNotation",
      "kind": "def",
      "elaborated_type": "{α : Type u} → {ι : Sort v} → [SupSet α] → (ι → α) → α",
      "doc": "Indexed supremum ",
      "short": "iSup",
      "signature_source": "@[to_dual /-- Indexed infimum -/]\ndef iSup [SupSet α] (s : ι → α) : α :=",
      "body_source": "sSup (range s)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Order/SetNotation.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
