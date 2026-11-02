window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.GroupTheory.Coset.Defs"] = {
  "module": "Mathlib.GroupTheory.Coset.Defs",
  "cards": {
    "QuotientAddGroup.mk": {
      "refs": [{"where":"type","name":"AddGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"AddSubgroup","module":"Mathlib.Algebra.Group.Subgroup.Defs","kind":"inductive"},{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"body","name":"Quotient.mk''","module":"Mathlib.Data.Quot","kind":"abbrev"},{"where":"body","name":"QuotientAddGroup.leftRel","module":"Mathlib.GroupTheory.Coset.Defs","kind":"def"}],
      "range": {"start":{"line":159,"column":2},"end":{"line":160,"column":72}},
      "name": "QuotientAddGroup.mk",
      "module": "Mathlib.GroupTheory.Coset.Defs",
      "kind": "abbrev",
      "elaborated_type": "{α : Type u_1} → [inst : AddGroup α] → {s : AddSubgroup α} → α → α ⧸ s",
      "doc": "The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`. ",
      "short": "mk",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
