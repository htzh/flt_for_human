window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Order.IsBotOne"] = {
  "module": "Mathlib.Algebra.Order.IsBotOne",
  "cards": {
    "NeZero.of_gt'": {
      "refs": [{"where":"type","name":"Fact","module":"Mathlib.Basic.Logic.Basic","kind":"inductive"},{"where":"type","name":"IsBotZeroClass","module":"Mathlib.Algebra.Order.IsBotOne","kind":"inductive"},{"where":"type","name":"Preorder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"type","name":"One","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":160,"column":0},"end":{"line":161,"column":61}},
      "name": "NeZero.of_gt'",
      "module": "Mathlib.Algebra.Order.IsBotOne",
      "kind": "theorem",
      "elaborated_type": "∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preorder α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],\n  NeZero a",
      "doc": "",
      "short": "of_gt'",
      "signature_source": "instance (priority := 10) of_gt' [Preorder α] [IsBotZeroClass α] [One α]\n    [Fact (1 < a)] : NeZero a :=",
      "body_source": "of_gt <| @Fact.out (1 < a) _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Order/IsBotOne.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
