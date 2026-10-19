window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Order.WithBot"] = {
  "module": "Mathlib.Order.WithBot",
  "cards": {
    "WithBot.unbotD": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":84,"column":0},"end":{"line":88,"column":18}},
      "name": "WithBot.unbotD",
      "module": "Mathlib.Order.WithBot",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → α → WithBot α → α",
      "doc": "Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries. ",
      "short": "unbotD",
      "signature_source": "@[to_dual\n/-- Specialization of `Option.getD` to values in `WithTop α` that respects API boundaries. -/]\ndef unbotD (d : α) (x : WithBot α) : α :=",
      "body_source": "recBotCoe d id x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Order/WithBot.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
