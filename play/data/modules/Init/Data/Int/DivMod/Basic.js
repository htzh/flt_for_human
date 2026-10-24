window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Int.DivMod.Basic"] = {
  "module": "Init.Data.Int.DivMod.Basic",
  "cards": {
    "Int.tdiv": {
      "refs": [{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":154,"column":0},"end":{"line":182,"column":48}},
      "name": "Int.tdiv",
      "module": "Init.Data.Int.DivMod.Basic",
      "kind": "def",
      "elaborated_type": "ℤ → ℤ → ℤ",
      "doc": "Integer division using the T-rounding convention.\n\nIn [the T-rounding convention][t-rounding] (division with truncation), all rounding is towards zero.\nDivision by 0 is defined to be 0. In this convention, `Int.tmod a b + b * (Int.tdiv a b) = a`.\n\n[t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862\n\nThis function is overridden by the compiler with an efficient implementation. This definition is the\nlogical model.\n\nExamples:\n* `(7 : Int).tdiv (0 : Int) = 0`\n* `(0 : Int).tdiv (7 : Int) = 0`\n* `(12 : Int).tdiv (6 : Int) = 2`\n* `(12 : Int).tdiv (-6 : Int) = -2`\n* `(-12 : Int).tdiv (6 : Int) = -2`\n* `(-12 : Int).tdiv (-6 : Int) = 2`\n* `(12 : Int).tdiv (7 : Int) = 1`\n* `(12 : Int).tdiv (-7 : Int) = -1`\n* `(-12 : Int).tdiv (7 : Int) = -1`\n* `(-12 : Int).tdiv (-7 : Int) = 1`\n",
      "short": "tdiv",
      "signature_source": "@[extern \"lean_int_div\", implicit_reducible]\ndef tdiv : (@& Int) → (@& Int) → Int\n  | ofNat m, ofNat n =>  ofNat (m / n)\n  | ofNat m, -[n +1] => -ofNat (m / succ n)\n  | -[m +1], ofNat n => -ofNat (succ m / n)\n  | -[m +1], -[n +1] =>  ofNat (succ m / succ n)",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Int/DivMod/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
