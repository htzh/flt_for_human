window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Int.Basic"] = {
  "module": "Init.Data.Int.Basic",
  "cards": {
    "Int": {
      "refs": [],
      "range": {"start":{"line":35,"column":0},"end":{"line":58,"column":23}},
      "name": "Int",
      "module": "Init.Data.Int.Basic",
      "kind": "inductive",
      "elaborated_type": "Type",
      "doc": "The integers.\n\nThis type is special-cased by the compiler and overridden with an efficient implementation. The\nruntime has a special representation for `Int` that stores “small” signed numbers directly, while\nlarger numbers use a fast arbitrary-precision arithmetic library (usually\n[GMP](https://gmplib.org/)). A “small number” is an integer that can be encoded with one fewer bits\nthan the platform's pointer size (i.e. 63 bits on 64-bit architectures and 31 bits on 32-bit\narchitectures).\n",
      "short": "Int",
      "signature_source": "@[suggest_for ℤ]\ninductive Int : Type where\n  /--\n  A natural number is an integer.\n\n  This constructor covers the non-negative integers (from `0` to `∞`).\n  -/\n  | ofNat   : Nat → Int\n  /--\n  The negation of the successor of a natural number is an integer.\n\n  This constructor covers the negative integers (from `-1` to `-∞`).\n  -/\n  | negSucc : Nat → Int",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Int/Basic.lean",
      "has_source": true,
      "has_refs": false
    },
    "Int.cast": {
      "refs": [{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"IntCast","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IntCast.intCast","module":"Init.Data.Int.Basic","kind":"abbrev"}],
      "range": {"start":{"line":457,"column":0},"end":{"line":459,"column":17}},
      "name": "Int.cast",
      "module": "Init.Data.Int.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [IntCast R] → ℤ → R",
      "doc": "The canonical homomorphism `Int → R`. In most use cases, the target type will have a ring structure,\nand this homomorphism should be a ring homomorphism.\n\n`IntCast` and `NatCast` exist to allow different libraries with their own types that can be notated\nas natural numbers to have consistent `simp` normal forms without needing to create coercion\nsimplification sets that are aware of all combinations. Libraries should make it easy to work with\n`IntCast` where possible. For instance, in Mathlib there will be such a homomorphism (and thus an\n`IntCast R` instance) whenever `R` is an additive group with a `1`.\n",
      "short": "cast",
      "signature_source": "@[coe, reducible, match_pattern, inherit_doc IntCast]\nprotected def Int.cast {R : Type u} [IntCast R] : Int → R :=",
      "body_source": "IntCast.intCast",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Int/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Int.decLt": {
      "refs": [{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Int.decNonneg","module":"Init.Data.Int.Basic","kind":"def"}],
      "range": {"start":{"line":303,"column":0},"end":{"line":314,"column":13}},
      "name": "Int.decLt",
      "module": "Init.Data.Int.Basic",
      "kind": "def",
      "elaborated_type": "(a b : ℤ) → Decidable (a < b)",
      "doc": "Decides whether `a < b`.\n\n```\n#eval `¬ ( (7 : Int) < 0 )` -- true\n#eval `¬ ( (0 : Int) < 0 )` -- true\n#eval `(7 : Int) < 10` -- true\n```\n\nImplemented by efficient native code. ",
      "short": "decLt",
      "signature_source": "@[extern \"lean_int_dec_lt\"]\ninstance decLt (a b : @& Int) : Decidable (a < b) :=",
      "body_source": "decNonneg _",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Int/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Int.natAbs": {
      "refs": [{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":317,"column":0},"end":{"line":332,"column":21}},
      "name": "Int.natAbs",
      "module": "Init.Data.Int.Basic",
      "kind": "def",
      "elaborated_type": "ℤ → ℕ",
      "doc": "The absolute value of an integer is its distance from `0`.\n\nThis function is overridden by the compiler with an efficient implementation. This definition is\nthe logical model.\n\nExamples:\n * `(7 : Int).natAbs = 7`\n * `(0 : Int).natAbs = 0`\n * `(-11 : Int).natAbs = 11`\n",
      "short": "natAbs",
      "signature_source": "@[extern \"lean_nat_abs\", implicit_reducible]\ndef natAbs (m : @& Int) : Nat :=",
      "body_source": "match m with\n  | ofNat m => m\n  | -[m +1] => m.succ",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Int/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Int.sign": {
      "refs": [{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Unit","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":338,"column":0},"end":{"line":354,"column":21}},
      "name": "Int.sign",
      "module": "Init.Data.Int.Basic",
      "kind": "def",
      "elaborated_type": "ℤ → ℤ",
      "doc": "Returns the “sign” of the integer as another integer:\n* `1` for positive numbers,\n* `-1` for negative numbers, and\n* `0` for `0`.\n\nExamples:\n* `Int.sign 34 = 1`\n* `Int.sign 2 = 1`\n* `Int.sign 0 = 0`\n* `Int.sign -1 = -1`\n* `Int.sign -362 = -1`\n",
      "short": "sign",
      "signature_source": "def sign : Int → Int\n  | Int.ofNat (succ _) => 1\n  | Int.ofNat 0 => 0\n  | -[_+1]      => -1",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Int/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
