window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Nat.Coprime"] = {
  "module": "Init.Data.Nat.Coprime",
  "cards": {
    "Nat.Coprime": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":24,"column":0},"end":{"line":25,"column":66}},
      "name": "Nat.Coprime",
      "module": "Init.Data.Nat.Coprime",
      "kind": "def",
      "elaborated_type": "ℕ → ℕ → Prop",
      "doc": "`m` and `n` are coprime, or relatively prime, if their `gcd` is 1. ",
      "short": "Coprime",
      "signature_source": "@[reducible, expose] def Coprime (m n : Nat) : Prop :=",
      "body_source": "gcd m n = 1",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Nat/Coprime.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
