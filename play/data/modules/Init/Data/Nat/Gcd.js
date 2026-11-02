window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Nat.Gcd"] = {
  "module": "Init.Data.Nat.Gcd",
  "cards": {
    "Nat.gcd": {
      "refs": [{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":19,"column":0},"end":{"line":41,"column":74}},
      "name": "Nat.gcd",
      "module": "Init.Data.Nat.Gcd",
      "kind": "def",
      "elaborated_type": "ℕ → ℕ → ℕ",
      "doc": "Computes the greatest common divisor of two natural numbers. The GCD of two natural numbers is the\nlargest natural number that evenly divides both.\n\nIn particular, the GCD of a number and `0` is the number itself.\n\nThis reference implementation via the Euclidean algorithm is overridden in both the kernel and the\ncompiler to efficiently evaluate using arbitrary-precision arithmetic. The definition provided here\nis the logical model.\n\nExamples:\n* `Nat.gcd 10 15 = 5`\n* `Nat.gcd 0 5 = 5`\n* `Nat.gcd 7 0 = 7`\n",
      "short": "gcd",
      "signature_source": "@[extern \"lean_nat_gcd\"]\ndef gcd (m n : @& Nat) : Nat :=",
      "body_source": "if m = 0 then\n    n\n  else\n    gcd (n % m) m\n  termination_by m\n  decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Nat/Gcd.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
