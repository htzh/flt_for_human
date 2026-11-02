window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.GroupWithZero.Defs"] = {
  "module": "Mathlib.Algebra.GroupWithZero.Defs",
  "cards": {
    "NoZeroDivisors": {
      "refs": [{"where":"type","name":"Mul","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":107,"column":0},"end":{"line":112,"column":77}},
      "name": "NoZeroDivisors",
      "module": "Mathlib.Algebra.GroupWithZero.Defs",
      "kind": "inductive",
      "elaborated_type": "(M₀ : Type u_2) → [Mul M₀] → [Zero M₀] → Prop",
      "doc": "Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`\nfor all `a` and `b` of type `M₀`. It is weaker than `IsCancelMulZero` in general,\nbut equivalent to it if `M₀` is a (not necessarily unital or associative) ring. ",
      "short": "NoZeroDivisors",
      "signature_source": "@[mk_iff] class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where\n  /-- For all `a` and `b` of `M₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/\n  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
