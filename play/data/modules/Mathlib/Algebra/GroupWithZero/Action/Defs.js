window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.GroupWithZero.Action.Defs"] = {
  "module": "Mathlib.Algebra.GroupWithZero.Action.Defs",
  "cards": {
    "SMulWithZero": {
      "refs": [{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":113,"column":0},"end":{"line":118,"column":39}},
      "name": "SMulWithZero",
      "module": "Mathlib.Algebra.GroupWithZero.Action.Defs",
      "kind": "inductive",
      "elaborated_type": "(M₀ : Type u_2) → (A : Type u_7) → [Zero M₀] → [Zero A] → Type (max u_2 u_7)",
      "doc": "`SMulWithZero` is a class consisting of a Type `M₀` with `0 ∈ M₀` and a scalar multiplication\nof `M₀` on a Type `A` with `0`, such that the equality `r • m = 0` holds if at least one among `r`\nor `m` equals `0`. ",
      "short": "SMulWithZero",
      "signature_source": "class SMulWithZero [Zero M₀] [Zero A] extends SMulZeroClass M₀ A where\n  /-- Scalar multiplication by the scalar `0` is `0`. -/\n  zero_smul : ∀ m : A, (0 : M₀) • m = 0",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "zero_smul": {
      "refs": [{"where":"type","name":"SMulWithZero","module":"Mathlib.Algebra.GroupWithZero.Action.Defs","kind":"inductive"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":133,"column":0},"end":{"line":135,"column":26}},
      "name": "zero_smul",
      "module": "Mathlib.Algebra.GroupWithZero.Action.Defs",
      "kind": "theorem",
      "elaborated_type": "∀ (M₀ : Type u_2) {A : Type u_7} [inst : Zero M₀] [inst_1 : Zero A] [inst_2 : SMulWithZero M₀ A] (m : A), 0 • m = 0",
      "doc": "",
      "short": "zero_smul",
      "signature_source": "@[simp]\ntheorem zero_smul (m : A) : (0 : M₀) • m = 0 :=",
      "body_source": "SMulWithZero.zero_smul m",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
