window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Ideal.Defs"] = {
  "module": "Mathlib.RingTheory.Ideal.Defs",
  "cards": {
    "Ideal": {
      "refs": [{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"}],
      "range": {"start":{"line":38,"column":0},"end":{"line":41,"column":15}},
      "name": "Ideal",
      "module": "Mathlib.RingTheory.Ideal.Defs",
      "kind": "abbrev",
      "elaborated_type": "(R : Type u) → [Semiring R] → Type u",
      "doc": "A (left) ideal in a semiring `R` is an additive submonoid `s` such that\n`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup. ",
      "short": "Ideal",
      "signature_source": "abbrev Ideal (R : Type u) [Semiring R] :=",
      "body_source": "Submodule R R",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Ideal.IsTwoSided": {
      "refs": [{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":49,"column":0},"end":{"line":51,"column":53}},
      "name": "Ideal.IsTwoSided",
      "module": "Mathlib.RingTheory.Ideal.Defs",
      "kind": "inductive",
      "elaborated_type": "{α : Type u} → [inst : Semiring α] → Ideal α → Prop",
      "doc": "A left ideal `I : Ideal R` is two-sided if it is also a right ideal. ",
      "short": "IsTwoSided",
      "signature_source": "@[mk_iff] class IsTwoSided : Prop where\n  mul_mem_of_left {a : α} (b : α) : a ∈ I → a * b ∈ I",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Ideal.mul_mem_left": {
      "refs": [{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":61,"column":0},"end":{"line":62,"column":24}},
      "name": "Ideal.mul_mem_left",
      "module": "Mathlib.RingTheory.Ideal.Defs",
      "kind": "theorem",
      "elaborated_type": "∀ {α : Type u} [inst : Semiring α] (I : Ideal α) (a : α) {b : α}, b ∈ I → a * b ∈ I",
      "doc": "",
      "short": "mul_mem_left",
      "signature_source": "theorem mul_mem_left : b ∈ I → a * b ∈ I :=",
      "body_source": "Submodule.smul_mem I a",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
