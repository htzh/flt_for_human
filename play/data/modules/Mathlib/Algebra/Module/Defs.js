window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Defs"] = {
  "module": "Mathlib.Algebra.Module.Defs",
  "cards": {
    "Module": {
      "seed": true,
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":48,"column":0},"end":{"line":59,"column":48}},
      "name": "Module",
      "module": "Mathlib.Algebra.Module.Defs",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (M : Type v) → [Semiring R] → [AddCommMonoid M] → Type (max u v)",
      "doc": "A module is a generalization of vector spaces to a scalar semiring.\nIt consists of a scalar semiring `R` and an additive monoid of \"vectors\" `M`,\nconnected by a \"scalar multiplication\" operation `r • x : M`\n(where `r : R` and `x : M`) with some natural associativity and\ndistributivity axioms similar to those on a ring. ",
      "short": "Module",
      "signature_source": "@[ext]\nclass Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends\n  DistribMulAction R M where\n  /-- Scalar multiplication distributes over addition from the right. -/\n  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x\n  /-- Scalar multiplication by zero gives zero. -/\n  protected zero_smul : ∀ x : M, (0 : R) • x = 0",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Defs.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
