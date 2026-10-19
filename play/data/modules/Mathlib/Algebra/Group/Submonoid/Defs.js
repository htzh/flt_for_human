window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Submonoid.Defs"] = {
  "module": "Mathlib.Algebra.Group.Submonoid.Defs",
  "cards": {
    "Submonoid": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":88,"column":0},"end":{"line":91,"column":30}},
      "name": "Submonoid",
      "module": "Mathlib.Algebra.Group.Submonoid.Defs",
      "kind": "inductive",
      "elaborated_type": "(M : Type u_3) → [MulOneClass M] → Type u_3",
      "doc": "A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. ",
      "short": "Submonoid",
      "signature_source": "structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where\n  /-- A submonoid contains `1`. -/\n  one_mem' : (1 : M) ∈ carrier",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
