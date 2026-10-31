window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs"] = {
  "module": "Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs",
  "cards": {
    "IsLocalRing.maximalIdeal": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"IsLocalRing","module":"Mathlib.RingTheory.LocalRing.Defs","kind":"inductive"},{"where":"body","name":"AddSubmonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"body","name":"IsLocalRing.nonunitsAddSubmonoid","module":"Mathlib.RingTheory.LocalRing.Basic","kind":"def"}],
      "range": {"start":{"line":29,"column":0},"end":{"line":32,"column":41}},
      "name": "IsLocalRing.maximalIdeal",
      "module": "Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → [inst : CommSemiring R] → [IsLocalRing R] → Ideal R",
      "doc": "The ideal of elements that are not units. ",
      "short": "maximalIdeal",
      "signature_source": "def maximalIdeal : Ideal R where\n  __ := nonunitsAddSubmonoid R\n  smul_mem' _ _ := mul_mem_nonunits_right",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/MaximalIdeal/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
