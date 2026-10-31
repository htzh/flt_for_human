window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Ideal.Operations"] = {
  "module": "Mathlib.RingTheory.Ideal.Operations",
  "cards": {
    "Ideal.mul_mem_mul": {
      "refs": [{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"IsScalarTower.left","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule.mul","module":"Mathlib.Algebra.Algebra.Operations","kind":"def"}],
      "range": {"start":{"line":277,"column":0},"end":{"line":278,"column":31}},
      "name": "Ideal.mul_mem_mul",
      "module": "Mathlib.RingTheory.Ideal.Operations",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : Semiring R] {I J : Ideal R} {r s : R}, r ∈ I → s ∈ J → r * s ∈ I * J",
      "doc": "",
      "short": "mul_mem_mul",
      "signature_source": "theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=",
      "body_source": "Submodule.smul_mem_smul hr hs",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
