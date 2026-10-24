window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.FiniteDimensional.Defs"] = {
  "module": "Mathlib.LinearAlgebra.FiniteDimensional.Defs",
  "cards": {
    "FiniteDimensional": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"DivisionRing","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"body","name":"Module.Finite","module":"Mathlib.RingTheory.Finiteness.Defs","kind":"inductive"}],
      "range": {"start":{"line":72,"column":0},"end":{"line":75,"column":19}},
      "name": "FiniteDimensional",
      "module": "Mathlib.LinearAlgebra.FiniteDimensional.Defs",
      "kind": "abbrev",
      "elaborated_type": "(K : Type u_1) → (V : Type u_2) → [inst : DivisionRing K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Prop",
      "doc": "`FiniteDimensional` vector spaces are defined to be finite modules.\nUse `Module.Basis.finiteDimensional_of_finite` to prove finite dimension from another definition. ",
      "short": "FiniteDimensional",
      "signature_source": "abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=",
      "body_source": "Module.Finite K V",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
