window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.FreeModule.Basic"] = {
  "module": "Mathlib.LinearAlgebra.FreeModule.Basic",
  "cards": {
    "Module.Free": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":42,"column":0},"end":{"line":44,"column":61}},
      "name": "Module.Free",
      "module": "Mathlib.LinearAlgebra.FreeModule.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (M : Type v) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Prop",
      "doc": "`Module.Free R M` is the statement that the `R`-module `M` is free. ",
      "short": "Free",
      "signature_source": "class Free (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where\n  exists_basis (R M) : Nonempty <| (I : Type v) × Basis I R M",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
