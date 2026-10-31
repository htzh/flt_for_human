window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Span.Defs"] = {
  "module": "Mathlib.LinearAlgebra.Span.Defs",
  "cards": {
    "Submodule.span": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"InfSet.sInf","module":"Mathlib.Order.SetNotation","kind":"abbrev"},{"where":"body","name":"Set.ofPred","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":45,"column":0},"end":{"line":47,"column":20}},
      "name": "Submodule.span",
      "module": "Mathlib.LinearAlgebra.Span.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  {M : Type u_2} →\n    [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → Set M → Submodule R M",
      "doc": "The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. ",
      "short": "span",
      "signature_source": "def span (s : Set M) : Submodule R M :=",
      "body_source": "sInf { p | s ⊆ p }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
