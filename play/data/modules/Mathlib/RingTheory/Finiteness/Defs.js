window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Finiteness.Defs"] = {
  "module": "Mathlib.RingTheory.Finiteness.Defs",
  "cards": {
    "Module.Finite": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":116,"column":0},"end":{"line":119,"column":35}},
      "name": "Module.Finite",
      "module": "Mathlib.RingTheory.Finiteness.Defs",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_1) → (M : Type u_3) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Prop",
      "doc": "A module over a semiring is `Module.Finite` if it is finitely generated as a module. ",
      "short": "Finite",
      "signature_source": "protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where\n  of_fg_top ::\n    fg_top : (⊤ : Submodule R M).FG",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.FG": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"body","name":"Submodule.span","module":"Mathlib.LinearAlgebra.Span.Defs","kind":"def"}],
      "range": {"start":{"line":41,"column":0},"end":{"line":43,"column":31}},
      "name": "Submodule.FG",
      "module": "Mathlib.RingTheory.Finiteness.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → Submodule R M → Prop",
      "doc": "A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. ",
      "short": "FG",
      "signature_source": "def FG (N : Submodule R M) : Prop :=",
      "body_source": "∃ S : Finset M, span R ↑S = N",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
