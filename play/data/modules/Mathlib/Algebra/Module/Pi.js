window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Pi"] = {
  "module": "Mathlib.Algebra.Module.Pi",
  "cards": {
    "Pi.Function.module": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Pi.addCommMonoid","module":"Mathlib.Algebra.Group.Pi.Basic","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Pi.module","module":"Mathlib.Algebra.Module.Pi","kind":"def"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":54,"column":17}},
      "name": "Pi.Function.module",
      "module": "Mathlib.Algebra.Module.Pi",
      "kind": "def",
      "elaborated_type": "(I : Type u) →\n  (α : Type u_1) →\n    (β : Type u_2) → [inst : Semiring α] → [inst_1 : AddCommMonoid β] → [_root_.Module α β] → _root_.Module α (I → β)",
      "doc": "A special case of `Pi.module` for non-dependent types. Lean struggles to elaborate\ndefinitions elsewhere in the library without this. ",
      "short": "module",
      "signature_source": "instance Function.module (α β : Type*) [Semiring α] [AddCommMonoid β] [Module α β] :\n    Module α (I → β) :=",
      "body_source": "Pi.module _ _ _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Pi.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
