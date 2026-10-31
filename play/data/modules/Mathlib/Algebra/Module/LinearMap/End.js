window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.LinearMap.End"] = {
  "module": "Mathlib.Algebra.Module.LinearMap.End",
  "cards": {
    "Module.End": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":30,"column":0},"end":{"line":33,"column":11}},
      "name": "Module.End",
      "module": "Mathlib.Algebra.Module.LinearMap.End",
      "kind": "abbrev",
      "elaborated_type": "(R : Type u) → (M : Type v) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type v",
      "doc": "Linear endomorphisms of a module, with associated ring structure\n`Module.End.semiring` and algebra structure `Module.End.algebra`. ",
      "short": "End",
      "signature_source": "abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=",
      "body_source": "M →ₗ[R] M",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
