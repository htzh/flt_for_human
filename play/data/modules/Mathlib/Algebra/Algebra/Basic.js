window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Basic"] = {
  "module": "Mathlib.Algebra.Algebra.Basic",
  "cards": {
    "Algebra.to_smulCommClass": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":430,"column":0},"end":{"line":433,"column":32}},
      "name": "Algebra.to_smulCommClass",
      "module": "Mathlib.Algebra.Algebra.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_4} {A : Type u_5} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],\n  SMulCommClass R A A",
      "doc": "This has high priority because it is almost always the right instance when it applies. ",
      "short": "to_smulCommClass",
      "signature_source": "instance (priority := high) Algebra.to_smulCommClass {R A} [CommSemiring R] [Semiring A]\n    [Algebra R A] : SMulCommClass R A A :=",
      "body_source": "IsScalarTower.to_smulCommClass",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
