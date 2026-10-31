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
    },
    "IsScalarTower.to_smulCommClass": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":420,"column":0},"end":{"line":423,"column":31}},
      "name": "IsScalarTower.to_smulCommClass",
      "module": "Mathlib.Algebra.Algebra.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}\n  [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M] [IsScalarTower R A M],\n  SMulCommClass R A M",
      "doc": "",
      "short": "to_smulCommClass",
      "signature_source": "instance (priority := 120) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=",
      "body_source": "⟨fun r a m => by\n    rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ←\n      algebra_compatible_smul]⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
