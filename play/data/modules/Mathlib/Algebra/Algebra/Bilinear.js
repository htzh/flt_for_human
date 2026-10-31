window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Bilinear"] = {
  "module": "Mathlib.Algebra.Algebra.Bilinear",
  "cards": {
    "LinearMap.mul": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"NonUnitalNonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"body","name":"LinearMap.mk₂","module":"Mathlib.LinearAlgebra.BilinearMap","kind":"def"}],
      "range": {"start":{"line":32,"column":0},"end":{"line":37,"column":70}},
      "name": "LinearMap.mul",
      "module": "Mathlib.Algebra.Algebra.Bilinear",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  (A : Type u_2) →\n    [inst : CommSemiring R] →\n      [inst_1 : NonUnitalNonAssocSemiring A] →\n        [inst_2 : _root_.Module R A] → [SMulCommClass R A A] → [IsScalarTower R A A] → A →ₗ[R] A →ₗ[R] A",
      "doc": "The multiplication in a non-unital non-associative algebra is a bilinear map.\n\nA weaker version of this for semirings exists as `AddMonoidHom.mul`. ",
      "short": "mul",
      "signature_source": "@[instance_reducible, simps!]\ndef mul : A →ₗ[R] A →ₗ[R] A :=",
      "body_source": "LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
