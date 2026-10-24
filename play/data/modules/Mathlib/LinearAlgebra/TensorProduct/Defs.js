window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.TensorProduct.Defs"] = {
  "module": "Mathlib.LinearAlgebra.TensorProduct.Defs",
  "cards": {
    "TensorProduct": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"body","name":"AddCon.Quotient","module":"Mathlib.GroupTheory.Congruence.Defs","kind":"def"},{"where":"body","name":"FreeAddMonoid","module":"Mathlib.Algebra.FreeMonoid.Basic","kind":"def"},{"where":"body","name":"TensorProduct.Eqv","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"inductive"},{"where":"body","name":"addConGen","module":"Mathlib.GroupTheory.Congruence.Defs","kind":"def"},{"where":"body","name":"Prod","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":69,"column":0},"end":{"line":73,"column":46}},
      "name": "TensorProduct",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  [inst : CommSemiring R] →\n    (M : Type u_5) →\n      (N : Type u_6) →\n        [inst_1 : AddCommMonoid M] →\n          [inst_2 : AddCommMonoid N] → [_root_.Module R M] → [_root_.Module R N] → Type (max u_5 u_6)",
      "doc": "The tensor product of two modules `M` and `N` over the same commutative semiring `R`.\nThe localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped TensorProduct`. ",
      "short": "TensorProduct",
      "signature_source": "def TensorProduct : Type _ :=",
      "body_source": "(addConGen (TensorProduct.Eqv R M N)).Quotient\nderiving Zero, Add, AddZeroClass, AddSemigroup",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "TensorProduct.addCommMonoid": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.addMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"}],
      "range": {"start":{"line":272,"column":0},"end":{"line":272,"column":55}},
      "name": "TensorProduct.addCommMonoid",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  [inst : CommSemiring R] →\n    {M : Type u_5} →\n      {N : Type u_6} →\n        [inst_1 : AddCommMonoid M] →\n          [inst_2 : AddCommMonoid N] →\n            [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R N] → AddCommMonoid (TensorProduct R M N)",
      "doc": "",
      "short": "addCommMonoid",
      "signature_source": "instance addCommMonoid : AddCommMonoid (M ⊗[R] N) where",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "TensorProduct.leftModule": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.add_smul","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"theorem"},{"where":"body","name":"TensorProduct.leftDistribMulAction","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.zero_smul","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"theorem"}],
      "range": {"start":{"line":317,"column":0},"end":{"line":319,"column":42}},
      "name": "TensorProduct.leftModule",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R'' : Type u_3} →\n    [inst : CommSemiring R] →\n      [inst_1 : Semiring R''] →\n        {M : Type u_5} →\n          {N : Type u_6} →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid N] →\n                [inst_4 : _root_.Module R'' M] →\n                  [inst_5 : _root_.Module R M] →\n                    [inst_6 : _root_.Module R N] → [SMulCommClass R R'' M] → _root_.Module R'' (TensorProduct R M N)",
      "doc": "",
      "short": "leftModule",
      "signature_source": "instance leftModule : Module R'' (M ⊗[R] N) :=",
      "body_source": "{ add_smul := TensorProduct.add_smul\n    zero_smul := TensorProduct.zero_smul }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
