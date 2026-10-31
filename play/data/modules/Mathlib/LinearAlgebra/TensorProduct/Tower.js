window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.TensorProduct.Tower"] = {
  "module": "Mathlib.LinearAlgebra.TensorProduct.Tower",
  "cards": {
    "TensorProduct.AlgebraTensorModule.lift": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.leftModule","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"LinearMap.restrictScalars","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"TensorProduct.lift","module":"Mathlib.LinearAlgebra.TensorProduct.Basic","kind":"def"}],
      "range": {"start":{"line":105,"column":0},"end":{"line":121,"column":60}},
      "name": "TensorProduct.AlgebraTensorModule.lift",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Tower",
      "kind": "def",
      "elaborated_type": "{R : Type uR} →\n  {A : Type uA} →\n    {M : Type uM} →\n      {N : Type uN} →\n        {P : Type uP} →\n          [inst : CommSemiring R] →\n            [inst_1 : Semiring A] →\n              [inst_2 : Algebra R A] →\n                [inst_3 : AddCommMonoid M] →\n                  [inst_4 : _root_.Module R M] →\n                    [inst_5 : _root_.Module A M] →\n                      [inst_6 : IsScalarTower R A M] →\n                        [inst_7 : AddCommMonoid N] →\n                          [inst_8 : _root_.Module R N] →\n                            [inst_9 : AddCommMonoid P] →\n                              [inst_10 : _root_.Module R P] →\n                                [inst_11 : _root_.Module A P] →\n                                  [inst_12 : IsScalarTower R A P] → (M →ₗ[A] N →ₗ[R] P) → TensorProduct R M N →ₗ[A] P",
      "doc": "Heterobasic version of `TensorProduct.lift`:\n\nConstructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the\nproperty that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is\nthe given bilinear map `M →[A] N →[R] P`. ",
      "short": "lift",
      "signature_source": "nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=",
      "body_source": "{ lift (f.restrictScalars R) with\n    map_smul' := fun c =>\n      show\n        ∀ x : M ⊗[R] N,\n          (lift (f.restrictScalars R)).comp (lsmul R R _ c) x =\n            (lsmul R R _ c).comp (lift (f.restrictScalars R)) x\n        from\n        LinearMap.ext_iff.1 <|\n          TensorProduct.ext' fun x y => by\n            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,\n              coe_restrictScalars, f.map_smul, smul_apply] }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Tower.lean",
      "has_source": true,
      "has_refs": true
    },
    "TensorProduct.AlgebraTensorModule.mk": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.leftModule","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.smulCommClass_left","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"theorem"},{"where":"body","name":"TensorProduct.mk","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"}],
      "range": {"start":{"line":168,"column":0},"end":{"line":175,"column":47}},
      "name": "TensorProduct.AlgebraTensorModule.mk",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Tower",
      "kind": "def",
      "elaborated_type": "(R : Type uR) →\n  [inst : CommSemiring R] →\n    (A : Type u_1) →\n      (M : Type u_2) →\n        (N : Type u_3) →\n          [inst_1 : Semiring A] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : _root_.Module R M] →\n                [inst_4 : _root_.Module A M] →\n                  [inst_5 : SMulCommClass R A M] →\n                    [inst_6 : AddCommMonoid N] → [inst_7 : _root_.Module R N] → M →ₗ[A] N →ₗ[R] TensorProduct R M N",
      "doc": "Heterobasic version of `TensorProduct.mk`:\n\nThe canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. ",
      "short": "mk",
      "signature_source": "@[simps! apply]\nnonrec def mk (A M N : Type*) [Semiring A]\n    [AddCommMonoid M] [Module R M] [Module A M] [SMulCommClass R A M]\n    [AddCommMonoid N] [Module R N] : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=",
      "body_source": "{ mk R M N with map_smul' := fun _ _ => rfl }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Tower.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
