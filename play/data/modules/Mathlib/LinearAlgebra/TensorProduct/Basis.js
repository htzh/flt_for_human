window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.TensorProduct.Basis"] = {
  "module": "Mathlib.LinearAlgebra.TensorProduct.Basis",
  "cards": {
    "Module.Basis.baseChange": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.leftModule","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"Equiv.punitProd","module":"Mathlib.Logic.Equiv.Prod","kind":"def"},{"where":"body","name":"IsScalarTower.right","module":"Mathlib.Algebra.Algebra.Defs","kind":"theorem"},{"where":"body","name":"Module.Basis.reindex","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"def"},{"where":"body","name":"Module.Basis.singleton","module":"Mathlib.LinearAlgebra.Basis.Basic","kind":"def"},{"where":"body","name":"Module.Basis.tensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Basis","kind":"def"},{"where":"body","name":"Prod","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Unit","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":62,"column":0},"end":{"line":65,"column":67}},
      "name": "Module.Basis.baseChange",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Basis",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_3} →\n    {ι : Type u_5} →\n      [inst : CommSemiring R] →\n        [inst_1 : AddCommMonoid M] →\n          [inst_2 : _root_.Module R M] →\n            (S : Type u_7) →\n              [inst_3 : Semiring S] →\n                [inst_4 : Algebra R S] → Module.Basis ι R M → Module.Basis ι S (TensorProduct R S M)",
      "doc": "The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`. ",
      "short": "baseChange",
      "signature_source": "noncomputable\ndef baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=",
      "body_source": "(tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basis.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
