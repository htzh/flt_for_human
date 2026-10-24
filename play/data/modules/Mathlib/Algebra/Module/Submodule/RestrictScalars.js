window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.RestrictScalars"] = {
  "module": "Mathlib.Algebra.Module.Submodule.RestrictScalars",
  "cards": {
    "Submodule.restrictScalars": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Submodule.add_mem","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"theorem"},{"where":"body","name":"Submodule.zero_mem","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"theorem"}],
      "range": {"start":{"line":32,"column":0},"end":{"line":39,"column":35}},
      "name": "Submodule.restrictScalars",
      "module": "Mathlib.Algebra.Module.Submodule.RestrictScalars",
      "kind": "def",
      "elaborated_type": "(S : Type u_1) →\n  {R : Type u_2} →\n    {M : Type u_3} →\n      [inst : Semiring R] →\n        [inst_1 : AddCommMonoid M] →\n          [inst_2 : Semiring S] →\n            [inst_3 : _root_.Module S M] →\n              [inst_4 : _root_.Module R M] → [inst_5 : SMul S R] → [IsScalarTower S R M] → Submodule R M → Submodule S M",
      "doc": "`V.restrictScalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,\ncorresponding to `V`, an `R`-submodule of the original `R`-module.\n",
      "short": "restrictScalars",
      "signature_source": "def restrictScalars (V : Submodule R M) : Submodule S M where\n  carrier := V\n  zero_mem' := V.zero_mem\n  smul_mem' c _ h := V.smul_of_tower_mem c h\n  add_mem' hx hy := V.add_mem hx hy",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/RestrictScalars.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
