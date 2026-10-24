window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Dual.Defs"] = {
  "module": "Mathlib.LinearAlgebra.Dual.Defs",
  "cards": {
    "Module.Dual": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":60,"column":0},"end":{"line":63,"column":11}},
      "name": "Module.Dual",
      "module": "Mathlib.LinearAlgebra.Dual.Defs",
      "kind": "abbrev",
      "elaborated_type": "(R : Type u_3) →\n  (M : Type u_4) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max u_4 u_3)",
      "doc": "The left dual space of an R-module M is the R-module of linear maps `M → R`. ",
      "short": "Dual",
      "signature_source": "@[wikidata Q752487]\nabbrev Dual (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=",
      "body_source": "M →ₗ[R] R",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.dualAnnihilator": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower.left","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Dual","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"abbrev"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.ker","module":"Mathlib.Algebra.Module.Submodule.Ker","kind":"def"},{"where":"body","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.dualRestrict","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"def"},{"where":"body","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"}],
      "range": {"start":{"line":333,"column":0},"end":{"line":337,"column":30}},
      "name": "Submodule.dualAnnihilator",
      "module": "Mathlib.LinearAlgebra.Dual.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_3} →\n  {M : Type u_4} →\n    [inst : CommSemiring R] →\n      [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → Submodule R M → Submodule R (Module.Dual R M)",
      "doc": "The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such\nthat `φ w = 0` for all `w ∈ W`. ",
      "short": "dualAnnihilator",
      "signature_source": "def dualAnnihilator {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]\n    (W : Submodule R M) : Submodule R <| Module.Dual R M :=",
      "body_source": "LinearMap.ker W.dualRestrict",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
