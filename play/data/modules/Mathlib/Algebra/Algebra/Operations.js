window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Operations"] = {
  "module": "Mathlib.Algebra.Algebra.Operations",
  "cards": {
    "Submodule.idemSemiring": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IdemSemiring","module":"Mathlib.Algebra.Order.Kleene","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"IsScalarTower.right","module":"Mathlib.Algebra.Algebra.Defs","kind":"theorem"},{"where":"body","name":"NPow.ofPow","module":"Mathlib.Algebra.Group.Monoid","kind":"def"},{"where":"body","name":"Submodule.completeLattice","module":"Mathlib.Algebra.Module.Submodule.Lattice","kind":"def"},{"where":"body","name":"Submodule.mul_one","module":"Mathlib.Algebra.Algebra.Operations","kind":"theorem"},{"where":"body","name":"Submodule.pointwiseAddCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Pointwise","kind":"def"}],
      "range": {"start":{"line":594,"column":0},"end":{"line":597,"column":30}},
      "name": "Submodule.idemSemiring",
      "module": "Mathlib.Algebra.Algebra.Operations",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  [inst : CommSemiring R] → {A : Type v} → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → IdemSemiring (Submodule R A)",
      "doc": "Sub-R-modules of an R-algebra form an idempotent semiring. ",
      "short": "idemSemiring",
      "signature_source": "instance idemSemiring : IdemSemiring (Submodule R A) where\n  one_mul := Submodule.one_mul\n  mul_one := Submodule.mul_one",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
