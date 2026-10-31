window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.MonoidAlgebra.Basic"] = {
  "module": "Mathlib.Algebra.MonoidAlgebra.Basic",
  "cards": {
    "AddMonoidAlgebra.algebra": {
      "refs": [{"where":"type","name":"AddMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"AddMonoidAlgebra","module":"Mathlib.Algebra.MonoidAlgebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AddMonoidAlgebra.nonAssocSemiring","module":"Mathlib.Algebra.MonoidAlgebra.Defs","kind":"def"},{"where":"body","name":"AddMonoidAlgebra.singleZeroRingHom","module":"Mathlib.Algebra.MonoidAlgebra.Defs","kind":"def"},{"where":"body","name":"AddMonoidAlgebra.smulZeroClass","module":"Mathlib.Algebra.MonoidAlgebra.Defs","kind":"def"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":86,"column":2},"end":{"line":89,"column":61}},
      "name": "AddMonoidAlgebra.algebra",
      "module": "Mathlib.Algebra.MonoidAlgebra.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {A : Type u_4} →\n    {M : Type u_7} →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] → [Algebra R A] → [inst_3 : AddMonoid M] → Algebra R (AddMonoidAlgebra A M)",
      "doc": "The instance `Algebra R R[M]` whenever we have `Algebra R R`.\n\nIn particular this provides the instance `Algebra R R[M]`. ",
      "short": "algebra",
      "signature_source": "@[to_additive (dont_translate := R A)\n/-- The instance `Algebra R R[M]` whenever we have `Algebra R R`.\n\nIn particular this provides the instance `Algebra R R[M]`. -/]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
