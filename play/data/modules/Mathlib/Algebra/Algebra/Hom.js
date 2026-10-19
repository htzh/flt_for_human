window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Hom"] = {
  "module": "Mathlib.Algebra.Algebra.Hom",
  "cards": {
    "AlgHom": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":29,"column":0},"end":{"line":32,"column":66}},
      "name": "AlgHom",
      "module": "Mathlib.Algebra.Algebra.Hom",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) →\n  (A : Type v) →\n    (B : Type w) →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] → [Algebra R B] → Type (max v w)",
      "doc": "Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`. ",
      "short": "AlgHom",
      "signature_source": "structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends RingHom A B where\n  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "AlgHom.funLike": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":88,"column":0},"end":{"line":94,"column":9}},
      "name": "AlgHom.funLike",
      "module": "Mathlib.Algebra.Algebra.Hom",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {A : Type v} →\n    {B : Type w} →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] →\n          [inst_2 : Semiring B] → [inst_3 : Algebra R A] → [inst_4 : Algebra R B] → FunLike (A →ₐ[R] B) A B",
      "doc": "",
      "short": "funLike",
      "signature_source": "@[macro_inline]\ninstance funLike : FunLike (A →ₐ[R] B) A B where\n  coe f := f.toFun\n  coe_injective f g h := by\n    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩\n    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩\n    congr",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
