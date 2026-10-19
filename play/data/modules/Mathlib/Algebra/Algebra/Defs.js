window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Defs"] = {
  "module": "Mathlib.Algebra.Algebra.Defs",
  "cards": {
    "Algebra": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":91,"column":0},"end":{"line":99,"column":45}},
      "name": "Algebra",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (A : Type v) → [CommSemiring R] → [Semiring A] → Type (max u v)",
      "doc": "An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.\n\nSee the implementation notes in this file for discussion of the details of this definition.\n",
      "short": "Algebra",
      "signature_source": "class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where\n  /-- Embedding `R →+* A` given by `Algebra` structure. -/\n  algebraMap (R) (A) : R →+* A\n  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r\n  smul_def' : ∀ r x, r • x = algebraMap r * x",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "Algebra.id": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":384,"column":0},"end":{"line":390,"column":32}},
      "name": "Algebra.id",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u) → [inst : CommSemiring R] → Algebra R R",
      "doc": "The identity map inducing an `Algebra` structure. ",
      "short": "id",
      "signature_source": "instance (priority := 1100) id : Algebra R R where\n  -- We override `toFun` and `toSMul` because `RingHom.id` is not reducible and cannot\n  -- be made so without a significant performance hit.\n  -- see library note [reducible non-instances].\n  toSMul := instSMulOfMul\n  __ := (RingHom.id R).toAlgebra",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
