window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Derivation"] = {
  "module": "Mathlib.Algebra.Polynomial.Derivation",
  "cards": {
    "Polynomial.derivative'": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.derivative","module":"Mathlib.Algebra.Polynomial.Derivative","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":32,"column":0},"end":{"line":39,"column":62}},
      "name": "Polynomial.derivative'",
      "module": "Mathlib.Algebra.Polynomial.Derivation",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : CommSemiring R] → Derivation R (Polynomial R) (Polynomial R)",
      "doc": "`Polynomial.derivative` as a derivation. ",
      "short": "derivative'",
      "signature_source": "@[simps]\ndef derivative' : Derivation R R[X] R[X] where\n  toFun := derivative\n  map_add' _ _ := derivative_add\n  map_smul' := derivative_smul\n  map_one_eq_zero' := derivative_one\n  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Derivation.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
