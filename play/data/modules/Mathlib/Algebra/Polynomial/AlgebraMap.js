window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.AlgebraMap"] = {
  "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
  "cards": {
    "Polynomial.algebraOfAlgebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.smulZeroClass","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":54,"column":0},"end":{"line":66,"column":39}},
      "name": "Polynomial.algebraOfAlgebra",
      "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
      "kind": "def",
      "elaborated_type": "{R : Type u} → {A : Type z} → [inst : CommSemiring R] → [inst_1 : Semiring A] → [Algebra R A] → Algebra R (Polynomial A)",
      "doc": "Note that this instance also provides `Algebra R R[X]`. ",
      "short": "algebraOfAlgebra",
      "signature_source": "instance algebraOfAlgebra : Algebra R A[X] where\n  smul_def' r p :=\n    toFinsupp_injective <| by\n      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]\n      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]\n      exact Algebra.smul_def' _ _\n  commutes' r p :=\n    toFinsupp_injective <| by\n      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]\n      simp_rw [toFinsupp_mul, toFinsupp_C]\n      convert! Algebra.commutes' r p.toFinsupp\n  algebraMap := C.comp (algebraMap R A)",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
