window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Equiv"] = {
  "module": "Mathlib.Algebra.Algebra.Equiv",
  "cards": {
    "AlgEquiv": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":29,"column":0},"end":{"line":34,"column":76}},
      "name": "AlgEquiv",
      "module": "Mathlib.Algebra.Algebra.Equiv",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) →\n  (A : Type v) →\n    (B : Type w) →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] → [Algebra R B] → Type (max v w)",
      "doc": "An equivalence of algebras (denoted as `A ≃ₐ[R] B`)\nis an equivalence of rings commuting with the actions of scalars. ",
      "short": "AlgEquiv",
      "signature_source": "structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where\n  /-- An equivalence of algebras commutes with the action of scalars. -/\n  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
