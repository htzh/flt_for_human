window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.MvPolynomial.Eval"] = {
  "module": "Mathlib.Algebra.MvPolynomial.Eval",
  "cards": {
    "MvPolynomial.aeval": {
      "refs": [{"where":"type","name":"AddMonoidAlgebra.algebra","module":"Mathlib.Algebra.MonoidAlgebra.Basic","kind":"def"},{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"MvPolynomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"AddMonoidAlgebra.nonAssocSemiring","module":"Mathlib.Algebra.MonoidAlgebra.Defs","kind":"def"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"MvPolynomial.eval₂Hom","module":"Mathlib.Algebra.MvPolynomial.Eval","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
      "range": {"start":{"line":567,"column":0},"end":{"line":570,"column":76}},
      "name": "MvPolynomial.aeval",
      "module": "Mathlib.Algebra.MvPolynomial.Eval",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {S₁ : Type v} →\n    {σ : Type u_1} →\n      [inst : CommSemiring R] →\n        [inst_1 : CommSemiring S₁] → [inst_2 : Algebra R S₁] → (σ → S₁) → MvPolynomial σ R →ₐ[R] S₁",
      "doc": "A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism\nfrom multivariate polynomials over `σ` to `S₁`. ",
      "short": "aeval",
      "signature_source": "def aeval : MvPolynomial σ R →ₐ[R] S₁ :=",
      "body_source": "{ eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
