window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.MvPolynomial.Basic"] = {
  "module": "Mathlib.Algebra.MvPolynomial.Basic",
  "cards": {
    "MvPolynomial": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AddMonoidAlgebra","module":"Mathlib.Algebra.MonoidAlgebra.Defs","kind":"inductive"},{"where":"body","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":80,"column":0},"end":{"line":83,"column":29}},
      "name": "MvPolynomial",
      "module": "Mathlib.Algebra.MvPolynomial.Basic",
      "kind": "abbrev",
      "elaborated_type": "Type u_1 → (R : Type u_2) → [CommSemiring R] → Type (max u_2 u_1)",
      "doc": "Multivariate polynomial, where `σ` is the index set of the variables and\n`R` is the coefficient ring ",
      "short": "MvPolynomial",
      "signature_source": "abbrev MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=",
      "body_source": "AddMonoidAlgebra R (σ →₀ ℕ)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "MvPolynomial.X": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"MvPolynomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"abbrev"},{"where":"body","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"Finsupp.single","module":"Mathlib.Data.Finsupp.Single","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"MvPolynomial.monomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":125,"column":0},"end":{"line":127,"column":33}},
      "name": "MvPolynomial.X",
      "module": "Mathlib.Algebra.MvPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} → {σ : Type u_1} → [inst : CommSemiring R] → σ → MvPolynomial σ R",
      "doc": "`X n` is the degree `1` monomial $X_n$. ",
      "short": "X",
      "signature_source": "def X (n : σ) : MvPolynomial σ R :=",
      "body_source": "monomial (Finsupp.single n 1) 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
