window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Kaehler.Polynomial"] = {
  "module": "Mathlib.RingTheory.Kaehler.Polynomial",
  "cards": {
    "KaehlerDifferential.mvPolynomialBasis": {
      "refs": [{"where":"type","name":"AddMonoidAlgebra.algebra","module":"Mathlib.Algebra.MonoidAlgebra.Basic","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"MvPolynomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"KaehlerDifferential.mvPolynomialEquiv","module":"Mathlib.RingTheory.Kaehler.Polynomial","kind":"def"}],
      "range": {"start":{"line":58,"column":0},"end":{"line":62,"column":25}},
      "name": "KaehlerDifferential.mvPolynomialBasis",
      "module": "Mathlib.RingTheory.Kaehler.Polynomial",
      "kind": "def",
      "elaborated_type": "(R : Type u) → [inst : CommRing R] → (σ : Type u_1) → Module.Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]",
      "doc": "`{ dx | x ∈ σ }` forms a basis of the relative differential module\nof a polynomial algebra `R[σ]`. ",
      "short": "mvPolynomialBasis",
      "signature_source": "def KaehlerDifferential.mvPolynomialBasis (σ) :\n    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=",
      "body_source": "⟨mvPolynomialEquiv R σ⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
