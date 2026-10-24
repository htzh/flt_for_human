window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree"] = {
  "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree",
  "cards": {
    "WeierstrassCurve.natDegree_Φ": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nontrivial","module":"Mathlib.Basic.Nontrivial.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.natDegree","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Int.natAbs","module":"Init.Data.Int.Basic","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":436,"column":0},"end":{"line":438,"column":81}},
      "name": "WeierstrassCurve.natDegree_Φ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] (W : WeierstrassCurve R) [Nontrivial R] (n : ℤ), (W.Φ n).natDegree = n.natAbs ^ 2",
      "doc": "",
      "short": "natDegree_Φ",
      "signature_source": "@[simp]\nlemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=",
      "body_source": "natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean",
      "has_source": true,
      "has_refs": true
    },
    "WeierstrassCurve.natDegree_ΨSq": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"NoZeroDivisors","module":"Mathlib.Algebra.GroupWithZero.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.natDegree","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.ΨSq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Int.cast","module":"Init.Data.Int.Basic","kind":"def"},{"where":"type","name":"Int.natAbs","module":"Init.Data.Int.Basic","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":361,"column":0},"end":{"line":364,"column":85}},
      "name": "WeierstrassCurve.natDegree_ΨSq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] (W : WeierstrassCurve R) [NoZeroDivisors R] {n : ℤ},\n  ↑n ≠ 0 → (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1",
      "doc": "",
      "short": "natDegree_ΨSq",
      "signature_source": "@[simp]\nlemma natDegree_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :\n    (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=",
      "body_source": "natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) <| W.coeff_ΨSq_ne_zero h",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
