window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.Omega"] = {
  "module": "FLTForHuman.Elliptic.Omega",
  "cards": {
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq": {
      "seed": true,
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.invar","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":35,"column":0},"end":{"line":37,"column":86}},
      "name": "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq",
      "module": "FLTForHuman.Elliptic.Omega",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (W : WeierstrassCurve R),\n  W.preΨ₄ + W.Ψ₂Sq ^ 2 = FLTForHuman.Elliptic.invar W * W.Ψ₃",
      "doc": "",
      "short": "preΨ₄_add_Ψ₂Sq_sq",
      "signature_source": "lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = invar W * W.Ψ₃ :=",
      "body_source": "by\n  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]\n  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2",
      "source_file": "lean/FLTForHuman/Elliptic/Omega.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.two_mul_ωe": {
      "seed": true,
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.ψc","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"FLTForHuman.Elliptic.ωe","module":"FLTForHuman.Elliptic.Omega","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.CC","module":"Mathlib.Algebra.Polynomial.Bivariate","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.a₁","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.a₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":63,"column":0},"end":{"line":65,"column":26}},
      "name": "FLTForHuman.Elliptic.two_mul_ωe",
      "module": "FLTForHuman.Elliptic.Omega",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ),\n  2 * FLTForHuman.Elliptic.ωe W n =\n    FLTForHuman.Elliptic.ψc W n - Polynomial.CC W.a₁ * W.φ n * W.ψ n - Polynomial.CC W.a₃ * W.ψ n ^ 3",
      "doc": "",
      "short": "two_mul_ωe",
      "signature_source": "lemma two_mul_ωe (n : ℤ) :\n    2 * ωe W n = ψc W n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 :=",
      "body_source": "by\n  rw [← ωe_spec W n]; abel",
      "source_file": "lean/FLTForHuman/Elliptic/Omega.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.ωe": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"FLTForHuman.Elliptic.complEDSAux","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"body","name":"FLTForHuman.Elliptic.redInvarDenom","module":"FLTForHuman.Elliptic.RedInvar","kind":"def"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.CC","module":"Mathlib.Algebra.Polynomial.Bivariate","kind":"abbrev"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.Affine.negPolynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula","kind":"def"},{"where":"body","name":"WeierstrassCurve.Affine.polynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Affine.polynomialX","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Affine.polynomialY","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.a₁","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"body","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":48,"column":0},"end":{"line":53,"column":73}},
      "name": "FLTForHuman.Elliptic.ωe",
      "module": "FLTForHuman.Elliptic.Omega",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial (Polynomial R)",
      "doc": "FLT's `WeierstrassCurve.ωe`: the `y`-coordinate numerator of `n • P`. ",
      "short": "ωe",
      "signature_source": "def ωe (n : ℤ) : R[X][Y] :=",
      "body_source": "redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *\n    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃\n      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))\n  - complEDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3",
      "source_file": "lean/FLTForHuman/Elliptic/Omega.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.ωe_spec": {
      "seed": true,
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.ψc","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"FLTForHuman.Elliptic.ωe","module":"FLTForHuman.Elliptic.Omega","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.CC","module":"Mathlib.Algebra.Polynomial.Bivariate","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.a₁","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.a₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":55,"column":0},"end":{"line":61,"column":14}},
      "name": "FLTForHuman.Elliptic.ωe_spec",
      "module": "FLTForHuman.Elliptic.Omega",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ),\n  2 * FLTForHuman.Elliptic.ωe W n + Polynomial.CC W.a₁ * W.φ n * W.ψ n + Polynomial.CC W.a₃ * W.ψ n ^ 3 =\n    FLTForHuman.Elliptic.ψc W n",
      "doc": "",
      "short": "ωe_spec",
      "signature_source": "lemma ωe_spec (n : ℤ) :\n    2 * ωe W n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = ψc W n :=",
      "body_source": "by\n  have hψ : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl\n  rw [ψc, complEDS₂_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four,\n    mul_assoc (C _), φ_mul_ψ, hψ, invarDenom_eq_redInvarDenom_mul, ωe, ← hψ,\n    invar, b₂, b₄, ψ₂, polynomialY, polynomialX, negPolynomial]\n  C_simp; ring",
      "source_file": "lean/FLTForHuman/Elliptic/Omega.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
