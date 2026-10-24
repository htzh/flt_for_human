window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula"] = {
  "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula",
  "cards": {
    "WeierstrassCurve.Affine.negPolynomial": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"abbrev"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.a₁","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"body","name":"WeierstrassCurve.a₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"}],
      "range": {"start":{"line":94,"column":0},"end":{"line":97,"column":44}},
      "name": "WeierstrassCurve.Affine.negPolynomial",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve.Affine R → Polynomial (Polynomial R)",
      "doc": "The negation polynomial `-Y - a₁X - a₃` associated to the negation of a nonsingular affine point\non a Weierstrass curve. ",
      "short": "negPolynomial",
      "signature_source": "noncomputable def negPolynomial : R[X][Y] :=",
      "body_source": "-(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean",
      "has_source": true,
      "has_refs": true
    },
    "WeierstrassCurve.Affine.negY": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"abbrev"},{"where":"body","name":"WeierstrassCurve.a₁","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"},{"where":"body","name":"WeierstrassCurve.a₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"abbrev"}],
      "range": {"start":{"line":115,"column":0},"end":{"line":121,"column":24}},
      "name": "WeierstrassCurve.Affine.negY",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [CommRing R] → WeierstrassCurve.Affine R → R → R → R",
      "doc": "The `Y`-coordinate of `-(x, y)` for a nonsingular affine point `(x, y)` on a Weierstrass curve\n`W`.\n\nThis depends on `W`, and has argument order: `x`, `y`. ",
      "short": "negY",
      "signature_source": "@[simp, implicit_reducible]\ndef negY (x y : R) : R :=",
      "body_source": "-y - W'.a₁ * x - W'.a₃",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
