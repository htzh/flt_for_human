window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic"] = {
  "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
  "cards": {
    "WeierstrassCurve.Affine": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":73,"column":0},"end":{"line":75,"column":20}},
      "name": "WeierstrassCurve.Affine",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
      "kind": "abbrev",
      "elaborated_type": "Type r → Type r",
      "doc": "An abbreviation for a Weierstrass curve in affine coordinates. ",
      "short": "Affine",
      "signature_source": "abbrev Affine : Type r :=",
      "body_source": "WeierstrassCurve R",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "WeierstrassCurve.Affine.Equation": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":146,"column":0},"end":{"line":150,"column":31}},
      "name": "WeierstrassCurve.Affine.Equation",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [CommRing R] → WeierstrassCurve.Affine R → R → R → Prop",
      "doc": "The proposition that an affine point `(x, y)` lies in a Weierstrass curve `W`.\n\nIn other words, it satisfies the Weierstrass equation `W(X, Y) = 0`. ",
      "short": "Equation",
      "signature_source": "def Equation (x y : R) : Prop :=",
      "body_source": "W.polynomial.evalEval x y = 0",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.Nonsingular": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":205,"column":0},"end":{"line":212,"column":84}},
      "name": "WeierstrassCurve.Affine.Nonsingular",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [CommRing R] → WeierstrassCurve.Affine R → R → R → Prop",
      "doc": "The proposition that an affine point `(x, y)` on a Weierstrass curve `W` is nonsingular.\n\nIn other words, either `W_X(x, y) ≠ 0` or `W_Y(x, y) ≠ 0`.\n\nNote that this definition is only mathematically accurate for fields. ",
      "short": "Nonsingular",
      "signature_source": "-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.\ndef Nonsingular (x y : R) : Prop :=",
      "body_source": "W.Equation x y ∧ (W.polynomialX.evalEval x y ≠ 0 ∨ W.polynomialY.evalEval x y ≠ 0)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.polynomial": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":89,"column":0},"end":{"line":97,"column":88}},
      "name": "WeierstrassCurve.Affine.polynomial",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve.Affine R → Polynomial (Polynomial R)",
      "doc": "The polynomial `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)` associated to a Weierstrass\ncurve `W` over a ring `R` in affine coordinates.\n\nFor ease of polynomial manipulation, this is represented as a term of type `R[X][X]`, where the\ninner variable represents `X` and the outer variable represents `Y`. For clarity, the alternative\nnotations `Y` and `R[X][Y]` are provided in the `Polynomial.Bivariate` scope to represent the outer\nvariable and the bivariate polynomial ring `R[X][X]` respectively. ",
      "short": "polynomial",
      "signature_source": "noncomputable def polynomial : R[X][Y] :=",
      "body_source": "Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.polynomialX": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":173,"column":0},"end":{"line":177,"column":62}},
      "name": "WeierstrassCurve.Affine.polynomialX",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve.Affine R → Polynomial (Polynomial R)",
      "doc": "The partial derivative `W_X(X, Y)` with respect to `X` of the polynomial `W(X, Y)` associated to\na Weierstrass curve `W` in affine coordinates. ",
      "short": "polynomialX",
      "signature_source": "-- TODO: define this in terms of `Polynomial.derivative`.\nnoncomputable def polynomialX : R[X][Y] :=",
      "body_source": "C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.polynomialY": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":189,"column":0},"end":{"line":193,"column":39}},
      "name": "WeierstrassCurve.Affine.polynomialY",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve.Affine R → Polynomial (Polynomial R)",
      "doc": "The partial derivative `W_Y(X, Y)` with respect to `Y` of the polynomial `W(X, Y)` associated to\na Weierstrass curve `W` in affine coordinates. ",
      "short": "polynomialY",
      "signature_source": "-- TODO: define this in terms of `Polynomial.derivative`.\nnoncomputable def polynomialY : R[X][Y] :=",
      "body_source": "C (C 2) * Y + C (C W.a₁ * X + C W.a₃)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
