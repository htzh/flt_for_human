window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass"] = {
  "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
  "cards": {
    "WeierstrassCurve": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":75,"column":0},"end":{"line":87,"column":8}},
      "name": "WeierstrassCurve",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "inductive",
      "elaborated_type": "Type u → Type u",
      "doc": "A Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` with parameters `aᵢ`. ",
      "short": "WeierstrassCurve",
      "signature_source": "@[ext]\nstructure WeierstrassCurve (R : Type u) where\n  /-- The `a₁` coefficient of a Weierstrass curve. -/\n  a₁ : R\n  /-- The `a₂` coefficient of a Weierstrass curve. -/\n  a₂ : R\n  /-- The `a₃` coefficient of a Weierstrass curve. -/\n  a₃ : R\n  /-- The `a₄` coefficient of a Weierstrass curve. -/\n  a₄ : R\n  /-- The `a₆` coefficient of a Weierstrass curve. -/\n  a₆ : R",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.IsElliptic": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":363,"column":0},"end":{"line":368,"column":21}},
      "name": "WeierstrassCurve.IsElliptic",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "inductive",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → Prop",
      "doc": "`WeierstrassCurve.IsElliptic` is a typeclass which asserts that a Weierstrass curve is an\nelliptic curve: that its discriminant is a unit. Note that this definition is only mathematically\naccurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. ",
      "short": "IsElliptic",
      "signature_source": "@[mk_iff]\nprotected class IsElliptic : Prop where\n  isUnit : IsUnit W.Δ",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.a₁": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":79,"column":2},"end":{"line":79,"column":4}},
      "name": "WeierstrassCurve.a₁",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "abbrev",
      "elaborated_type": "{R : Type u} → WeierstrassCurve R → R",
      "doc": "The `a₁` coefficient of a Weierstrass curve. ",
      "short": "a₁",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.a₃": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":83,"column":2},"end":{"line":83,"column":4}},
      "name": "WeierstrassCurve.a₃",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "abbrev",
      "elaborated_type": "{R : Type u} → WeierstrassCurve R → R",
      "doc": "The `a₃` coefficient of a Weierstrass curve. ",
      "short": "a₃",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.baseChange": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":235,"column":0},"end":{"line":237,"column":25}},
      "name": "WeierstrassCurve.baseChange",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  [inst : CommRing R] → WeierstrassCurve R → (A : Type v) → [inst_1 : CommRing A] → [Algebra R A] → WeierstrassCurve A",
      "doc": "The Weierstrass curve base changed to an algebra `A` over `R`. ",
      "short": "baseChange",
      "signature_source": "def baseChange [Algebra R A] : WeierstrassCurve A :=",
      "body_source": "W.map <| algebraMap R A",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.b₂": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":100,"column":0},"end":{"line":102,"column":21}},
      "name": "WeierstrassCurve.b₂",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → R",
      "doc": "The `b₂` coefficient of a Weierstrass curve. ",
      "short": "b₂",
      "signature_source": "def b₂ : R :=",
      "body_source": "W.a₁ ^ 2 + 4 * W.a₂",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.b₄": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":104,"column":0},"end":{"line":106,"column":24}},
      "name": "WeierstrassCurve.b₄",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → R",
      "doc": "The `b₄` coefficient of a Weierstrass curve. ",
      "short": "b₄",
      "signature_source": "def b₄ : R :=",
      "body_source": "2 * W.a₄ + W.a₁ * W.a₃",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.b₆": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":108,"column":0},"end":{"line":110,"column":21}},
      "name": "WeierstrassCurve.b₆",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → R",
      "doc": "The `b₆` coefficient of a Weierstrass curve. ",
      "short": "b₆",
      "signature_source": "def b₆ : R :=",
      "body_source": "W.a₃ ^ 2 + 4 * W.a₆",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.b₈": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":112,"column":0},"end":{"line":114,"column":85}},
      "name": "WeierstrassCurve.b₈",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → R",
      "doc": "The `b₈` coefficient of a Weierstrass curve. ",
      "short": "b₈",
      "signature_source": "def b₈ : R :=",
      "body_source": "W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.isElliptic_iff": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsUnit","module":"Mathlib.Algebra.Group.Units.Defs","kind":"def"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.IsElliptic","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Δ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"}],
      "range": {"start":{"line":366,"column":2},"end":{"line":366,"column":8}},
      "name": "WeierstrassCurve.isElliptic_iff",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] (W : WeierstrassCurve R), W.IsElliptic ↔ IsUnit W.Δ",
      "doc": "",
      "short": "isElliptic_iff",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "WeierstrassCurve.mk": {
      "seed": true,
      "refs": [{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"}],
      "range": {"start":{"line":77,"column":10},"end":{"line":77,"column":26}},
      "name": "WeierstrassCurve.mk",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "constructor",
      "elaborated_type": "{R : Type u} → R → R → R → R → R → WeierstrassCurve R",
      "doc": "",
      "short": "mk",
      "signature_source": "structure WeierstrassCurve (R : Type u) where",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.twoTorsionPolynomial": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":302,"column":0},"end":{"line":306,"column":27}},
      "name": "WeierstrassCurve.twoTorsionPolynomial",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → Cubic R",
      "doc": "A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If\n`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a\nsplitting field of `R` are precisely the `X`-coordinates of the non-zero 2-torsion points of `W`. ",
      "short": "twoTorsionPolynomial",
      "signature_source": "def twoTorsionPolynomial : Cubic R :=",
      "body_source": "⟨4, W.b₂, 2 * W.b₄, W.b₆⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Δ": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":128,"column":0},"end":{"line":133,"column":74}},
      "name": "WeierstrassCurve.Δ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommRing R] → WeierstrassCurve R → R",
      "doc": "The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes\nif and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to\nsign in the literature; we choose the sign used by the LMFDB. For more discussion, see\n[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). ",
      "short": "Δ",
      "signature_source": "def Δ : R :=",
      "body_source": "-W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
