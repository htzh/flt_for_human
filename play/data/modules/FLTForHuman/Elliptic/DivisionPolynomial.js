window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.DivisionPolynomial"] = {
  "module": "FLTForHuman.Elliptic.DivisionPolynomial",
  "cards": {
    "FLTForHuman.Elliptic.complEDSAux": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"preNormEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":79,"column":0},"end":{"line":82,"column":29}},
      "name": "FLTForHuman.Elliptic.complEDSAux",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → R",
      "doc": "FLT's `compl₂EDSAux`: the `2`-complement auxiliary sequence. ",
      "short": "complEDSAux",
      "signature_source": "def complEDSAux (m : ℤ) : R :=",
      "body_source": "preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2\n    * if Even m then 1 else b",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.invar": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.b₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":30,"column":0},"end":{"line":32,"column":51}},
      "name": "FLTForHuman.Elliptic.invar",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : CommRing R] → WeierstrassCurve R → Polynomial R",
      "doc": "`6X² + b₂X + b₄`. The identity `preΨ₄ + Ψ₂Sq² = invar * Ψ₃` is what makes the\n`ω` construction go through. ",
      "short": "invar",
      "signature_source": "def invar : R[X] :=",
      "body_source": "6 * X ^ 2 + C W.b₂ * X + C W.b₄",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.invarDenom": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":63,"column":0},"end":{"line":64,"column":71}},
      "name": "FLTForHuman.Elliptic.invarDenom",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → ℤ → ℤ → R",
      "doc": "The denominator invariant of a sequence `u`, `invarDenom u s n`. ",
      "short": "invarDenom",
      "signature_source": "def invarDenom (u : ℤ → R) (s n : ℤ) : R :=",
      "body_source": "u (n + s) * u n * u (n - s)",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.invarNum": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":58,"column":0},"end":{"line":61,"column":29}},
      "name": "FLTForHuman.Elliptic.invarNum",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → ℤ → ℤ → R",
      "doc": "The numerator invariant of a sequence `u`, `invarNum u s n`. ",
      "short": "invarNum",
      "signature_source": "def invarNum (u : ℤ → R) (s n : ℤ) : R :=",
      "body_source": "(u (n + 2 * s) * u (n - s) ^ 2 + u (n + s) ^ 2 * u (n - 2 * s)) * u s ^ 2\n    + u n ^ 3 * u (2 * s) ^ 2",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul": {
      "seed": true,
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.invarNum","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"FLTForHuman.Elliptic.redInvarNum","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":106,"column":0},"end":{"line":110,"column":6}},
      "name": "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  FLTForHuman.Elliptic.invarNum (normEDS b c d) 1 m = FLTForHuman.Elliptic.redInvarNum b c d m * b",
      "doc": "",
      "short": "invarNum_eq_redInvarNum_mul",
      "signature_source": "lemma invarNum_eq_redInvarNum_mul (m : ℤ) :\n    invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b :=",
      "body_source": "by\n  simp_rw [redInvarNum, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b, complEDSAux_mul_b,\n    invarNum_normEDS]\n  ring",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.redInvarNum": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"FLTForHuman.Elliptic.complEDSAux","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"body","name":"complEDS₂","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":96,"column":0},"end":{"line":99,"column":71}},
      "name": "FLTForHuman.Elliptic.redInvarNum",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → R",
      "doc": "FLT's `redInvarNum`, written with mathlib's `complEDS₂` in place of\n`compl₂EDS` (they are definitionally equal). ",
      "short": "redInvarNum",
      "signature_source": "def redInvarNum (m : ℤ) : R :=",
      "body_source": "complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDSAux b c d m",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.ψc": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"complEDS₂","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"}],
      "range": {"start":{"line":34,"column":0},"end":{"line":37,"column":65}},
      "name": "FLTForHuman.Elliptic.ψc",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial (Polynomial R)",
      "doc": "The `2`-complement of the division polynomials, characterised by\n`ψ n * ψc n = ψ (2n)`. This is FLT's `compl₂EDS`, which is definitionally\nmathlib's `complEDS₂`. ",
      "short": "ψc",
      "signature_source": "def ψc (n : ℤ) : R[X][Y] :=",
      "body_source": "complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.ψc_spec": {
      "seed": true,
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.ψc","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":39,"column":0},"end":{"line":43,"column":51}},
      "name": "FLTForHuman.Elliptic.ψc_spec",
      "module": "FLTForHuman.Elliptic.DivisionPolynomial",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ), W.ψ n * FLTForHuman.Elliptic.ψc W n = W.ψ (2 * n)",
      "doc": "The defining property of the `2`-complement. In FLT this is\n`ψc_spec`/`normEDS_mul_compl₂EDS`; here it is mathlib's\n`normEDS_mul_complEDS₂` read through `WeierstrassCurve.ψ`. ",
      "short": "ψc_spec",
      "signature_source": "lemma ψc_spec (n : ℤ) : W.ψ n * ψc W n = W.ψ (2 * n) :=",
      "body_source": "normEDS_mul_complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n",
      "source_file": "lean/FLTForHuman/Elliptic/DivisionPolynomial.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
