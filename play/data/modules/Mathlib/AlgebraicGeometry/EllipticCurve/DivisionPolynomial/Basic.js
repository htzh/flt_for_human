window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic"] = {
  "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
  "cards": {
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing.mk","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.polynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ΨSq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":338,"column":0},"end":{"line":340,"column":21}},
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ),\n  (WeierstrassCurve.Affine.CoordinateRing.mk W) (W.Ψ n) ^ 2 =\n    (WeierstrassCurve.Affine.CoordinateRing.mk W) (Polynomial.C (W.ΨSq n))",
      "doc": "",
      "short": "mk_Ψ_sq",
      "signature_source": "lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) :=",
      "body_source": "by\n  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,\n    one_pow, map_pow]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing.mk","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.polynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":482,"column":0},"end":{"line":485,"column":72}},
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_φ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ),\n  (WeierstrassCurve.Affine.CoordinateRing.mk W) (W.φ n) =\n    (WeierstrassCurve.Affine.CoordinateRing.mk W) (Polynomial.C (W.Φ n))",
      "doc": "",
      "short": "mk_φ",
      "signature_source": "lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) :=",
      "body_source": "by\n  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,\n    mul_mul_mul_comm _ <| mk W <| ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,\n    apply_ite C, apply_ite <| mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing.mk","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.polynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":438,"column":0},"end":{"line":439,"column":88}},
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ),\n  (WeierstrassCurve.Affine.CoordinateRing.mk W) (W.ψ n) = (WeierstrassCurve.Affine.CoordinateRing.mk W) (W.Ψ n)",
      "doc": "",
      "short": "mk_ψ",
      "signature_source": "lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) :=",
      "body_source": "by\n  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.CoordinateRing.mk","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve.Affine.polynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":128,"column":0},"end":{"line":129,"column":15}},
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R),\n  (WeierstrassCurve.Affine.CoordinateRing.mk W) W.ψ₂ ^ 2 =\n    (WeierstrassCurve.Affine.CoordinateRing.mk W) (Polynomial.C W.Ψ₂Sq)",
      "doc": "",
      "short": "mk_ψ₂_sq",
      "signature_source": "lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) :=",
      "body_source": "by\n  simp [C_Ψ₂Sq]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.C_Ψ₂Sq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.polynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":120,"column":0},"end":{"line":123,"column":7}},
      "name": "WeierstrassCurve.C_Ψ₂Sq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), Polynomial.C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial",
      "doc": "",
      "short": "C_Ψ₂Sq",
      "signature_source": "lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial :=",
      "body_source": "by\n  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]\n  C_simp\n  ring1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.preΨ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"preNormEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":192,"column":0},"end":{"line":195,"column":40}},
      "name": "WeierstrassCurve.preΨ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial R",
      "doc": "The univariate polynomials `preΨₙ` for `n ∈ ℤ`, which are auxiliary to the bivariate polynomials\n`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. ",
      "short": "preΨ",
      "signature_source": "noncomputable def preΨ (n : ℤ) : R[X] :=",
      "body_source": "preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.preΨ'": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"preNormEDS'","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"}],
      "range": {"start":{"line":151,"column":0},"end":{"line":154,"column":41}},
      "name": "WeierstrassCurve.preΨ'",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℕ → Polynomial R",
      "doc": "The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate polynomials\n`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. ",
      "short": "preΨ'",
      "signature_source": "noncomputable def preΨ' (n : ℕ) : R[X] :=",
      "body_source": "preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.preΨ_even": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.preΨ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":225,"column":0},"end":{"line":228,"column":20}},
      "name": "WeierstrassCurve.preΨ_even",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R) (m : ℤ),\n  W.preΨ (2 * m) = W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2",
      "doc": "",
      "short": "preΨ_even",
      "signature_source": "lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =\n    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -\n      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=",
      "body_source": "preNormEDS_even ..",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.preΨ_odd": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.preΨ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":230,"column":0},"end":{"line":233,"column":19}},
      "name": "WeierstrassCurve.preΨ_odd",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R) (m : ℤ),\n  W.preΨ (2 * m + 1) =\n    (W.preΨ (m + 2) * W.preΨ m ^ 3 * if Even m then W.Ψ₂Sq ^ 2 else 1) -\n      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * if Even m then 1 else W.Ψ₂Sq ^ 2",
      "doc": "",
      "short": "preΨ_odd",
      "signature_source": "lemma preΨ_odd (m : ℤ) : W.preΨ (2 * m + 1) =\n    W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -\n      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=",
      "body_source": "preNormEDS_odd ..",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.preΨ₄": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.b₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₆","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₈","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":145,"column":0},"end":{"line":149,"column":66}},
      "name": "WeierstrassCurve.preΨ₄",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → Polynomial R",
      "doc": "The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial\n`ψ₄ = Ψ₄ = preΨ₄ψ₂`. ",
      "short": "preΨ₄",
      "signature_source": "noncomputable def preΨ₄ : R[X] :=",
      "body_source": "2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +\n    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Φ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.preΨ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.ΨSq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"}],
      "range": {"start":{"line":348,"column":0},"end":{"line":350,"column":78}},
      "name": "WeierstrassCurve.Φ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial R",
      "doc": "The univariate polynomials `Φₙ` congruent to `φₙ`. ",
      "short": "Φ",
      "signature_source": "protected noncomputable def Φ (n : ℤ) : R[X] :=",
      "body_source": "X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Φ_neg": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":389,"column":0},"end":{"line":392,"column":55}},
      "name": "WeierstrassCurve.Φ_neg",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R) (n : ℤ), W.Φ (-n) = W.Φ n",
      "doc": "",
      "short": "Φ_neg",
      "signature_source": "@[simp]\nlemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n :=",
      "body_source": "by\n  simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg,\n    neg_mul_neg, mul_comm <| W.preΨ <| n - 1, even_neg]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Φ_three": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":377,"column":0},"end":{"line":380,"column":57}},
      "name": "WeierstrassCurve.Φ_three",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), W.Φ 3 = Polynomial.X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq",
      "doc": "",
      "short": "Φ_three",
      "signature_source": "@[simp]\nlemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq :=",
      "body_source": "by\n  rw [show 3 = ((2 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_three, ite_eq_left <| by decide, mul_one,\n    preΨ'_four, preΨ'_two, mul_one, ite_eq_left even_two]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Ψ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.preΨ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"}],
      "range": {"start":{"line":289,"column":0},"end":{"line":291,"column":43}},
      "name": "WeierstrassCurve.Ψ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial (Polynomial R)",
      "doc": "The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`. ",
      "short": "Ψ",
      "signature_source": "protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=",
      "body_source": "C (W.preΨ n) * if Even n then W.ψ₂ else 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ΨSq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"WeierstrassCurve.preΨ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":241,"column":0},"end":{"line":243,"column":45}},
      "name": "WeierstrassCurve.ΨSq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial R",
      "doc": "The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`. ",
      "short": "ΨSq",
      "signature_source": "noncomputable def ΨSq (n : ℤ) : R[X] :=",
      "body_source": "W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ΨSq_three": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.ΨSq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":261,"column":0},"end":{"line":263,"column":42}},
      "name": "WeierstrassCurve.ΨSq_three",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), W.ΨSq 3 = W.Ψ₃ ^ 2",
      "doc": "",
      "short": "ΨSq_three",
      "signature_source": "@[simp]\nlemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 :=",
      "body_source": "by\n  simp [ΨSq, show ¬Even (3 : ℤ) by decide]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Ψ₂Sq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.b₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₆","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":116,"column":0},"end":{"line":118,"column":58}},
      "name": "WeierstrassCurve.Ψ₂Sq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → Polynomial R",
      "doc": "The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`. ",
      "short": "Ψ₂Sq",
      "signature_source": "noncomputable def Ψ₂Sq : R[X] :=",
      "body_source": "C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Ψ₂Sq_eq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.twoTorsionPolynomial","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"type","name":"WeierstrassCurve.Ψ₂Sq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"}],
      "range": {"start":{"line":132,"column":0},"end":{"line":133,"column":5}},
      "name": "WeierstrassCurve.Ψ₂Sq_eq",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly",
      "doc": "",
      "short": "Ψ₂Sq_eq",
      "signature_source": "lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=",
      "body_source": "rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.Ψ₃": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.b₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₆","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"WeierstrassCurve.b₈","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":141,"column":0},"end":{"line":143,"column":75}},
      "name": "WeierstrassCurve.Ψ₃",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → Polynomial R",
      "doc": "The `3`-division polynomial `ψ₃ = Ψ₃`. ",
      "short": "Ψ₃",
      "signature_source": "noncomputable def Ψ₃ : R[X] :=",
      "body_source": "3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.φ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":447,"column":0},"end":{"line":449,"column":45}},
      "name": "WeierstrassCurve.φ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial (Polynomial R)",
      "doc": "The bivariate polynomials `φₙ`. ",
      "short": "φ",
      "signature_source": "protected noncomputable def φ (n : ℤ) : R[X][Y] :=",
      "body_source": "C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ψ": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.preΨ₄","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.Ψ₃","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"body","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"}],
      "range": {"start":{"line":400,"column":0},"end":{"line":402,"column":37}},
      "name": "WeierstrassCurve.ψ",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → ℤ → Polynomial (Polynomial R)",
      "doc": "The bivariate `n`-division polynomials `ψₙ`. ",
      "short": "ψ",
      "signature_source": "protected noncomputable def ψ (n : ℤ) : R[X][Y] :=",
      "body_source": "normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ψ_one": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":410,"column":0},"end":{"line":412,"column":16}},
      "name": "WeierstrassCurve.ψ_one",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), W.ψ 1 = 1",
      "doc": "",
      "short": "ψ_one",
      "signature_source": "@[simp]\nlemma ψ_one : W.ψ 1 = 1 :=",
      "body_source": "normEDS_one ..",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ψ_two": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ₂","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":414,"column":0},"end":{"line":416,"column":16}},
      "name": "WeierstrassCurve.ψ_two",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), W.ψ 2 = W.ψ₂",
      "doc": "",
      "short": "ψ_two",
      "signature_source": "@[simp]\nlemma ψ_two : W.ψ 2 = W.ψ₂ :=",
      "body_source": "normEDS_two ..",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ψ_zero": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":406,"column":0},"end":{"line":408,"column":17}},
      "name": "WeierstrassCurve.ψ_zero",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type r} [inst : CommRing R] (W : WeierstrassCurve R), W.ψ 0 = 0",
      "doc": "",
      "short": "ψ_zero",
      "signature_source": "@[simp]\nlemma ψ_zero : W.ψ 0 = 0 :=",
      "body_source": "normEDS_zero ..",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "WeierstrassCurve.ψ₂": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"body","name":"WeierstrassCurve.Affine.polynomialY","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"}],
      "range": {"start":{"line":112,"column":0},"end":{"line":114,"column":24}},
      "name": "WeierstrassCurve.ψ₂",
      "module": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type r} → [inst : CommRing R] → WeierstrassCurve R → Polynomial (Polynomial R)",
      "doc": "The `2`-division polynomial `ψ₂ = Ψ₂`. ",
      "short": "ψ₂",
      "signature_source": "noncomputable def ψ₂ : R[X][Y] :=",
      "body_source": "W.toAffine.polynomialY",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
