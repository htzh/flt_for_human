window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.Bridge"] = {
  "module": "FLTForHuman.Elliptic.Bridge",
  "cards": {
    "FLTForHuman.Elliptic.evalEval_φ": {
      "seed": true,
      "refs": [{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.eval","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Polynomial.evalEval","module":"Mathlib.Algebra.Polynomial.Bivariate","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.Equation","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.Φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.φ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":45,"column":0},"end":{"line":51,"column":10}},
      "name": "FLTForHuman.Elliptic.evalEval_φ",
      "module": "FLTForHuman.Elliptic.Bridge",
      "kind": "theorem",
      "elaborated_type": "∀ {F : Type u_1} [inst : Field F] (W : WeierstrassCurve F) {x y : F},\n  W.toAffine.Equation x y → ∀ (n : ℤ), Polynomial.evalEval x y (W.φ n) = Polynomial.eval x (W.Φ n)",
      "doc": "",
      "short": "evalEval_φ",
      "signature_source": "theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :\n    (W.φ n).evalEval x y = (W.Φ n).eval x :=",
      "body_source": "by\n  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)\n  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h\n  have h1 := congrArg (evalEval x y) hp\n  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1\n  exact h1",
      "source_file": "lean/FLTForHuman/Elliptic/Bridge.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "FLTForHuman.Elliptic.evalEval_ψ_sq": {
      "seed": true,
      "refs": [{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.eval","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Polynomial.evalEval","module":"Mathlib.Algebra.Polynomial.Bivariate","kind":"abbrev"},{"where":"type","name":"WeierstrassCurve","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","kind":"inductive"},{"where":"type","name":"WeierstrassCurve.Affine.Equation","module":"Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ΨSq","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"WeierstrassCurve.ψ","module":"Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":26,"column":0},"end":{"line":42,"column":44}},
      "name": "FLTForHuman.Elliptic.evalEval_ψ_sq",
      "module": "FLTForHuman.Elliptic.Bridge",
      "kind": "theorem",
      "elaborated_type": "∀ {F : Type u_1} [inst : Field F] (W : WeierstrassCurve F) {x y : F},\n  W.toAffine.Equation x y → ∀ (n : ℤ), Polynomial.evalEval x y (W.ψ n) ^ 2 = Polynomial.eval x (W.ΨSq n)",
      "doc": "",
      "short": "evalEval_ψ_sq",
      "signature_source": "theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :\n    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x :=",
      "body_source": "by\n  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by\n    rw [eval₂_evalRingHom]; exact h\n  let e : W.toAffine.CoordinateRing →+* F := AdjoinRoot.lift (evalRingHom x) y h0\n  have he : ∀ p : F[X][Y], e (WeierstrassCurve.Affine.CoordinateRing.mk W p) = p.evalEval x y :=\n    fun p ↦ by\n      show AdjoinRoot.lift (evalRingHom x) y h0 (AdjoinRoot.mk _ p) = _\n      rw [AdjoinRoot.lift_mk, eval₂_evalRingHom]\n  calc ((W.ψ n).evalEval x y) ^ 2\n      = e (WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n)) ^ 2 := by rw [he]\n    _ = e (WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n) ^ 2) := (map_pow e _ 2).symm\n    _ = e (WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by\n        rw [WeierstrassCurve.Affine.CoordinateRing.mk_ψ,\n          WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]\n    _ = (C (W.ΨSq n)).evalEval x y := he _\n    _ = (W.ΨSq n).eval x := evalEval_C x y _",
      "source_file": "lean/FLTForHuman/Elliptic/Bridge.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
