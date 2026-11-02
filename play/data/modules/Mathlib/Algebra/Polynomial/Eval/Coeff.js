window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Eval.Coeff"] = {
  "module": "Mathlib.Algebra.Polynomial.Eval.Coeff",
  "cards": {
    "Polynomial.eval₂_map": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":137,"column":0},"end":{"line":139,"column":52}},
      "name": "Polynomial.eval₂_map",
      "module": "Mathlib.Algebra.Polynomial.Eval.Coeff",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {S : Type v} {T : Type w} [inst : Semiring R] {p : Polynomial R} [inst_1 : Semiring S] (f : R →+* S)\n  [inst_2 : Semiring T] (g : S →+* T) (x : T),\n  Polynomial.eval₂ g x (Polynomial.map f p) = Polynomial.eval₂ (g.comp f) x p",
      "doc": "",
      "short": "eval₂_map",
      "signature_source": "theorem eval₂_map [Semiring T] (g : S →+* T) (x : T) :\n    (p.map f).eval₂ g x = p.eval₂ (g.comp f) x :=",
      "body_source": "by\n  rw [eval₂_eq_eval_map, eval₂_eq_eval_map, map_map]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Coeff.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
