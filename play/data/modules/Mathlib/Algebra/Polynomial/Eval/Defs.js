window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Eval.Defs"] = {
  "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
  "cards": {
    "Polynomial.eval": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":249,"column":0},"end":{"line":251,"column":26}},
      "name": "Polynomial.eval",
      "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → R → Polynomial R → R",
      "doc": "`eval x p` is the evaluation of the polynomial `p` at `x` ",
      "short": "eval",
      "signature_source": "def eval (x : R) (p : R[X]) : R :=",
      "body_source": "eval₂ (RingHom.id _) x p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
