window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Degree.Defs"] = {
  "module": "Mathlib.Algebra.Polynomial.Degree.Defs",
  "cards": {
    "Polynomial.degree": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":45,"column":0},"end":{"line":49,"column":15}},
      "name": "Polynomial.degree",
      "module": "Mathlib.Algebra.Polynomial.Degree.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → Polynomial R → WithBot ℕ",
      "doc": "`degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.\n`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise\n`degree 0 = ⊥`. ",
      "short": "degree",
      "signature_source": "def degree (p : R[X]) : WithBot ℕ :=",
      "body_source": "p.support.max",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "Polynomial.natDegree": {
      "seed": true,
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Polynomial.degree","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"body","name":"WithBot.unbotD","module":"Mathlib.Order.WithBot","kind":"def"}],
      "range": {"start":{"line":51,"column":0},"end":{"line":53,"column":21}},
      "name": "Polynomial.natDegree",
      "module": "Mathlib.Algebra.Polynomial.Degree.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → Polynomial R → ℕ",
      "doc": "`natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. ",
      "short": "natDegree",
      "signature_source": "def natDegree (p : R[X]) : ℕ :=",
      "body_source": "(degree p).unbotD 0",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/Defs.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
