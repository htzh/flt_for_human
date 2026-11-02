window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Monic"] = {
  "module": "Mathlib.Algebra.Polynomial.Monic",
  "cards": {
    "Polynomial.Monic.natDegree_map": {
      "refs": [{"where":"type","name":"Nontrivial","module":"Mathlib.Basic.Nontrivial.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.Monic","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Polynomial.natDegree","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":396,"column":0},"end":{"line":401,"column":19}},
      "name": "Polynomial.Monic.natDegree_map",
      "module": "Mathlib.Algebra.Polynomial.Monic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {S : Type v} [inst : Semiring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},\n  P.Monic → ∀ (f : R →+* S), (Polynomial.map f P).natDegree = P.natDegree",
      "doc": "",
      "short": "natDegree_map",
      "signature_source": "@[simp]\ntheorem Monic.natDegree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :\n    (P.map f).natDegree = P.natDegree :=",
      "body_source": "by\n  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)\n  rw [coeff_map, Monic.coeff_natDegree hmo, map_one]\n  exact one_ne_zero",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Monic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
