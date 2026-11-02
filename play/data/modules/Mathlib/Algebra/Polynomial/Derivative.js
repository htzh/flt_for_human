window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Derivative"] = {
  "module": "Mathlib.Algebra.Polynomial.Derivative",
  "cards": {
    "Polynomial.derivative": {
      "refs": [{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.sum","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Nat.cast","module":"Init.Data.Cast","kind":"def"}],
      "range": {"start":{"line":45,"column":0},"end":{"line":53,"column":94}},
      "name": "Polynomial.derivative",
      "module": "Mathlib.Algebra.Polynomial.Derivative",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → Polynomial R →ₗ[R] Polynomial R",
      "doc": "`derivative p` is the formal derivative of the polynomial `p` ",
      "short": "derivative",
      "signature_source": "def derivative : R[X] →ₗ[R] R[X] where\n  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)\n  map_add' p q := by\n    rw [sum_add_index] <;>\n      simp only [add_mul, forall_const, map_add, zero_mul, map_zero]\n  map_smul' a p := by\n    dsimp; rw [sum_smul_index] <;>\n      simp only [mul_sum, ← C_mul', mul_assoc, map_mul, forall_const, zero_mul, map_zero, sum]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Derivative.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
