window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Pi"] = {
  "module": "Mathlib.Algebra.Algebra.Pi",
  "cards": {
    "Function.algebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Pi.algebra","module":"Mathlib.Algebra.Algebra.Pi","kind":"def"}],
      "range": {"start":{"line":134,"column":0},"end":{"line":138,"column":16}},
      "name": "Function.algebra",
      "module": "Mathlib.Algebra.Algebra.Pi",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  (ι : Type u_2) → (A : Type u_3) → [inst : CommSemiring R] → [inst_1 : Semiring A] → [Algebra R A] → Algebra R (ι → A)",
      "doc": "A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate\ndefinitions elsewhere in the library without this. ",
      "short": "algebra",
      "signature_source": "instance Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]\n    [Algebra R A] : Algebra R (ι → A) :=",
      "body_source": "Pi.algebra _ _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Pi.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
