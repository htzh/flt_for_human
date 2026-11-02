window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Dimension.Finite"] = {
  "module": "Mathlib.LinearAlgebra.Dimension.Finite",
  "cards": {
    "LinearIndependent.finrank_eq_zero_of_infinite": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Infinite","module":"Mathlib.Basic.Finite.Defs","kind":"inductive"},{"where":"type","name":"LinearIndependent","module":"Mathlib.LinearAlgebra.LinearIndependent.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.finrank","module":"Mathlib.LinearAlgebra.Dimension.Finrank","kind":"def"},{"where":"type","name":"Nontrivial","module":"Mathlib.Basic.Nontrivial.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":356,"column":0},"end":{"line":357,"column":97}},
      "name": "LinearIndependent.finrank_eq_zero_of_infinite",
      "module": "Mathlib.LinearAlgebra.Dimension.Finite",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Nontrivial R]\n  {ι : Type u_1} [Infinite ι] {v : ι → M}, LinearIndependent R v → Module.finrank R M = 0",
      "doc": "",
      "short": "finrank_eq_zero_of_infinite",
      "signature_source": "lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι → M}\n    (hv : LinearIndependent R v) : finrank R M = 0 :=",
      "body_source": "toNat_eq_zero.mpr <| .inr hv.aleph0_le_rank",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
