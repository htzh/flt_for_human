window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.LinearIndependent.Defs"] = {
  "module": "Mathlib.LinearAlgebra.LinearIndependent.Defs",
  "cards": {
    "LinearIndependent": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"Finsupp.linearCombination","module":"Mathlib.LinearAlgebra.Finsupp.LinearCombination","kind":"def"},{"where":"body","name":"Finsupp.module","module":"Mathlib.Data.Finsupp.SMul","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"Function.Injective","module":"Init.Data.Function","kind":"def"}],
      "range": {"start":{"line":97,"column":0},"end":{"line":99,"column":43}},
      "name": "LinearIndependent",
      "module": "Mathlib.LinearAlgebra.LinearIndependent.Defs",
      "kind": "def",
      "elaborated_type": "{ι : Type u'} →\n  (R : Type u_2) →\n    {M : Type u_4} → (ι → M) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Prop",
      "doc": "`LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. ",
      "short": "LinearIndependent",
      "signature_source": "def LinearIndependent : Prop :=",
      "body_source": "Injective (Finsupp.linearCombination R v)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
