window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.Ker"] = {
  "module": "Mathlib.Algebra.Module.Submodule.Ker",
  "cards": {
    "LinearMap.ker": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Bot.bot","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"body","name":"Submodule.comap","module":"Mathlib.Algebra.Module.Submodule.Map","kind":"def"}],
      "range": {"start":{"line":58,"column":0},"end":{"line":61,"column":11}},
      "name": "LinearMap.ker",
      "module": "Mathlib.Algebra.Module.Submodule.Ker",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_2} →\n    {M : Type u_5} →\n      {M₂ : Type u_6} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                [inst_4 : _root_.Module R M] →\n                  [inst_5 : _root_.Module R₂ M₂] → {τ₁₂ : R →+* R₂} → (M →ₛₗ[τ₁₂] M₂) → Submodule R M",
      "doc": "The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the\nset of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. ",
      "short": "ker",
      "signature_source": "def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=",
      "body_source": "comap f ⊥",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Ker.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
