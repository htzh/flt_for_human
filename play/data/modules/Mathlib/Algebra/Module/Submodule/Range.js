window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.Range"] = {
  "module": "Mathlib.Algebra.Module.Submodule.Range",
  "cards": {
    "LinearMap.range": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHomSurjective","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Set.range","module":"Mathlib.Data.Set.Operations","kind":"def"},{"where":"body","name":"Submodule.copy","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.map","module":"Mathlib.Algebra.Module.Submodule.Map","kind":"def"},{"where":"body","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"}],
      "range": {"start":{"line":55,"column":0},"end":{"line":58,"column":50}},
      "name": "LinearMap.range",
      "module": "Mathlib.Algebra.Module.Submodule.Range",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_2} →\n    {M : Type u_5} →\n      {M₂ : Type u_6} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                [inst_4 : _root_.Module R M] →\n                  [inst_5 : _root_.Module R₂ M₂] →\n                    {τ₁₂ : R →+* R₂} → [RingHomSurjective τ₁₂] → (M →ₛₗ[τ₁₂] M₂) → Submodule R₂ M₂",
      "doc": "The range of a linear map `f : M → M₂` is a submodule of `M₂`.\nSee Note [range copy pattern]. ",
      "short": "range",
      "signature_source": "def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=",
      "body_source": "(map f ⊤).copy (Set.range f) Set.image_univ.symm",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
