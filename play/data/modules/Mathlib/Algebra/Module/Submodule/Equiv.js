window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.Equiv"] = {
  "module": "Mathlib.Algebra.Module.Submodule.Equiv",
  "cards": {
    "LinearEquiv.ofBijective": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Function.Bijective","module":"Mathlib.Logic.Function.Defs","kind":"def"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHomInvPair","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"LinearEquiv.ofInjective","module":"Mathlib.Algebra.Module.Submodule.Equiv","kind":"def"},{"where":"body","name":"LinearEquiv.ofTop","module":"Mathlib.Algebra.Module.Submodule.Equiv","kind":"def"},{"where":"body","name":"LinearEquiv.trans","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"def"},{"where":"body","name":"LinearMap.range","module":"Mathlib.Algebra.Module.Submodule.Range","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"RingHomCompTriple.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"body","name":"RingHomCompTriple.right_ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"body","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"body","name":"RingHomSurjective.invPair","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"}],
      "range": {"start":{"line":182,"column":0},"end":{"line":186,"column":42}},
      "name": "LinearEquiv.ofBijective",
      "module": "Mathlib.Algebra.Module.Submodule.Equiv",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_2} →\n    {M : Type u_4} →\n      {M₂ : Type u_6} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                {module_M : _root_.Module R M} →\n                  {module_M₂ : _root_.Module R₂ M₂} →\n                    {σ₁₂ : R →+* R₂} →\n                      {σ₂₁ : R₂ →+* R} →\n                        (f : M →ₛₗ[σ₁₂] M₂) →\n                          [inst_4 : RingHomInvPair σ₁₂ σ₂₁] →\n                            [inst_5 : RingHomInvPair σ₂₁ σ₁₂] → Function.Bijective ⇑f → M ≃ₛₗ[σ₁₂] M₂",
      "doc": "A bijective linear map is a linear equivalence. ",
      "short": "ofBijective",
      "signature_source": "noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :\n    M ≃ₛₗ[σ₁₂] M₂ :=",
      "body_source": "(ofInjective f hf.injective).trans <| ofTop _ <|\n    LinearMap.range_eq_top.2 hf.surjective",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
