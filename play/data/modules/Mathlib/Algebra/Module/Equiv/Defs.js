window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Equiv.Defs"] = {
  "module": "Mathlib.Algebra.Module.Equiv.Defs",
  "cards": {
    "LinearEquiv": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHomInvPair","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":48,"column":0},"end":{"line":51,"column":99}},
      "name": "LinearEquiv",
      "module": "Mathlib.Algebra.Module.Equiv.Defs",
      "kind": "inductive",
      "elaborated_type": "{R : Type u_14} →\n  {S : Type u_15} →\n    [inst : Semiring R] →\n      [inst_1 : Semiring S] →\n        (σ : R →+* S) →\n          {σ' : S →+* R} →\n            [RingHomInvPair σ σ'] →\n              [RingHomInvPair σ' σ] →\n                (M : Type u_16) →\n                  (M₂ : Type u_17) →\n                    [inst_4 : AddCommMonoid M] →\n                      [inst_5 : AddCommMonoid M₂] → [_root_.Module R M] → [_root_.Module S M₂] → Type (max u_16 u_17)",
      "doc": "A linear equivalence is an invertible linear map. ",
      "short": "LinearEquiv",
      "signature_source": "structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)\n  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)\n  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "LinearEquiv.symm": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHomInvPair","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"body","name":"Equiv.left_inv","module":"Mathlib.Logic.Equiv.Defs","kind":"theorem"},{"where":"body","name":"Equiv.right_inv","module":"Mathlib.Logic.Equiv.Defs","kind":"theorem"},{"where":"body","name":"Equiv.symm","module":"Mathlib.Logic.Equiv.Defs","kind":"def"},{"where":"body","name":"LinearEquiv.left_inv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"theorem"},{"where":"body","name":"LinearEquiv.right_inv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"theorem"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.inverse","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"}],
      "range": {"start":{"line":249,"column":0},"end":{"line":256,"column":41}},
      "name": "LinearEquiv.symm",
      "module": "Mathlib.Algebra.Module.Equiv.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {S : Type u_6} →\n    {M : Type u_7} →\n      {M₂ : Type u_9} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring S] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                {module_M : _root_.Module R M} →\n                  {module_S_M₂ : _root_.Module S M₂} →\n                    {σ : R →+* S} →\n                      {σ' : S →+* R} →\n                        {re₁ : RingHomInvPair σ σ'} → {re₂ : RingHomInvPair σ' σ} → (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M",
      "doc": "Linear equivalences are symmetric. ",
      "short": "symm",
      "signature_source": "@[symm, implicit_reducible]\ndef symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=",
      "body_source": "{ e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,\n    e.toEquiv.symm with\n    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv\n    invFun := e.toEquiv.symm.invFun\n    map_smul' r x := by rw [map_smulₛₗ] }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
