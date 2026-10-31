window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.Map"] = {
  "module": "Mathlib.Algebra.Module.Submodule.Map",
  "cards": {
    "Submodule.comap": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"AddSubmonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"body","name":"AddSubmonoid.comap","module":"Mathlib.Algebra.Group.Submonoid.Operations","kind":"def"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Set.preimage","module":"Mathlib.Data.Set.Operations","kind":"def"}],
      "range": {"start":{"line":170,"column":0},"end":{"line":176,"column":76}},
      "name": "Submodule.comap",
      "module": "Mathlib.Algebra.Module.Submodule.Map",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_2} →\n    {M : Type u_4} →\n      {M₂ : Type u_5} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                [inst_4 : _root_.Module R M] →\n                  [inst_5 : _root_.Module R₂ M₂] → {σ₁₂ : R →+* R₂} → (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂ → Submodule R M",
      "doc": "The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` ",
      "short": "comap",
      "signature_source": "@[implicit_reducible]\ndef comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=",
      "body_source": "{ p.toAddSubmonoid.comap f with\n    carrier := f ⁻¹' p\n    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`\n    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Map.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.map": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHomSurjective","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"AddSubmonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"body","name":"AddSubmonoid.map","module":"Mathlib.Algebra.Group.Submonoid.Operations","kind":"def"},{"where":"body","name":"Set.image","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":52,"column":0},"end":{"line":59,"column":52}},
      "name": "Submodule.map",
      "module": "Mathlib.Algebra.Module.Submodule.Map",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_2} →\n    {M : Type u_4} →\n      {M₂ : Type u_5} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                [inst_4 : _root_.Module R M] →\n                  [inst_5 : _root_.Module R₂ M₂] →\n                    {σ₁₂ : R →+* R₂} → [RingHomSurjective σ₁₂] → (M →ₛₗ[σ₁₂] M₂) → Submodule R M → Submodule R₂ M₂",
      "doc": "The pushforward of a submodule `p ⊆ M` by `f : M → M₂` ",
      "short": "map",
      "signature_source": "def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=",
      "body_source": "{ p.toAddSubmonoid.map f with\n    carrier := f '' p\n    smul_mem' := by\n      rintro c x ⟨y, hy, rfl⟩\n      obtain ⟨a, rfl⟩ := σ₁₂.surjective c\n      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Map.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
