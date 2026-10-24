window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.LinearMap.Defs"] = {
  "module": "Mathlib.Algebra.Module.LinearMap.Defs",
  "cards": {
    "LinearMap": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":79,"column":0},"end":{"line":87,"column":36}},
      "name": "LinearMap",
      "module": "Mathlib.Algebra.Module.LinearMap.Defs",
      "kind": "inductive",
      "elaborated_type": "{R : Type u_14} →\n  {S : Type u_15} →\n    [inst : Semiring R] →\n      [inst_1 : Semiring S] →\n        (R →+* S) →\n          (M : Type u_16) →\n            (M₂ : Type u_17) →\n              [inst_2 : AddCommMonoid M] →\n                [inst_3 : AddCommMonoid M₂] → [_root_.Module R M] → [_root_.Module S M₂] → Type (max u_16 u_17)",
      "doc": "A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`\nis semilinear if it satisfies the two properties `f (x + y) = f x + f y` and\n`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation\n`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which\n`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear\nmaps is available with the predicate `IsLinearMap`, but it should be avoided most of the time. ",
      "short": "LinearMap",
      "signature_source": "structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)\n    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends\n    AddHom M M₂, MulActionHom σ M M₂",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "LinearMap.addCommMonoid": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.addMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"}],
      "range": {"start":{"line":845,"column":0},"end":{"line":847,"column":74}},
      "name": "LinearMap.addCommMonoid",
      "module": "Mathlib.Algebra.Module.LinearMap.Defs",
      "kind": "def",
      "elaborated_type": "{R₁ : Type u_2} →\n  {R₂ : Type u_3} →\n    {M : Type u_8} →\n      {M₂ : Type u_10} →\n        [inst : Semiring R₁] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                [inst_4 : _root_.Module R₁ M] →\n                  [inst_5 : _root_.Module R₂ M₂] → {σ₁₂ : R₁ →+* R₂} → AddCommMonoid (M →ₛₗ[σ₁₂] M₂)",
      "doc": "The type of linear maps is an additive monoid. ",
      "short": "addCommMonoid",
      "signature_source": "instance addCommMonoid : AddCommMonoid (M →ₛₗ[σ₁₂] M₂) :=",
      "body_source": "fast_instance%\n  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "LinearMap.module": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":949,"column":0},"end":{"line":951,"column":42}},
      "name": "LinearMap.module",
      "module": "Mathlib.Algebra.Module.LinearMap.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_3} →\n    {S : Type u_5} →\n      {M : Type u_8} →\n        {M₂ : Type u_10} →\n          [inst : Semiring R] →\n            [inst_1 : Semiring R₂] →\n              [inst_2 : AddCommMonoid M] →\n                [inst_3 : AddCommMonoid M₂] →\n                  [inst_4 : _root_.Module R M] →\n                    [inst_5 : _root_.Module R₂ M₂] →\n                      {σ₁₂ : R →+* R₂} →\n                        [inst_6 : Semiring S] →\n                          [inst_7 : _root_.Module S M₂] → [SMulCommClass R₂ S M₂] → _root_.Module S (M →ₛₗ[σ₁₂] M₂)",
      "doc": "",
      "short": "module",
      "signature_source": "instance module : Module S (M →ₛₗ[σ₁₂] M₂) where\n  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _\n  zero_smul _ := ext fun _ ↦ zero_smul _ _",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
