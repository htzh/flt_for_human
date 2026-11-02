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
    "LinearMap.comp": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHomCompTriple","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":477,"column":0},"end":{"line":484,"column":76}},
      "name": "LinearMap.comp",
      "module": "Mathlib.Algebra.Module.LinearMap.Defs",
      "kind": "def",
      "elaborated_type": "{R₁ : Type u_2} →\n  {R₂ : Type u_3} →\n    {R₃ : Type u_4} →\n      {M₁ : Type u_9} →\n        {M₂ : Type u_10} →\n          {M₃ : Type u_11} →\n            [inst : Semiring R₁] →\n              [inst_1 : Semiring R₂] →\n                [inst_2 : Semiring R₃] →\n                  [inst_3 : AddCommMonoid M₁] →\n                    [inst_4 : AddCommMonoid M₂] →\n                      [inst_5 : AddCommMonoid M₃] →\n                        {module_M₁ : _root_.Module R₁ M₁} →\n                          {module_M₂ : _root_.Module R₂ M₂} →\n                            {module_M₃ : _root_.Module R₃ M₃} →\n                              {σ₁₂ : R₁ →+* R₂} →\n                                {σ₂₃ : R₂ →+* R₃} →\n                                  {σ₁₃ : R₁ →+* R₃} →\n                                    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] →\n                                      (M₂ →ₛₗ[σ₂₃] M₃) → (M₁ →ₛₗ[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₃] M₃",
      "doc": "Composition of two linear maps is a linear map ",
      "short": "comp",
      "signature_source": "@[instance_reducible]\ndef comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :\n    M₁ →ₛₗ[σ₁₃] M₃ where\n  toFun x := f (g x)\n  map_add' := by simp only [map_add, forall_const]\n  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`\n  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]",
      "body_source": "",
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
    },
    "LinearMap.restrictScalars": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.CompatibleSMul","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":413,"column":0},"end":{"line":421,"column":35}},
      "name": "LinearMap.restrictScalars",
      "module": "Mathlib.Algebra.Module.LinearMap.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  {S : Type u_5} →\n    {M : Type u_8} →\n      {M₂ : Type u_10} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring S] →\n            [inst_2 : AddCommMonoid M] →\n              [inst_3 : AddCommMonoid M₂] →\n                [inst_4 : _root_.Module R M] →\n                  [inst_5 : _root_.Module R M₂] →\n                    [inst_6 : _root_.Module S M] →\n                      [inst_7 : _root_.Module S M₂] → [LinearMap.CompatibleSMul M M₂ R S] → (M →ₗ[S] M₂) → M →ₗ[R] M₂",
      "doc": "If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures\nare defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear\nmap from `M` to `M₂` is `R`-linear.\n\nSee also `LinearMap.map_smul_of_tower`. ",
      "short": "restrictScalars",
      "signature_source": "@[coe] def restrictScalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ where\n  toFun := fₗ\n  map_add' := fₗ.map_add\n  map_smul' := fₗ.map_smul_of_tower",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
