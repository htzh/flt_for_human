window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Tower"] = {
  "module": "Mathlib.Algebra.Algebra.Tower",
  "cards": {
    "AlgHom.restrictScalars": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
      "range": {"start":{"line":181,"column":0},"end":{"line":186,"column":43}},
      "name": "AlgHom.restrictScalars",
      "module": "Mathlib.Algebra.Algebra.Tower",
      "kind": "def",
      "elaborated_type": "(R : Type u) →\n  {S : Type v} →\n    {A : Type w} →\n      {B : Type u₁} →\n        [inst : CommSemiring R] →\n          [inst_1 : CommSemiring S] →\n            [inst_2 : Semiring A] →\n              [inst_3 : Semiring B] →\n                [inst_4 : Algebra R S] →\n                  [inst_5 : Algebra S A] →\n                    [inst_6 : Algebra S B] →\n                      [inst_7 : Algebra R A] →\n                        [inst_8 : Algebra R B] → [IsScalarTower R S A] → [IsScalarTower R S B] → (A →ₐ[S] B) → A →ₐ[R] B",
      "doc": "R ⟶ S induces S-Alg ⥤ R-Alg ",
      "short": "restrictScalars",
      "signature_source": "def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=",
      "body_source": "{ (f : A →+* B) with\n    commutes' := fun r => by\n      rw [algebraMap_apply R S A, algebraMap_apply R S B]\n      exact f.commutes (algebraMap R S r) }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Tower.lean",
      "has_source": true,
      "has_refs": true
    },
    "Algebra.lsmul": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower.to_smulCommClass'","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.End","module":"Mathlib.Algebra.Module.LinearMap.End","kind":"abbrev"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":42,"column":0},"end":{"line":74,"column":53}},
      "name": "Algebra.lsmul",
      "module": "Mathlib.Algebra.Algebra.Tower",
      "kind": "def",
      "elaborated_type": "(R : Type u) →\n  {A : Type w} →\n    (B : Type u₁) →\n      (M : Type v₁) →\n        [inst : CommSemiring R] →\n          [inst_1 : Semiring A] →\n            [inst_2 : Semiring B] →\n              [inst_3 : Algebra R A] →\n                [inst_4 : Algebra R B] →\n                  [inst_5 : AddCommMonoid M] →\n                    [inst_6 : _root_.Module R M] →\n                      [inst_7 : _root_.Module A M] →\n                        [inst_8 : _root_.Module B M] →\n                          [IsScalarTower R A M] →\n                            [inst_10 : IsScalarTower R B M] → [SMulCommClass A B M] → A →ₐ[R] Module.End B M",
      "doc": "The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`\non the `B`-module `M`.\n\nThis is a stronger version of `DistribSMul.toLinearMap`, and could also have been\ncalled `Algebra.toModuleEnd`.\n\nThe typeclasses correspond to the situation where the types act on each other as\n```\nR ----→ B\n| ⟍     |\n|   ⟍   |\n↓     ↘ ↓\nA ----→ M\n```\nwhere the diagram commutes, the action by `R` commutes with everything, and the action by `A` and\n`B` on `M` commute.\n\nTypically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Module.End R M`.\nHowever this can be used to get the fact that left-multiplication by `A` is right `A`-linear, and\nvice versa, as\n```lean\nexample : A →ₐ[R] Module.End Aᵐᵒᵖ A := Algebra.lsmul R Aᵐᵒᵖ A\nexample : Aᵐᵒᵖ →ₐ[R] Module.End A A := Algebra.lsmul R A A\n```\nrespectively; though `LinearMap.mulLeft` and `LinearMap.mulRight` can also be used here.\n",
      "short": "lsmul",
      "signature_source": "def lsmul : A →ₐ[R] Module.End B M where\n  toFun := DistribSMul.toLinearMap B M\n  map_one' := LinearMap.ext fun _ => one_smul A _\n  map_mul' a b := LinearMap.ext <| smul_assoc a b\n  map_zero' := LinearMap.ext fun _ => zero_smul A _\n  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _\n  commutes' r := LinearMap.ext <| algebraMap_smul A r",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Tower.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsScalarTower.algebraMap_smul": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"MulAction","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":93,"column":0},"end":{"line":95,"column":59}},
      "name": "IsScalarTower.algebraMap_smul",
      "module": "Mathlib.Algebra.Algebra.Tower",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} (A : Type w) {M : Type v₁} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]\n  [inst_3 : MulAction A M] [inst_4 : SMul R M] [IsScalarTower R A M] (r : R) (x : M), (algebraMap R A) r • x = r • x",
      "doc": "",
      "short": "algebraMap_smul",
      "signature_source": "theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :\n    algebraMap R A r • x = r • x :=",
      "body_source": "by\n  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Tower.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
