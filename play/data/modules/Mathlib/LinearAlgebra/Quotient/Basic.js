window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Quotient.Basic"] = {
  "module": "Mathlib.LinearAlgebra.Quotient.Basic",
  "cards": {
    "Submodule.Quotient.restrictScalarsEquiv": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.Quotient.addCommMonoid","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.Quotient.module","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.Quotient.module'","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.hasQuotient","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.restrictScalars","module":"Mathlib.Algebra.Module.Submodule.RestrictScalars","kind":"def"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"body","name":"Quotient.congrRight","module":"Mathlib.Logic.Equiv.Defs","kind":"def"},{"where":"body","name":"Submodule.quotientRel","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"Quotient","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":57,"column":81}},
      "name": "Submodule.Quotient.restrictScalarsEquiv",
      "module": "Mathlib.LinearAlgebra.Quotient.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : Ring R] →\n      [inst_1 : AddCommGroup M] →\n        [inst_2 : _root_.Module R M] →\n          (S : Type u_3) →\n            [inst_3 : Ring S] →\n              [inst_4 : SMul S R] →\n                [inst_5 : _root_.Module S M] →\n                  [inst_6 : IsScalarTower S R M] → (P : Submodule R M) → (M ⧸ Submodule.restrictScalars S P) ≃ₗ[S] M ⧸ P",
      "doc": "The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,\nwhere `P : Submodule R M`.\n",
      "short": "restrictScalarsEquiv",
      "signature_source": "def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]\n    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=",
      "body_source": "{ Quotient.congrRight fun _ _ => Iff.rfl with\n    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl\n    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.liftQ": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.ker","module":"Mathlib.Algebra.Module.Submodule.Ker","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.Quotient.addCommMonoid","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.Quotient.module","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.hasQuotient","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"body","name":"AddSubgroup","module":"Mathlib.Algebra.Group.Subgroup.Defs","kind":"inductive"},{"where":"body","name":"QuotientAddGroup.Quotient.addGroup","module":"Mathlib.GroupTheory.QuotientGroup.Defs","kind":"def"},{"where":"body","name":"QuotientAddGroup.lift","module":"Mathlib.GroupTheory.QuotientGroup.Defs","kind":"def"}],
      "range": {"start":{"line":116,"column":0},"end":{"line":120,"column":58}},
      "name": "Submodule.liftQ",
      "module": "Mathlib.LinearAlgebra.Quotient.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : Ring R] →\n      [inst_1 : AddCommGroup M] →\n        [inst_2 : _root_.Module R M] →\n          (p : Submodule R M) →\n            {R₂ : Type u_3} →\n              {M₂ : Type u_4} →\n                [inst_3 : Ring R₂] →\n                  [inst_4 : AddCommGroup M₂] →\n                    [inst_5 : _root_.Module R₂ M₂] →\n                      {τ₁₂ : R →+* R₂} → (f : M →ₛₗ[τ₁₂] M₂) → p ≤ f.ker → M ⧸ p →ₛₗ[τ₁₂] M₂",
      "doc": "The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`\nvanishing on `p`, as a linear map. ",
      "short": "liftQ",
      "signature_source": "def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=",
      "body_source": "{ QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with\n    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
