window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.BilinearMap"] = {
  "module": "Mathlib.LinearAlgebra.BilinearMap",
  "cards": {
    "LinearMap.flip": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"SMulCommClass","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"SMulCommClass.symm","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.mk₂'ₛₗ","module":"Mathlib.LinearAlgebra.BilinearMap","kind":"def"}],
      "range": {"start":{"line":112,"column":0},"end":{"line":120,"column":58}},
      "name": "LinearMap.flip",
      "module": "Mathlib.LinearAlgebra.BilinearMap",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {R₂ : Type u_2} →\n    {S : Type u_3} →\n      {S₂ : Type u_4} →\n        [inst : Semiring R] →\n          [inst_1 : Semiring R₂] →\n            [inst_2 : Semiring S] →\n              [inst_3 : Semiring S₂] →\n                {M : Type u_5} →\n                  {N : Type u_7} →\n                    {P : Type u_9} →\n                      [inst_4 : AddCommMonoid M] →\n                        [inst_5 : AddCommMonoid N] →\n                          [inst_6 : AddCommMonoid P] →\n                            [inst_7 : _root_.Module R M] →\n                              [inst_8 : _root_.Module S N] →\n                                [inst_9 : _root_.Module R₂ P] →\n                                  [inst_10 : _root_.Module S₂ P] →\n                                    [inst_11 : SMulCommClass S₂ R₂ P] →\n                                      {ρ₁₂ : R →+* R₂} →\n                                        {σ₁₂ : S →+* S₂} → (M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) → N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P",
      "doc": "Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to\n`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. ",
      "short": "flip",
      "signature_source": "def flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P :=",
      "body_source": "mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun _ _ m => (f m).map_add _ _)\n    (fun _ _ m => (f m).map_smulₛₗ _ _)\n    (fun n m₁ m₂ => by simp only [map_add, add_apply])\n    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`.\n    -- It looks like we now run out of assignable metavariables.\n    (fun c n m => by simp only [map_smulₛₗ _, smul_apply])",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean",
      "has_source": true,
      "has_refs": true
    },
    "LinearMap.lsmul": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"body","name":"LinearMap.mk₂","module":"Mathlib.LinearAlgebra.BilinearMap","kind":"def"},{"where":"body","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":506,"column":0},"end":{"line":509,"column":35}},
      "name": "LinearMap.lsmul",
      "module": "Mathlib.LinearAlgebra.BilinearMap",
      "kind": "def",
      "elaborated_type": "(R : Type u_2) →\n  [inst : CommSemiring R] →\n    (M : Type u_5) → [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → R →ₗ[R] M →ₗ[R] M",
      "doc": "Scalar multiplication as a bilinear map `R → M → M`. ",
      "short": "lsmul",
      "signature_source": "def lsmul : R →ₗ[R] M →ₗ[R] M :=",
      "body_source": "mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by\n    simp only [smul_smul, mul_comm]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean",
      "has_source": true,
      "has_refs": true
    },
    "LinearMap.mk₂": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"LinearMap.mk₂'","module":"Mathlib.LinearAlgebra.BilinearMap","kind":"def"}],
      "range": {"start":{"line":315,"column":0},"end":{"line":322,"column":24}},
      "name": "LinearMap.mk₂",
      "module": "Mathlib.LinearAlgebra.BilinearMap",
      "kind": "def",
      "elaborated_type": "(R : Type u_2) →\n  [inst : CommSemiring R] →\n    {M : Type u_5} →\n      {Nₗ : Type u_8} →\n        {Pₗ : Type u_9} →\n          [inst_1 : AddCommMonoid M] →\n            [inst_2 : AddCommMonoid Nₗ] →\n              [inst_3 : AddCommMonoid Pₗ] →\n                [inst_4 : _root_.Module R M] →\n                  [inst_5 : _root_.Module R Nₗ] →\n                    [inst_6 : _root_.Module R Pₗ] →\n                      (f : M → Nₗ → Pₗ) →\n                        (∀ (m₁ m₂ : M) (n : Nₗ), f (m₁ + m₂) n = f m₁ n + f m₂ n) →\n                          (∀ (c : R) (m : M) (n : Nₗ), f (c • m) n = c • f m n) →\n                            (∀ (m : M) (n₁ n₂ : Nₗ), f m (n₁ + n₂) = f m n₁ + f m n₂) →\n                              (∀ (c : R) (m : M) (n : Nₗ), f m (c • n) = c • f m n) → M →ₗ[R] Nₗ →ₗ[R] Pₗ",
      "doc": "Create a bilinear map from a function that is linear in each component.\n\nThis is a shorthand for `mk₂'` for the common case when `R = S`. ",
      "short": "mk₂",
      "signature_source": "def mk₂ (f : M → Nₗ → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)\n    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n)\n    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)\n    (H4 : ∀ (c : R) (m n), f m (c • n) = c • f m n) : M →ₗ[R] Nₗ →ₗ[R] Pₗ :=",
      "body_source": "mk₂' R R f H1 H2 H3 H4",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
