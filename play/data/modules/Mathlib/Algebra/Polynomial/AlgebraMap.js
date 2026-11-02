window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.AlgebraMap"] = {
  "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
  "cards": {
    "Polynomial.aeval": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.aevalEquiv","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"}],
      "range": {"start":{"line":253,"column":0},"end":{"line":258,"column":18}},
      "name": "Polynomial.aeval",
      "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {A : Type z} → [inst : CommSemiring R] → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → A → Polynomial R →ₐ[R] A",
      "doc": "Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is\nthe unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.\n\nThis is a stronger variant of the linear map `Polynomial.leval`. ",
      "short": "aeval",
      "signature_source": "def aeval : R[X] →ₐ[R] A :=",
      "body_source": "aevalEquiv R A x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.aevalEquiv": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"body","name":"Algebra.commutes","module":"Mathlib.Algebra.Algebra.Defs","kind":"theorem"},{"where":"body","name":"Algebra.ofId","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.eval₂AlgHom","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"}],
      "range": {"start":{"line":244,"column":0},"end":{"line":251,"column":65}},
      "name": "Polynomial.aevalEquiv",
      "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
      "kind": "def",
      "elaborated_type": "(R : Type u) →\n  (A : Type z) → [inst : CommSemiring R] → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → A ≃ (Polynomial R →ₐ[R] A)",
      "doc": "Given a valuation `x` of the variable in an `R`-algebra `A`, the bijection induced by the unique\n`R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. ",
      "short": "aevalEquiv",
      "signature_source": "@[simps! symm_apply]\ndef aevalEquiv : A ≃ (R[X] →ₐ[R] A) where\n  toFun x := eval₂AlgHom (Algebra.ofId _ _) x (Algebra.commutes · _)\n  invFun f := f X\n  left_inv := eval₂_X _\n  right_inv _ := algHom_ext' (Subsingleton.elim ..) <| eval₂_X ..",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.aeval_def": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.aeval","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":273,"column":0},"end":{"line":274,"column":5}},
      "name": "Polynomial.aeval_def",
      "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {A : Type z} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (x : A)\n  (p : Polynomial R), (Polynomial.aeval x) p = Polynomial.eval₂ (algebraMap R A) x p",
      "doc": "",
      "short": "aeval_def",
      "signature_source": "theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=",
      "body_source": "rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.algebraOfAlgebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.smulZeroClass","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":54,"column":0},"end":{"line":66,"column":39}},
      "name": "Polynomial.algebraOfAlgebra",
      "module": "Mathlib.Algebra.Polynomial.AlgebraMap",
      "kind": "def",
      "elaborated_type": "{R : Type u} → {A : Type z} → [inst : CommSemiring R] → [inst_1 : Semiring A] → [Algebra R A] → Algebra R (Polynomial A)",
      "doc": "Note that this instance also provides `Algebra R R[X]`. ",
      "short": "algebraOfAlgebra",
      "signature_source": "instance algebraOfAlgebra : Algebra R A[X] where\n  smul_def' r p :=\n    toFinsupp_injective <| by\n      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]\n      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]\n      exact Algebra.smul_def' _ _\n  commutes' r p :=\n    toFinsupp_injective <| by\n      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]\n      simp_rw [toFinsupp_mul, toFinsupp_C]\n      convert! Algebra.commutes' r p.toFinsupp\n  algebraMap := C.comp (algebraMap R A)",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
