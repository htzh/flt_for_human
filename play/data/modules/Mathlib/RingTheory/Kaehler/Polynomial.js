window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Kaehler.Polynomial"] = {
  "module": "Mathlib.RingTheory.Kaehler.Polynomial",
  "cards": {
    "KaehlerDifferential.mvPolynomialBasis": {
      "refs": [{"where":"type","name":"AddMonoidAlgebra.algebra","module":"Mathlib.Algebra.MonoidAlgebra.Basic","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"MvPolynomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"KaehlerDifferential.mvPolynomialEquiv","module":"Mathlib.RingTheory.Kaehler.Polynomial","kind":"def"}],
      "range": {"start":{"line":58,"column":0},"end":{"line":62,"column":25}},
      "name": "KaehlerDifferential.mvPolynomialBasis",
      "module": "Mathlib.RingTheory.Kaehler.Polynomial",
      "kind": "def",
      "elaborated_type": "(R : Type u) → [inst : CommRing R] → (σ : Type u_1) → Module.Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]",
      "doc": "`{ dx | x ∈ σ }` forms a basis of the relative differential module\nof a polynomial algebra `R[σ]`. ",
      "short": "mvPolynomialBasis",
      "signature_source": "def KaehlerDifferential.mvPolynomialBasis (σ) :\n    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=",
      "body_source": "⟨mvPolynomialEquiv R σ⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.polynomialEquiv": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"body","name":"Algebra.lsmul","module":"Mathlib.Algebra.Algebra.Tower","kind":"def"},{"where":"body","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"body","name":"Derivation.liftKaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"LinearMap.flip","module":"Mathlib.LinearAlgebra.BilinearMap","kind":"def"},{"where":"body","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"Module.End","module":"Mathlib.Algebra.Module.LinearMap.End","kind":"abbrev"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.derivative'","module":"Mathlib.Algebra.Polynomial.Derivation","kind":"def"},{"where":"body","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"}],
      "range": {"start":{"line":111,"column":0},"end":{"line":125,"column":24}},
      "name": "KaehlerDifferential.polynomialEquiv",
      "module": "Mathlib.RingTheory.Kaehler.Polynomial",
      "kind": "def",
      "elaborated_type": "(R : Type u) → [inst : CommRing R] → Ω[Polynomial R⁄R] ≃ₗ[Polynomial R] Polynomial R",
      "doc": "The relative differential module of the univariate polynomial algebra `R[X]` is isomorphic to\n`R[X]` as an `R[X]`-module. ",
      "short": "polynomialEquiv",
      "signature_source": "def KaehlerDifferential.polynomialEquiv : Ω[R[X]⁄R] ≃ₗ[R[X]] R[X] where\n  __ := derivative'.liftKaehlerDifferential\n  invFun := (Algebra.lsmul R R _).toLinearMap.flip (D R R[X] X)\n  left_inv := by\n    intro x\n    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x\n    induction x using Finsupp.induction_linear with\n    | zero => simp\n    | add x y hx hy =>\n      simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.flip_apply,\n        AlgHom.toLinearMap_apply, lsmul_coe] at *; simp only [*]\n    | single x y => simp [polynomial_D_apply _ x]\n  right_inv x := by simp",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.polynomialEquiv_D": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.polynomialEquiv","module":"Mathlib.RingTheory.Kaehler.Polynomial","kind":"def"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.derivative","module":"Mathlib.Algebra.Polynomial.Derivative","kind":"def"},{"where":"type","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"}],
      "range": {"start":{"line":131,"column":0},"end":{"line":134,"column":51}},
      "name": "KaehlerDifferential.polynomialEquiv_D",
      "module": "Mathlib.RingTheory.Kaehler.Polynomial",
      "kind": "theorem",
      "elaborated_type": "∀ (R : Type u) [inst : CommRing R] (P : Polynomial R),\n  (KaehlerDifferential.polynomialEquiv R) ((KaehlerDifferential.D R (Polynomial R)) P) = Polynomial.derivative P",
      "doc": "",
      "short": "polynomialEquiv_D",
      "signature_source": "@[simp]\nlemma KaehlerDifferential.polynomialEquiv_D (P) :\n    polynomialEquiv R (D R R[X] P) = derivative P :=",
      "body_source": "Derivation.congr_fun (polynomialEquiv_comp_D R) P",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.polynomialEquiv_symm": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.polynomialEquiv","module":"Mathlib.RingTheory.Kaehler.Polynomial","kind":"def"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"LinearEquiv.symm","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"def"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":136,"column":0},"end":{"line":138,"column":54}},
      "name": "KaehlerDifferential.polynomialEquiv_symm",
      "module": "Mathlib.RingTheory.Kaehler.Polynomial",
      "kind": "theorem",
      "elaborated_type": "∀ (R : Type u) [inst : CommRing R] (P : Polynomial R),\n  (KaehlerDifferential.polynomialEquiv R).symm P = P • (KaehlerDifferential.D R (Polynomial R)) Polynomial.X",
      "doc": "",
      "short": "polynomialEquiv_symm",
      "signature_source": "@[simp]\nlemma KaehlerDifferential.polynomialEquiv_symm (P) :\n    (polynomialEquiv R).symm P = P • D R R[X] X :=",
      "body_source": "rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.polynomial_D_apply": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.derivative","module":"Mathlib.Algebra.Polynomial.Derivative","kind":"def"},{"where":"type","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":107,"column":0},"end":{"line":109,"column":91}},
      "name": "KaehlerDifferential.polynomial_D_apply",
      "module": "Mathlib.RingTheory.Kaehler.Polynomial",
      "kind": "theorem",
      "elaborated_type": "∀ (R : Type u) [inst : CommRing R] (P : Polynomial R),\n  (KaehlerDifferential.D R (Polynomial R)) P =\n    Polynomial.derivative P • (KaehlerDifferential.D R (Polynomial R)) Polynomial.X",
      "doc": "",
      "short": "polynomial_D_apply",
      "signature_source": "lemma KaehlerDifferential.polynomial_D_apply (P : R[X]) :\n    D R R[X] P = derivative P • D R R[X] X :=",
      "body_source": "by\n  rw [← aeval_X_left_apply P, (D R R[X]).map_aeval, aeval_X_left_apply, aeval_X_left_apply]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
