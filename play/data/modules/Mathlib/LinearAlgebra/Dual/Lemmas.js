window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Dual.Lemmas"] = {
  "module": "Mathlib.LinearAlgebra.Dual.Lemmas",
  "cards": {
    "Submodule.dualQuotEquivDualAnnihilator": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"IsScalarTower.left","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Dual","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"abbrev"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.Quotient.addCommMonoid","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.Quotient.module","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Submodule.dualAnnihilator","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"def"},{"where":"type","name":"Submodule.hasQuotient","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"LinearEquiv.ofLinearMap","module":"Mathlib.Algebra.Module.Equiv.Basic","kind":"def"},{"where":"body","name":"LinearMap.codRestrict","module":"Mathlib.Algebra.Module.Submodule.LinearMap","kind":"def"},{"where":"body","name":"LinearMap.dualMap","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"def"},{"where":"body","name":"Submodule.dualCopairing","module":"Mathlib.LinearAlgebra.Dual.Lemmas","kind":"def"},{"where":"body","name":"Submodule.mkQ","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"}],
      "range": {"start":{"line":655,"column":0},"end":{"line":665,"column":47}},
      "name": "Submodule.dualQuotEquivDualAnnihilator",
      "module": "Mathlib.LinearAlgebra.Dual.Lemmas",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : CommRing R] →\n      [inst_1 : AddCommGroup M] →\n        [inst_2 : _root_.Module R M] → (W : Submodule R M) → Module.Dual R (M ⧸ W) ≃ₗ[R] ↥W.dualAnnihilator",
      "doc": "Equivalence $(M/W)^* \\cong \\operatorname{ann}(W)$. That is, there is a one-to-one\ncorrespondence between the dual of `M ⧸ W` and those elements of the dual of `M` that\nvanish on `W`.\n\nThe inverse of this is `Submodule.dualCopairing`. ",
      "short": "dualQuotEquivDualAnnihilator",
      "signature_source": "def dualQuotEquivDualAnnihilator (W : Submodule R M) :\n    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=",
      "body_source": "LinearEquiv.ofLinearMap\n    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ ↦\n      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)\n    W.dualCopairing (by ext; rfl) (by ext; rfl)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean",
      "has_source": true,
      "has_refs": true
    },
    "Subspace.dual_finrank_eq": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Dual","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"abbrev"},{"where":"type","name":"Module.finrank","module":"Mathlib.LinearAlgebra.Dimension.Finrank","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":549,"column":0},"end":{"line":555,"column":81}},
      "name": "Subspace.dual_finrank_eq",
      "module": "Mathlib.LinearAlgebra.Dual.Lemmas",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],\n  Module.finrank K (Module.Dual K V) = Module.finrank K V",
      "doc": "",
      "short": "dual_finrank_eq",
      "signature_source": "@[simp]\ntheorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V :=",
      "body_source": "by\n  by_cases h : FiniteDimensional K V\n  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm\n  rw [finrank_eq_zero_of_basis_imp_false, finrank_eq_zero_of_basis_imp_false]\n  · exact fun _ b ↦ h (Module.Finite.of_basis b)\n  · exact fun _ b ↦ h ((Module.finite_dual_iff K).mp <| Module.Finite.of_basis b)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
