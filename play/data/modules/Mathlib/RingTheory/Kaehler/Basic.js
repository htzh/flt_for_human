window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Kaehler.Basic"] = {
  "module": "Mathlib.RingTheory.Kaehler.Basic",
  "cards": {
    "KaehlerDifferential": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Ideal.Cotangent","module":"Mathlib.RingTheory.Ideal.Cotangent","kind":"def"},{"where":"body","name":"KaehlerDifferential.ideal","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"abbrev"},{"where":"body","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"}],
      "range": {"start":{"line":142,"column":0},"end":{"line":152,"column":18}},
      "name": "KaehlerDifferential",
      "module": "Mathlib.RingTheory.Kaehler.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u) → (S : Type v) → [inst : CommRing R] → [inst_1 : CommRing S] → [Algebra R S] → Type v",
      "doc": "The module of Kähler differentials (Kahler differentials, Kaehler differentials).\nThis is implemented as `I / I ^ 2` with `I` the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.\nTo view elements as a linear combination of the form `s • D s'`, use\n`KaehlerDifferential.tensorProductTo_surjective` and `Derivation.tensorProductTo_tmul`.\n\nWe also provide the notation `Ω[S⁄R]` for `KaehlerDifferential R S`.\nNote that the slash is `\\textfractionsolidus`.\n",
      "short": "KaehlerDifferential",
      "signature_source": "def KaehlerDifferential : Type v :=",
      "body_source": "(KaehlerDifferential.ideal R S).Cotangent\nderiving Inhabited",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.D": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"body","name":"KaehlerDifferential.DLinearMap","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":194,"column":0},"end":{"line":213,"column":15}},
      "name": "KaehlerDifferential.D",
      "module": "Mathlib.RingTheory.Kaehler.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u) →\n  (S : Type v) → [inst : CommRing R] → [inst_1 : CommRing S] → [inst_2 : Algebra R S] → Derivation R S Ω[S⁄R]",
      "doc": "The universal derivation into `Ω[S⁄R]`. ",
      "short": "D",
      "signature_source": "def KaehlerDifferential.D : Derivation R S Ω[S⁄R] :=",
      "body_source": "{ toLinearMap := KaehlerDifferential.DLinearMap R S\n    map_one_eq_zero' := by\n      dsimp [KaehlerDifferential.DLinearMap_apply, Ideal.toCotangent_apply]\n      congr\n      rw [sub_self]\n    leibniz' := fun a b => by\n      have : LinearMap.CompatibleSMul { x // x ∈ ideal R S } Ω[S⁄R] S (S ⊗[R] S) := inferInstance\n      dsimp [KaehlerDifferential.DLinearMap_apply]\n      rw [← LinearMap.map_smul_of_tower (ideal R S).toCotangent,\n        ← LinearMap.map_smul_of_tower (ideal R S).toCotangent,\n        ← map_add (ideal R S).toCotangent, Ideal.toCotangent_eq, pow_two]\n      convert!\n        Submodule.mul_mem_mul (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a :)\n          (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b :) using 1\n      simp only [Submodule.coe_add,\n        TensorProduct.tmul_mul_tmul, mul_sub, sub_mul, mul_comm b, Submodule.coe_smul_of_tower,\n        smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]\n      ring_nf }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.DLinearMap": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"body","name":"Algebra.TensorProduct.includeLeft","module":"Mathlib.RingTheory.TensorProduct.Basic","kind":"def"},{"where":"body","name":"Algebra.TensorProduct.includeRight","module":"Mathlib.RingTheory.TensorProduct.Basic","kind":"def"},{"where":"body","name":"Algebra.TensorProduct.leftAlgebra","module":"Mathlib.RingTheory.TensorProduct.Basic","kind":"def"},{"where":"body","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"body","name":"KaehlerDifferential.fromIdeal","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"KaehlerDifferential.ideal","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"abbrev"},{"where":"body","name":"KaehlerDifferential.one_smul_sub_smul_one_mem_ideal","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"theorem"},{"where":"body","name":"LinearMap.codRestrict","module":"Mathlib.Algebra.Module.Submodule.LinearMap","kind":"def"},{"where":"body","name":"LinearMap.comp","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"LinearMap.restrictScalars","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.module'","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.restrictScalars","module":"Mathlib.Algebra.Module.Submodule.RestrictScalars","kind":"def"},{"where":"body","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.addCommGroup","module":"Mathlib.LinearAlgebra.TensorProduct.Basic","kind":"def"},{"where":"body","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"}],
      "range": {"start":{"line":178,"column":0},"end":{"line":185,"column":16}},
      "name": "KaehlerDifferential.DLinearMap",
      "module": "Mathlib.RingTheory.Kaehler.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u) → (S : Type v) → [inst : CommRing R] → [inst_1 : CommRing S] → [inst_2 : Algebra R S] → S →ₗ[R] Ω[S⁄R]",
      "doc": "(Implementation) The underlying linear map of the derivation into `Ω[S⁄R]`. ",
      "short": "DLinearMap",
      "signature_source": "def KaehlerDifferential.DLinearMap : S →ₗ[R] Ω[S⁄R] :=",
      "body_source": "((KaehlerDifferential.fromIdeal R S).restrictScalars R).comp\n    ((TensorProduct.includeRight.toLinearMap - TensorProduct.includeLeft.toLinearMap :\n            S →ₗ[R] S ⊗[R] S).codRestrict\n        ((KaehlerDifferential.ideal R S).restrictScalars R)\n        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R) :\n      _ →ₗ[R] _)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Kaehler/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
