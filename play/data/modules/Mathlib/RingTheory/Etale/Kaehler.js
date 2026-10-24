window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Etale.Kaehler"] = {
  "module": "Mathlib.RingTheory.Etale.Kaehler",
  "cards": {
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.FormallyEtale","module":"Mathlib.RingTheory.Etale.Basic","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.leftModule","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"KaehlerDifferential.mapBaseChange","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"LinearEquiv.ofBijective","module":"Mathlib.Algebra.Module.Submodule.Equiv","kind":"def"}],
      "range": {"start":{"line":33,"column":0},"end":{"line":45,"column":38}},
      "name": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
      "module": "Mathlib.RingTheory.Etale.Kaehler",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  (S : Type u_2) →\n    (T : Type u_3) →\n      [inst : CommRing R] →\n        [inst_1 : CommRing S] →\n          [inst_2 : CommRing T] →\n            [inst_3 : Algebra R S] →\n              [inst_4 : Algebra R T] →\n                [inst_5 : Algebra S T] →\n                  [IsScalarTower R S T] → [Algebra.FormallyEtale S T] → TensorProduct S T Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]",
      "doc": "The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.\nAlso see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehlerEquiv`.\n",
      "short": "tensorKaehlerEquivOfFormallyEtale",
      "signature_source": "@[simps! apply] noncomputable\ndef KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEtale S T] :\n    T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] :=",
      "body_source": "by\n  refine LinearEquiv.ofBijective (mapBaseChange R S T)\n    ⟨?_, fun x ↦ (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩\n  rw [injective_iff_map_eq_zero]\n  intro x hx\n  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx\n  rw [Subsingleton.elim x 0, map_zero]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
