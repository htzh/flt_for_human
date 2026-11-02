window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.TensorProduct.Maps"] = {
  "module": "Mathlib.RingTheory.TensorProduct.Maps",
  "cards": {
    "Algebra.TensorProduct.lmul'": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"AlgHom.restrictScalars","module":"Mathlib.Algebra.Algebra.Tower","kind":"def"},{"where":"body","name":"Algebra.TensorProduct.leftAlgebra","module":"Mathlib.RingTheory.TensorProduct.Basic","kind":"def"},{"where":"body","name":"Algebra.TensorProduct.lmul''","module":"Mathlib.RingTheory.TensorProduct.Maps","kind":"def"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"}],
      "range": {"start":{"line":764,"column":0},"end":{"line":765,"column":60}},
      "name": "Algebra.TensorProduct.lmul'",
      "module": "Mathlib.RingTheory.TensorProduct.Maps",
      "kind": "def",
      "elaborated_type": "(R : Type uR) →\n  {S : Type uS} →\n    [inst : CommSemiring R] → [inst_1 : CommSemiring S] → [inst_2 : Algebra R S] → TensorProduct R S S →ₐ[R] S",
      "doc": "`LinearMap.mul'` as an `AlgHom` over the base ring. ",
      "short": "lmul'",
      "signature_source": "def lmul' : S ⊗[R] S →ₐ[R] S :=",
      "body_source": "(lmul'' R).restrictScalars R",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean",
      "has_source": true,
      "has_refs": true
    },
    "Algebra.TensorProduct.lmul''": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.TensorProduct.leftAlgebra","module":"Mathlib.RingTheory.TensorProduct.Basic","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"Algebra.TensorProduct.algHomOfLinearMapTensorProduct","module":"Mathlib.RingTheory.TensorProduct.Maps","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.mul'","module":"Mathlib.Algebra.Algebra.Bilinear","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.leftModule","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"}],
      "range": {"start":{"line":751,"column":0},"end":{"line":758,"column":62}},
      "name": "Algebra.TensorProduct.lmul''",
      "module": "Mathlib.RingTheory.TensorProduct.Maps",
      "kind": "def",
      "elaborated_type": "(R : Type uR) →\n  {S : Type uS} →\n    [inst : CommSemiring R] → [inst_1 : CommSemiring S] → [inst_2 : Algebra R S] → TensorProduct R S S →ₐ[S] S",
      "doc": "`LinearMap.mul'` as an `AlgHom` over the algebra. ",
      "short": "lmul''",
      "signature_source": "def lmul'' : S ⊗[R] S →ₐ[S] S :=",
      "body_source": "algHomOfLinearMapTensorProduct\n    { __ := LinearMap.mul' R S\n      map_smul' := fun s x ↦ x.inductionOn\n        (fun _ _ ↦ by simp [TensorProduct.smul_tmul', mul_assoc])\n        fun x y hx hy ↦ by simp_all [mul_add] }\n    (fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) <| by simp",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean",
      "has_source": true,
      "has_refs": true
    },
    "Algebra.TensorProduct.lmul'_apply_tmul": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.TensorProduct.lmul'","module":"Mathlib.RingTheory.TensorProduct.Maps","kind":"def"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"type","name":"TensorProduct.tmul","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"}],
      "range": {"start":{"line":772,"column":0},"end":{"line":774,"column":5}},
      "name": "Algebra.TensorProduct.lmul'_apply_tmul",
      "module": "Mathlib.RingTheory.TensorProduct.Maps",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type uR} {S : Type uS} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (a b : S),\n  (Algebra.TensorProduct.lmul' R) (a ⊗ₜ[R] b) = a * b",
      "doc": "",
      "short": "lmul'_apply_tmul",
      "signature_source": "@[simp]\ntheorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=",
      "body_source": "rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
