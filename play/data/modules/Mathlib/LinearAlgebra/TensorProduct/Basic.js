window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.TensorProduct.Basic"] = {
  "module": "Mathlib.LinearAlgebra.TensorProduct.Basic",
  "cards": {
    "TensorProduct.addCommGroup": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"TensorProduct","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"SubNegMonoid.sub'","module":"Mathlib.Algebra.Group.DivInvMonoid","kind":"def"},{"where":"body","name":"TensorProduct.addCommMonoid","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.leftHasSMul","module":"Mathlib.LinearAlgebra.TensorProduct.Defs","kind":"def"},{"where":"body","name":"TensorProduct.neg","module":"Mathlib.LinearAlgebra.TensorProduct.Basic","kind":"def"},{"where":"body","name":"TensorProduct.neg_add_cancel","module":"Mathlib.LinearAlgebra.TensorProduct.Basic","kind":"theorem"},{"where":"body","name":"ZSMul.ofSMul","module":"Mathlib.Algebra.Group.DivInvMonoid","kind":"def"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":389,"column":0},"end":{"line":397,"column":7}},
      "name": "TensorProduct.addCommGroup",
      "module": "Mathlib.LinearAlgebra.TensorProduct.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  [inst : CommSemiring R] →\n    {M : Type u_2} →\n      {N : Type u_3} →\n        [inst_1 : AddCommGroup M] →\n          [inst_2 : AddCommMonoid N] →\n            [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R N] → AddCommGroup (TensorProduct R M N)",
      "doc": "",
      "short": "addCommGroup",
      "signature_source": "instance addCommGroup : AddCommGroup (M ⊗[R] N) where\n  neg_add_cancel := fun x => TensorProduct.neg_add_cancel x\n  zsmul_zero' := by simp\n  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]\n  zsmul_neg' := fun n x => by\n    change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)\n    rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,\n      ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]\n    rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
