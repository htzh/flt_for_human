window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.BigOperators.Finsupp.Basic"] = {
  "module": "Mathlib.Algebra.BigOperators.Finsupp.Basic",
  "cards": {
    "Finsupp.liftAddHom": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"AddEquiv","module":"Mathlib.Algebra.Group.Equiv.Defs","kind":"inductive"},{"where":"type","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"AddMonoidHom.add","module":"Mathlib.Algebra.Group.Hom.Basic","kind":"def"},{"where":"type","name":"AddZeroClass","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"AddMonoidHom.comp","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"def"},{"where":"body","name":"Finsupp.singleAddHom","module":"Mathlib.Algebra.Group.Finsupp","kind":"def"},{"where":"body","name":"Finsupp.sum","module":"Mathlib.Algebra.BigOperators.Finsupp.Basic","kind":"def"},{"where":"body","name":"Finsupp.sum_hom_add_index","module":"Mathlib.Algebra.BigOperators.Finsupp.Basic","kind":"theorem"}],
      "range": {"start":{"line":382,"column":0},"end":{"line":392,"column":30}},
      "name": "Finsupp.liftAddHom",
      "module": "Mathlib.Algebra.BigOperators.Finsupp.Basic",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} →\n  {M : Type u_8} →\n    {N : Type u_10} → [inst : AddZeroClass M] → [inst_1 : AddCommMonoid N] → (α → M →+ N) ≃+ ((α →₀ M) →+ N)",
      "doc": "The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`\nand monoid homomorphisms `(α →₀ M) →+ N`. ",
      "short": "liftAddHom",
      "signature_source": "def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where\n  toFun F :=\n    { toFun f := f.sum (F ·)\n      map_zero' := Finsupp.sum_zero_index\n      map_add' f g := Finsupp.sum_hom_add_index F }\n  invFun F x := F.comp (singleAddHom x)\n  left_inv F := by ext; simp\n  right_inv F := by ext; simp\n  map_add' F G := by ext; simp",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
