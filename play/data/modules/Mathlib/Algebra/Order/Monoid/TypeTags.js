window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Order.Monoid.TypeTags"] = {
  "module": "Mathlib.Algebra.Order.Monoid.TypeTags",
  "cards": {
    "Multiplicative.isOrderedCancelMonoid": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"IsOrderedCancelAddMonoid","module":"Mathlib.Algebra.Order.Monoid.Defs","kind":"inductive"},{"where":"type","name":"IsOrderedCancelMonoid","module":"Mathlib.Algebra.Order.Monoid.Defs","kind":"inductive"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.commMonoid","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.preorder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Preorder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"}],
      "range": {"start":{"line":25,"column":0},"end":{"line":28,"column":86}},
      "name": "Multiplicative.isOrderedCancelMonoid",
      "module": "Mathlib.Algebra.Order.Monoid.TypeTags",
      "kind": "theorem",
      "elaborated_type": "∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α],\n  IsOrderedCancelMonoid (Multiplicative α)",
      "doc": "",
      "short": "isOrderedCancelMonoid",
      "signature_source": "instance Multiplicative.isOrderedCancelMonoid\n    [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :\n    IsOrderedCancelMonoid (Multiplicative α) :=",
      "body_source": "{ le_of_mul_le_mul_left := @IsOrderedCancelAddMonoid.le_of_add_le_add_left α _ _ _ }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/TypeTags.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
