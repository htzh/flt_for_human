window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags"] = {
  "module": "Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags",
  "cards": {
    "Multiplicative.linearOrder": {
      "refs": [{"where":"type","name":"LinearOrder","module":"Mathlib.Order.Defs.LinearOrder","kind":"inductive"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"body","name":"Multiplicative.partialOrder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"}],
      "range": {"start":{"line":42,"column":0},"end":{"line":43,"column":34}},
      "name": "Multiplicative.linearOrder",
      "module": "Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → [LinearOrder α] → LinearOrder (Multiplicative α)",
      "doc": "",
      "short": "linearOrder",
      "signature_source": "instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=",
      "body_source": "inferInstanceAs <| LinearOrder α",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/TypeTags.lean",
      "has_source": true,
      "has_refs": true
    },
    "Multiplicative.preorder": {
      "refs": [{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Preorder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"}],
      "range": {"start":{"line":30,"column":0},"end":{"line":31,"column":31}},
      "name": "Multiplicative.preorder",
      "module": "Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → [Preorder α] → Preorder (Multiplicative α)",
      "doc": "",
      "short": "preorder",
      "signature_source": "instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=",
      "body_source": "inferInstanceAs <| Preorder α",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/TypeTags.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
