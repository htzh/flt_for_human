window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.TypeTags.Basic"] = {
  "module": "Mathlib.Algebra.Group.TypeTags.Basic",
  "cards": {
    "Multiplicative": {
      "refs": [],
      "range": {"start":{"line":44,"column":0},"end":{"line":46,"column":35}},
      "name": "Multiplicative",
      "module": "Mathlib.Algebra.Group.TypeTags.Basic",
      "kind": "def",
      "elaborated_type": "Type u_1 → Type u_1",
      "doc": "If `α` carries some additive structure, then `Multiplicative α` carries the corresponding\nmultiplicative structure. ",
      "short": "Multiplicative",
      "signature_source": "def Multiplicative (α : Type*) :=",
      "body_source": "α",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean",
      "has_source": true,
      "has_refs": false
    },
    "Multiplicative.commMonoid": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"body","name":"CommSemigroup","module":"Mathlib.Algebra.Group.Semigroup","kind":"inductive"},{"where":"body","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"body","name":"Multiplicative.commSemigroup","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"body","name":"Multiplicative.monoid","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"}],
      "range": {"start":{"line":361,"column":0},"end":{"line":362,"column":62}},
      "name": "Multiplicative.commMonoid",
      "module": "Mathlib.Algebra.Group.TypeTags.Basic",
      "kind": "def",
      "elaborated_type": "{α : Type u} → [AddCommMonoid α] → CommMonoid (Multiplicative α)",
      "doc": "",
      "short": "commMonoid",
      "signature_source": "instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=",
      "body_source": "{ Multiplicative.monoid, Multiplicative.commSemigroup with }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
