window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.BigOperators.Group.Finset.Defs"] = {
  "module": "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
  "cards": {
    "Finset.prod": {
      "refs": [{"where":"type","name":"CommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"body","name":"Finset.val","module":"Mathlib.Data.Finset.Defs","kind":"abbrev"},{"where":"body","name":"Multiset.map","module":"Mathlib.Data.Multiset.MapFold","kind":"def"},{"where":"body","name":"Multiset.prod","module":"Mathlib.Algebra.BigOperators.Group.Multiset.Defs","kind":"def"}],
      "range": {"start":{"line":59,"column":0},"end":{"line":69,"column":18}},
      "name": "Finset.prod",
      "module": "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
      "kind": "def",
      "elaborated_type": "{ι : Type u_1} → {M : Type u_3} → [CommMonoid M] → Finset ι → (ι → M) → M",
      "doc": "`∏ x ∈ s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`.\n\nWhen the index type is a `Fintype`, the notation `∏ x, f x`, is a shorthand for\n`∏ x ∈ Finset.univ, f x`. ",
      "short": "prod",
      "signature_source": "@[to_additive /-- `∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements\nof the finite set `s`.\n\nWhen the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for\n`∑ x ∈ Finset.univ, f x`. -/]\nprotected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=",
      "body_source": "(s.1.map f).prod",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Finset.sum": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"body","name":"Finset.val","module":"Mathlib.Data.Finset.Defs","kind":"abbrev"},{"where":"body","name":"Multiset.map","module":"Mathlib.Data.Multiset.MapFold","kind":"def"},{"where":"body","name":"Multiset.sum","module":"Mathlib.Algebra.BigOperators.Group.Multiset.Defs","kind":"def"}],
      "range": {"start":{"line":63,"column":2},"end":{"line":67,"column":28}},
      "name": "Finset.sum",
      "module": "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
      "kind": "def",
      "elaborated_type": "{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M",
      "doc": "`∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements\nof the finite set `s`.\n\nWhen the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for\n`∑ x ∈ Finset.univ, f x`. ",
      "short": "sum",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
