window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.BigOperators.Group.Finset.Defs"] = {
  "module": "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
  "cards": {
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
