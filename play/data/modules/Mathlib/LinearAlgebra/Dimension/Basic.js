window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Dimension.Basic"] = {
  "module": "Mathlib.LinearAlgebra.Dimension.Basic",
  "cards": {
    "Module.rank": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Cardinal","module":"Mathlib.SetTheory.Cardinal.Defs","kind":"def"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":53,"column":0},"end":{"line":69,"column":53}},
      "name": "Module.rank",
      "module": "Mathlib.LinearAlgebra.Dimension.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  (M : Type u_2) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Cardinal.{u_2}",
      "doc": "The rank of a module, defined as a term of type `Cardinal`.\n\nWe define this as the supremum of the cardinalities of linearly independent subsets.\nThe supremum may not be attained, see https://mathoverflow.net/a/263053.\n\nFor a free module over any ring satisfying the strong rank condition\n(e.g. left-Noetherian rings, commutative rings, and in particular division rings and fields),\nthis is the same as the dimension of the space (i.e. the cardinality of any basis).\n\nIn particular this agrees with the usual notion of the dimension of a vector space.\n\nSee also `Module.finrank` for a `ℕ`-valued function which returns the correct value\nfor a finite-dimensional vector space (but 0 for an infinite-dimensional vector space).\n\n\n[Stacks Tag 09G3](https://stacks.math.columbia.edu/tag/09G3) (first part)",
      "short": "rank",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
