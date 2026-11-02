window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finset.Defs"] = {
  "module": "Mathlib.Data.Finset.Defs",
  "cards": {
    "Finset": {
      "refs": [],
      "range": {"start":{"line":72,"column":0},"end":{"line":79,"column":19}},
      "name": "Finset",
      "module": "Mathlib.Data.Finset.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u_3 → Type u_3",
      "doc": "`Finset α` is the type of finite sets of elements of `α`. It is implemented\nas a multiset (a list up to permutation) which has no duplicate elements. ",
      "short": "Finset",
      "signature_source": "@[use_set_notation_for_order, to_dual_dont_translate]\nstructure Finset (α : Type*) where\n  /-- The underlying multiset -/\n  val : Multiset α\n  /-- `val` contains no duplicates -/\n  nodup : Nodup val",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finset/Defs.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
