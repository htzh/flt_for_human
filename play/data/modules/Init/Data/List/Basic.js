window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.List.Basic"] = {
  "module": "Init.Data.List.Basic",
  "cards": {
    "List.Pairwise": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":1355,"column":0},"end":{"line":1380,"column":91}},
      "name": "List.Pairwise",
      "module": "Init.Data.List.Basic",
      "kind": "inductive",
      "elaborated_type": "{α : Type u} → (α → α → Prop) → List α → Prop",
      "doc": "Each element of a list is related to all later elements of the list by `R`.\n\n`Pairwise R l` means that all the elements of `l` with earlier indexes are `R`-related to all the\nelements with later indexes.\n\nFor example, `Pairwise (· ≠ ·) l` asserts that `l` has no duplicates, and `Pairwise (· < ·) l`\nasserts that `l` is (strictly) sorted.\n\nExamples:\n * `Pairwise (· < ·) [1, 2, 3] ↔ (1 < 2 ∧ 1 < 3) ∧ 2 < 3`\n * `Pairwise (· = ·) [1, 2, 3] = False`\n * `Pairwise (· ≠ ·) [1, 2, 3] = True`\n",
      "short": "Pairwise",
      "signature_source": "inductive Pairwise : List α → Prop\n  /-- All elements of the empty list are vacuously pairwise related. -/\n  | nil : Pairwise []\n  /--\n  A nonempty list is pairwise related with `R` if the head is related to every element of the tail\n  and the tail is itself pairwise related.\n\n  That is, `a :: l` is `Pairwise R` if:\n   * `R` relates `a` to every element of `l`\n   * `l` is `Pairwise R`.\n  -/\n  | cons : ∀ {a : α} {l : List α}, (∀ a', a' ∈ l → R a a') → Pairwise l → Pairwise (a :: l)",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/List/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
