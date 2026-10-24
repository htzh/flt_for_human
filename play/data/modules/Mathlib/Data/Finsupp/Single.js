window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finsupp.Single"] = {
  "module": "Mathlib.Data.Finsupp.Single",
  "cards": {
    "Finsupp.single": {
      "refs": [{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"body","name":"Pi.single","module":"Mathlib.Algebra.Notation.Pi.Basic","kind":"def"},{"where":"body","name":"EmptyCollection.emptyCollection","module":"Init.Core","kind":"abbrev"}],
      "range": {"start":{"line":46,"column":0},"end":{"line":54,"column":34}},
      "name": "Finsupp.single",
      "module": "Mathlib.Data.Finsupp.Single",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → {M : Type u_4} → [inst : Zero M] → α → M → α →₀ M",
      "doc": "`single a b` is the finitely supported function with value `b` at `a` and zero otherwise. ",
      "short": "single",
      "signature_source": "def single (a : α) (b : M) : α →₀ M where\n  support :=\n    haveI := Classical.decEq M\n    if b = 0 then ∅ else {a}\n  toFun :=\n    haveI := Classical.decEq α\n    Pi.single a b\n  mem_support_toFun a' := by grind",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finsupp/Single.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
