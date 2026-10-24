window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finsupp.Defs"] = {
  "module": "Mathlib.Data.Finsupp.Defs",
  "cards": {
    "Finsupp": {
      "refs": [{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":86,"column":0},"end":{"line":95,"column":52}},
      "name": "Finsupp",
      "module": "Mathlib.Data.Finsupp.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u_8 → (M : Type u_9) → [Zero M] → Type (max u_8 u_9)",
      "doc": "`Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that\n`f x = 0` for all but finitely many `x`. ",
      "short": "Finsupp",
      "signature_source": "structure Finsupp (α : Type*) (M : Type*) [Zero M] where\n  /-- The support of a finitely supported function (aka `Finsupp`). -/\n  support : Finset α\n  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/\n  toFun : α → M\n  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its\n  underlying function is nonzero. -/\n  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finsupp/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Finsupp.support": {
      "refs": [{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":90,"column":2},"end":{"line":90,"column":9}},
      "name": "Finsupp.support",
      "module": "Mathlib.Data.Finsupp.Defs",
      "kind": "abbrev",
      "elaborated_type": "{α : Type u_8} → {M : Type u_9} → [inst : Zero M] → (α →₀ M) → Finset α",
      "doc": "The support of a finitely supported function (aka `Finsupp`). ",
      "short": "support",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
