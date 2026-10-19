window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finsupp.Defs"] = {
  "module": "Mathlib.Data.Finsupp.Defs",
  "cards": {
    "Finsupp": {
      "seed": false,
      "refs": [],
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
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
