window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.RatFunc.Defs"] = {
  "module": "Mathlib.FieldTheory.RatFunc.Defs",
  "cards": {
    "RatFunc": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":61,"column":0},"end":{"line":69,"column":36}},
      "name": "RatFunc",
      "module": "Mathlib.FieldTheory.RatFunc.Defs",
      "kind": "inductive",
      "elaborated_type": "(K : Type u) → [CommRing K] → Type u",
      "doc": "`RatFunc K` is `K(X)`, the field of rational functions over `K`.\n\nThe inclusion of polynomials into `RatFunc` is `algebraMap K[X] K⟮X⟯`,\nthe maps between `K⟮X⟯` and another field of fractions of `K[X]`,\nespecially `FractionRing K[X]`, are given by `IsLocalization.algEquiv`.\n",
      "short": "RatFunc",
      "signature_source": "structure RatFunc [CommRing K] : Type u where ofFractionRing ::\n/-- the coercion to the fraction ring of the polynomial ring -/\n  toFractionRing : FractionRing K[X]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
