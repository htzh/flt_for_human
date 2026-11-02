window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.Perfect"] = {
  "module": "Mathlib.FieldTheory.Perfect",
  "cards": {
    "PerfectField": {
      "refs": [{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":286,"column":0},"end":{"line":291,"column":70}},
      "name": "PerfectField",
      "module": "Mathlib.FieldTheory.Perfect",
      "kind": "inductive",
      "elaborated_type": "(K : Type u_1) → [Field K] → Prop",
      "doc": "A perfect field.\n\nSee also `PerfectRing` for a generalisation in positive characteristic. ",
      "short": "PerfectField",
      "signature_source": "class PerfectField (K : Type*) [Field K] : Prop where\n  /-- A field is perfect if every irreducible polynomial is separable. -/\n  separable_of_irreducible : ∀ {f : K[X]}, Irreducible f → f.Separable",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Perfect.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
