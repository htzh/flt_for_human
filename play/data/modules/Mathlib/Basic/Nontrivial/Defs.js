window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Basic.Nontrivial.Defs"] = {
  "module": "Mathlib.Basic.Nontrivial.Defs",
  "cards": {
    "Nontrivial": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":26,"column":0},"end":{"line":30,"column":35}},
      "name": "Nontrivial",
      "module": "Mathlib.Basic.Nontrivial.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u_3 → Prop",
      "doc": "Predicate typeclass for expressing that a type is not reduced to a single element. In rings,\nthis is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. ",
      "short": "Nontrivial",
      "signature_source": "class Nontrivial (α : Type*) : Prop where\n  /-- In a nontrivial type, there exists a pair of distinct terms. -/\n  exists_pair_ne : ∃ x y : α, x ≠ y",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Basic/Nontrivial/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
