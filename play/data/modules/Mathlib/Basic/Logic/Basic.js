window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Basic.Logic.Basic"] = {
  "module": "Mathlib.Basic.Logic.Basic",
  "cards": {
    "Classical.decEq": {
      "seed": true,
      "refs": [{"where":"body","name":"Classical.propDecidable","module":"Init.Classical","kind":"def"},{"where":"body","name":"inferInstance","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":765,"column":0},"end":{"line":767,"column":72}},
      "name": "Classical.decEq",
      "module": "Mathlib.Basic.Logic.Basic",
      "kind": "def",
      "elaborated_type": "(α : Sort u_2) → DecidableEq α",
      "doc": "Any type `α` has decidable equality classically. ",
      "short": "decEq",
      "signature_source": "@[instance_reducible]\nnoncomputable def decEq (α : Sort*) : DecidableEq α :=",
      "body_source": "by infer_instance",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Basic/Logic/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "Fact": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":150,"column":0},"end":{"line":170,"column":9}},
      "name": "Fact",
      "module": "Mathlib.Basic.Logic.Basic",
      "kind": "inductive",
      "elaborated_type": "Prop → Prop",
      "doc": "Wrapper for adding elementary propositions to the type class systems.\nWarning: this can easily be abused. See the rest of this docstring for details.\n\nCertain propositions should not be treated as a class globally,\nbut sometimes it is very convenient to be able to use the type class system\nin specific circumstances.\n\nFor example, `ZMod p` is a field if and only if `p` is a prime number.\nIn order to be able to find this field instance automatically by type class search,\nwe have to turn `p.Prime` into an instance implicit assumption.\n\nOn the other hand, making `Nat.Prime` a class would require a major refactoring of the library,\nand it is questionable whether making `Nat.Prime` a class is desirable at all.\nThe compromise is to add the assumption `[Fact p.Prime]` to `ZMod.instField`.\n\nIn particular, this class is not intended for turning the type class system\ninto an automated theorem prover for first-order logic. ",
      "short": "Fact",
      "signature_source": "class Fact (p : Prop) : Prop where\n  /-- `Fact.out` contains the unwrapped witness for the fact represented by the instance of\n  `Fact p`. -/\n  out : p",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Basic/Logic/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
