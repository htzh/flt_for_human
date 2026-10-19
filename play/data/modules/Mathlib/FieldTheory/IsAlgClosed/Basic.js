window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.IsAlgClosed.Basic"] = {
  "module": "Mathlib.FieldTheory.IsAlgClosed.Basic",
  "cards": {
    "IsAlgClosed": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":58,"column":0},"end":{"line":63,"column":31}},
      "name": "IsAlgClosed",
      "module": "Mathlib.FieldTheory.IsAlgClosed.Basic",
      "kind": "inductive",
      "elaborated_type": "(k : Type u) → [Field k] → Prop",
      "doc": "An algebraically closed field is one where every polynomial splits. Equivalently, all\nnon-constant polynomials have a root. See `IsAlgClosed.exists_root` and\n`IsAlgClosed.of_exists_root`. ",
      "short": "IsAlgClosed",
      "signature_source": "@[stacks 09GR \"The definition of `IsAlgClosed` in mathlib is 09GR (4)\"]\nclass IsAlgClosed : Prop where\n  splits : ∀ p : k[X], p.Splits",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/IsAlgClosed/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
