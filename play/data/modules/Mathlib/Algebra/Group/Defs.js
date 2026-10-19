window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Defs"] = {
  "module": "Mathlib.Algebra.Group.Defs",
  "cards": {
    "AddGroup": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":36,"column":0},"end":{"line":45,"column":48}},
      "name": "AddGroup",
      "module": "Mathlib.Algebra.Group.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u_2 → Type u_2",
      "doc": "An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.\n\nThere is also a binary operation `-` such that `a - b = a + -b`,\nwith a default so that `a - b = a + -b` holds by definition.\n\nUse `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an\nadditive group structure on a type with the minimum proof obligations.\n\n\n[Wikidata Q83478](https://www.wikidata.org/wiki/Q83478)",
      "short": "AddGroup",
      "signature_source": "class AddGroup (A : Type*) extends SubNegMonoid A where\n  protected neg_add_cancel : ∀ a : A, -a + a = 0",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
