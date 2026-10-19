window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.SetTheory.Cardinal.Defs"] = {
  "module": "Mathlib.SetTheory.Cardinal.Defs",
  "cards": {
    "Cardinal": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":78,"column":0},"end":{"line":83,"column":32}},
      "name": "Cardinal",
      "module": "Mathlib.SetTheory.Cardinal.Defs",
      "kind": "def",
      "elaborated_type": "Type (u + 1)",
      "doc": "`Cardinal.{u}` is the type of cardinal numbers in `Type u`,\ndefined as the quotient of `Type u` by existence of an equivalence\n(a bijection with explicit inverse). ",
      "short": "Cardinal",
      "signature_source": "@[pp_with_univ, wikidata Q163875]\ndef Cardinal : Type (u + 1) :=",
      "body_source": "Quotient Cardinal.isEquivalent",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "Cardinal.mk": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":87,"column":0},"end":{"line":89,"column":14}},
      "name": "Cardinal.mk",
      "module": "Mathlib.SetTheory.Cardinal.Defs",
      "kind": "def",
      "elaborated_type": "Type u → Cardinal.{u}",
      "doc": "The cardinal number of a type ",
      "short": "mk",
      "signature_source": "def mk : Type u → Cardinal :=",
      "body_source": "Quotient.mk'",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
