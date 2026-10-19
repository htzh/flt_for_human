window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Subgroup.Defs"] = {
  "module": "Mathlib.Algebra.Group.Subgroup.Defs",
  "cards": {
    "AddSubgroup": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":300,"column":0},"end":{"line":304,"column":43}},
      "name": "AddSubgroup",
      "module": "Mathlib.Algebra.Group.Subgroup.Defs",
      "kind": "inductive",
      "elaborated_type": "(G : Type u_3) → [AddGroup G] → Type u_3",
      "doc": "An additive subgroup of an additive group `G` is a subset containing 0, closed\nunder addition and additive inverse. \n\n[Wikidata Q466109](https://www.wikidata.org/wiki/Q466109)",
      "short": "AddSubgroup",
      "signature_source": "structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where\n  /-- `G` is closed under negation -/\n  neg_mem' {x} : x ∈ carrier → -x ∈ carrier",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
