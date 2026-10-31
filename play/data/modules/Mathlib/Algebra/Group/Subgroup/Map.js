window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Subgroup.Map"] = {
  "module": "Mathlib.Algebra.Group.Subgroup.Map",
  "cards": {
    "AddSubgroup.addSubgroupOf": {
      "refs": [{"where":"type","name":"AddGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"AddSubgroup","module":"Mathlib.Algebra.Group.Subgroup.Defs","kind":"inductive"},{"where":"body","name":"AddSubgroup.comap","module":"Mathlib.Algebra.Group.Subgroup.Map","kind":"def"},{"where":"body","name":"AddSubgroup.subtype","module":"Mathlib.Algebra.Group.Subgroup.Defs","kind":"def"}],
      "range": {"start":{"line":283,"column":2},"end":{"line":283,"column":86}},
      "name": "AddSubgroup.addSubgroupOf",
      "module": "Mathlib.Algebra.Group.Subgroup.Map",
      "kind": "def",
      "elaborated_type": "{G : Type u_1} → [inst : AddGroup G] → AddSubgroup G → (K : AddSubgroup G) → AddSubgroup ↥K",
      "doc": "For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. ",
      "short": "addSubgroupOf",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
