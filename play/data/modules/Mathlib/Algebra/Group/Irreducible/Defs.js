window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Irreducible.Defs"] = {
  "module": "Mathlib.Algebra.Group.Irreducible.Defs",
  "cards": {
    "Irreducible": {
      "refs": [{"where":"type","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"}],
      "range": {"start":{"line":39,"column":0},"end":{"line":48,"column":62}},
      "name": "Irreducible",
      "module": "Mathlib.Algebra.Group.Irreducible.Defs",
      "kind": "inductive",
      "elaborated_type": "{M : Type u_1} → [Monoid M] → M → Prop",
      "doc": "`Irreducible p` states that `p` is non-unit and only factors into units.\n\nWe explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a\nmonoid allows us to reuse irreducible for associated elements. \n\n[Wikidata Q2989575](https://www.wikidata.org/wiki/Q2989575)",
      "short": "Irreducible",
      "signature_source": "@[to_additive (attr := wikidata Q2989575)]\nstructure Irreducible (p : M) : Prop where\n  /-- An irreducible element is not a unit. -/\n  not_isUnit : ¬IsUnit p\n  /-- If an irreducible element factors, then one factor is a unit. -/\n  isUnit_or_isUnit ⦃a b : M⦄ : p = a * b → IsUnit a ∨ IsUnit b",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Irreducible/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
