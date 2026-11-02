window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Coprime.Basic"] = {
  "module": "Mathlib.RingTheory.Coprime.Basic",
  "cards": {
    "IsCoprime": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":41,"column":0},"end":{"line":46,"column":26}},
      "name": "IsCoprime",
      "module": "Mathlib.RingTheory.Coprime.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [CommSemiring R] → R → R → Prop",
      "doc": "The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such\nthat `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,\ne.g., the multivariate polynomials `x₁` and `x₂` are not coprime. ",
      "short": "IsCoprime",
      "signature_source": "@[wikidata Q104752]\ndef IsCoprime : Prop :=",
      "body_source": "∃ a b, a * x + b * y = 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
