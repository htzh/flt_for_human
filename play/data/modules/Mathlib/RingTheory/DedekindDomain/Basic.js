window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.DedekindDomain.Basic"] = {
  "module": "Mathlib.RingTheory.DedekindDomain.Basic",
  "cards": {
    "IsDedekindDomain": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":132,"column":0},"end":{"line":145,"column":38}},
      "name": "IsDedekindDomain",
      "module": "Mathlib.RingTheory.DedekindDomain.Basic",
      "kind": "inductive",
      "elaborated_type": "(A : Type u_2) → [CommRing A] → Prop",
      "doc": "A Dedekind domain is an integral domain that is Noetherian, integrally closed, and\nhas Krull dimension at most one.\n\nThis is definition 3.2 of [Neukirch1992].\n\nThis is exactly `IsDedekindRing` plus the `IsDomain` hypothesis.\n\nThe integral closure condition is independent of the choice of field of fractions:\nuse `isDedekindDomain_iff` to prove `IsDedekindDomain` for a given `fraction_map`.\n\nSee also `isDedekindDomain_iff_isDiscreteValuationRing_atPrime` and\n`isDedekindDomain_iff_mul_inv_cancel`. ",
      "short": "IsDedekindDomain",
      "signature_source": "class IsDedekindDomain : Prop\n  extends IsDomain A, IsDedekindRing A",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
