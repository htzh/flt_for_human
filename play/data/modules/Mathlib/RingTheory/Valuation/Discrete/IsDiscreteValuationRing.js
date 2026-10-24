window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing"] = {
  "module": "Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing",
  "cards": {
    "IsDiscreteValuationRing.maximalIdeal": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum","module":"Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","kind":"inductive"},{"where":"type","name":"IsDiscreteValuationRing","module":"Mathlib.RingTheory.DiscreteValuationRing.Basic","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"IsLocalRing.maximalIdeal","module":"Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs","kind":"def"}],
      "range": {"start":{"line":40,"column":0},"end":{"line":44,"column":79}},
      "name": "IsDiscreteValuationRing.maximalIdeal",
      "module": "Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing",
      "kind": "def",
      "elaborated_type": "(A : Type u_1) →\n  [inst : CommRing A] → [inst_1 : IsDomain A] → [IsDiscreteValuationRing A] → IsDedekindDomain.HeightOneSpectrum A",
      "doc": "The maximal ideal of a discrete valuation ring. ",
      "short": "maximalIdeal",
      "signature_source": "def maximalIdeal : HeightOneSpectrum A where\n  asIdeal := IsLocalRing.maximalIdeal A\n  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)\n  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
