window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.IntegralClosure.IntegrallyClosed"] = {
  "module": "Mathlib.RingTheory.IntegralClosure.IntegrallyClosed",
  "cards": {
    "IsIntegrallyClosed": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"FractionRing","module":"Mathlib.RingTheory.Localization.FractionRing","kind":"abbrev"},{"where":"body","name":"IsIntegrallyClosedIn","module":"Mathlib.RingTheory.IntegralClosure.IntegrallyClosed","kind":"abbrev"},{"where":"body","name":"OreLocalization.oreSetComm","module":"Mathlib.GroupTheory.OreLocalization.OreSet","kind":"def"},{"where":"body","name":"nonZeroDivisors","module":"Mathlib.Algebra.GroupWithZero.NonZeroDivisors","kind":"def"}],
      "range": {"start":{"line":69,"column":0},"end":{"line":74,"column":93}},
      "name": "IsIntegrallyClosed",
      "module": "Mathlib.RingTheory.IntegralClosure.IntegrallyClosed",
      "kind": "abbrev",
      "elaborated_type": "(R : Type u_1) → [CommRing R] → Prop",
      "doc": "`R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.\n\nThis definition uses `FractionRing R` to denote `Frac(R)`. See `isIntegrallyClosed_iff`\nif you want to choose another field of fractions for `R`.\n",
      "short": "IsIntegrallyClosed",
      "signature_source": "abbrev IsIntegrallyClosed (R : Type*) [CommRing R] :=",
      "body_source": "IsIntegrallyClosedIn R (FractionRing R)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
