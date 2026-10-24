window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.DedekindDomain.AdicValuation"] = {
  "module": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
  "cards": {
    "IsDedekindDomain.HeightOneSpectrum.valuation": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IsDedekindDomain","module":"Mathlib.RingTheory.DedekindDomain.Basic","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum","module":"Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","kind":"inductive"},{"where":"type","name":"IsFractionRing","module":"Mathlib.RingTheory.Localization.FractionRing","kind":"abbrev"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.commMonoid","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.isOrderedCancelMonoid","module":"Mathlib.Algebra.Order.Monoid.TypeTags","kind":"theorem"},{"where":"type","name":"Multiplicative.linearOrder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Valuation","module":"Mathlib.RingTheory.Valuation.Basic","kind":"inductive"},{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IsDedekindDomain.HeightOneSpectrum.intValuation","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"def"},{"where":"body","name":"Valuation.extendToLocalization","module":"Mathlib.RingTheory.Valuation.ExtendToLocalization","kind":"def"},{"where":"body","name":"nonZeroDivisors","module":"Mathlib.Algebra.GroupWithZero.NonZeroDivisors","kind":"def"}],
      "range": {"start":{"line":319,"column":0},"end":{"line":324,"column":68}},
      "name": "IsDedekindDomain.HeightOneSpectrum.valuation",
      "module": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  [inst : CommRing R] →\n    [IsDedekindDomain R] →\n      (K : Type u_2) →\n        [inst_2 : Field K] →\n          [inst_3 : Algebra R K] →\n            [IsFractionRing R K] → IsDedekindDomain.HeightOneSpectrum R → Valuation K (WithZero (Multiplicative ℤ))",
      "doc": "The `v`-adic valuation of `x : K` is the valuation of `r` divided by the valuation of `s`,\nwhere `r` and `s` are chosen so that `x = r/s`. ",
      "short": "valuation",
      "signature_source": "@[no_expose]\ndef valuation (v : HeightOneSpectrum R) : Valuation K ℤᵐ⁰ :=",
      "body_source": "v.intValuation.extendToLocalization\n    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
