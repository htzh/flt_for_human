window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.DedekindDomain.AdicValuation"] = {
  "module": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
  "cards": {
    "IsDedekindDomain.HeightOneSpectrum.intValuation": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsDedekindDomain","module":"Mathlib.RingTheory.DedekindDomain.Basic","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum","module":"Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","kind":"inductive"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.commMonoid","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.isOrderedCancelMonoid","module":"Mathlib.Algebra.Order.Monoid.TypeTags","kind":"theorem"},{"where":"type","name":"Multiplicative.linearOrder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Valuation","module":"Mathlib.RingTheory.Valuation.Basic","kind":"inductive"},{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IsDedekindDomain.HeightOneSpectrum.intValuation.map_add_le_max'","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"theorem"},{"where":"body","name":"IsDedekindDomain.HeightOneSpectrum.intValuation.map_mul'","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"theorem"},{"where":"body","name":"IsDedekindDomain.HeightOneSpectrum.intValuation.map_one'","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"theorem"},{"where":"body","name":"IsDedekindDomain.HeightOneSpectrum.intValuation.map_zero'","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"theorem"},{"where":"body","name":"IsDedekindDomain.HeightOneSpectrum.intValuationDef","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"def"}],
      "range": {"start":{"line":166,"column":0},"end":{"line":172,"column":51}},
      "name": "IsDedekindDomain.HeightOneSpectrum.intValuation",
      "module": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  [inst : CommRing R] →\n    [IsDedekindDomain R] → IsDedekindDomain.HeightOneSpectrum R → Valuation R (WithZero (Multiplicative ℤ))",
      "doc": "The `v`-adic valuation on `R`. ",
      "short": "intValuation",
      "signature_source": "def intValuation : Valuation R ℤᵐ⁰ where\n  toFun := v.intValuationDef\n  map_zero' := intValuation.map_zero' v\n  map_one' := intValuation.map_one' v\n  map_mul' := intValuation.map_mul' v\n  map_add_le_max' := intValuation.map_add_le_max' v",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsDedekindDomain","module":"Mathlib.RingTheory.DedekindDomain.Basic","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum","module":"Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum.intValuation","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"def"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.commMonoid","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.isOrderedCancelMonoid","module":"Mathlib.Algebra.Order.Monoid.TypeTags","kind":"theorem"},{"where":"type","name":"Multiplicative.linearOrder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Multiplicative.preorder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Valuation","module":"Mathlib.RingTheory.Valuation.Basic","kind":"inductive"},{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"type","name":"WithZero.one","module":"Mathlib.Algebra.GroupWithZero.WithZero","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":212,"column":0},"end":{"line":217,"column":30}},
      "name": "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one",
      "module": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.HeightOneSpectrum R) (x : R),\n  v.intValuation x ≤ 1",
      "doc": "The `v`-adic valuation on `R` is bounded above by 1. ",
      "short": "intValuation_le_one",
      "signature_source": "theorem intValuation_le_one (x : R) : v.intValuation x ≤ 1 :=",
      "body_source": "by\n  obtain rfl | hx := eq_or_ne x 0\n  · simp\n  · rw [v.intValuation_if_neg hx, ← exp_zero, exp_le_exp, Right.neg_nonpos_iff]\n    exact Int.natCast_nonneg _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"IsDedekindDomain","module":"Mathlib.RingTheory.DedekindDomain.Basic","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum","module":"Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","kind":"inductive"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum.asIdeal","module":"Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","kind":"abbrev"},{"where":"type","name":"IsDedekindDomain.HeightOneSpectrum.intValuation","module":"Mathlib.RingTheory.DedekindDomain.AdicValuation","kind":"def"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.commMonoid","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"Multiplicative.isOrderedCancelMonoid","module":"Mathlib.Algebra.Order.Monoid.TypeTags","kind":"theorem"},{"where":"type","name":"Multiplicative.linearOrder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Multiplicative.preorder","module":"Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","kind":"def"},{"where":"type","name":"Valuation","module":"Mathlib.RingTheory.Valuation.Basic","kind":"inductive"},{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"type","name":"WithZero.one","module":"Mathlib.Algebra.GroupWithZero.WithZero","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":231,"column":0},"end":{"line":234,"column":60}},
      "name": "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem",
      "module": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.HeightOneSpectrum R) (r : R),\n  v.intValuation r < 1 ↔ r ∈ v.asIdeal",
      "doc": "The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`. ",
      "short": "intValuation_lt_one_iff_mem",
      "signature_source": "theorem intValuation_lt_one_iff_mem (r : R) :\n    v.intValuation r < 1 ↔ r ∈ v.asIdeal :=",
      "body_source": "by\n  rw [intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean",
      "has_source": true,
      "has_refs": true
    },
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
