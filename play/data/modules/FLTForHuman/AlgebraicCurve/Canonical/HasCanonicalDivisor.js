window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor"] = {
  "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
  "cards": {
    "AlgebraicCurve.Place.ord_uniformizerSubring": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.ord","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"def"},{"where":"type","name":"AlgebraicCurve.Place.uniformizerSubring","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"ValuationSubring","module":"Mathlib.RingTheory.Valuation.ValuationSubring","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":64,"column":0},"end":{"line":65,"column":101}},
      "name": "AlgebraicCurve.Place.ord_uniformizerSubring",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F]\n  (v : AlgebraicCurve.Place K F), v.ord ↑v.uniformizerSubring = 1",
      "doc": "",
      "short": "ord_uniformizerSubring",
      "signature_source": "theorem ord_uniformizerSubring : v.ord (uniformizerSubring v : F) = 1 :=",
      "body_source": "v.ord_coe_irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": {
      "refs": [{"where":"type","name":"AlgebraicCurve.HasCanonicalDivisor","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.IsCurveOver","module":"FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.EssFiniteType","module":"Mathlib.RingTheory.EssentialFiniteness","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"PerfectField","module":"Mathlib.FieldTheory.Perfect","kind":"inductive"}],
      "range": {"start":{"line":442,"column":0},"end":{"line":455,"column":48}},
      "name": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F] [PerfectField K]\n  [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F], AlgebraicCurve.HasCanonicalDivisor",
      "doc": "",
      "short": "hasCanonicalDivisor_of_isCurveOver",
      "signature_source": "theorem hasCanonicalDivisor_of_isCurveOver\n    {K F : Type*} [Field K] [Field F] [Algebra K F]\n    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :\n    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=",
      "body_source": "by\n  have hspan := valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField (K := K) (F := F)\n  haveI : ∀ v : Place K F, v.DCoordGenerates := fun v =>\n    Place.dCoordGenerates_of_valSubringKaehlerSpanTop hspan v\n  obtain ⟨t, htr, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)\n  haveI := hfd\n  haveI := hsep\n  exact hasCanonicalDivisor_of_generator_finiteSupport\n    (KaehlerDifferential.D_ne_zero_of_transcendental K t htr)\n    (KaehlerDifferential.span_D_eq_top_of_transcendental K t htr)\n    (finite_ordDifferential_D_ne_zero hspan htr)",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
