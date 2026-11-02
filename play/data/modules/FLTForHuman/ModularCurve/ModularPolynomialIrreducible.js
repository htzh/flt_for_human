window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.ModularPolynomialIrreducible"] = {
  "module": "FLTForHuman.ModularCurve.ModularPolynomialIrreducible",
  "cards": {
    "ModularCurve.evalAtJGen_injective": {
      "refs": [{"where":"type","name":"ModularCurve.evalAtJGen","module":"FLTForHuman.ModularCurve.Defs.Fields","kind":"def"},{"where":"type","name":"ModularCurve.jq","module":"FLTForHuman.ModularCurve.Defs.Jq","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"HahnSeries.powerSeriesAlgebra","module":"Mathlib.RingTheory.HahnSeries.PowerSeries","kind":"def"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Function.Injective","module":"Init.Data.Function","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"type","name":"Unit","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":103,"column":0},"end":{"line":110,"column":80}},
      "name": "ModularCurve.evalAtJGen_injective",
      "module": "FLTForHuman.ModularCurve.ModularPolynomialIrreducible",
      "kind": "theorem",
      "elaborated_type": "Function.Injective ⇑ModularCurve.evalAtJGen",
      "doc": "Evaluation at `jq` from `ℤ[X]` is injective, transported to `ℚ⟮jq⟯` through\n`algebraMap_comp_evalAtJGen`. FLT's `eq_of_prime` file proves it this way; the\nblock's second coefficient argument is dropped. ",
      "short": "evalAtJGen_injective",
      "signature_source": "theorem evalAtJGen_injective :\n    Function.Injective (evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮jq⟯) :=",
      "body_source": "by\n  intro a b hab\n  apply PhiGen.evalAtJ_injective\n  rw [← algebraMap_comp_evalAtJGen, RingHom.comp_apply, RingHom.comp_apply, hab]",
      "source_file": "lean/FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
