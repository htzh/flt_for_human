window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.Defs.PhiGen"] = {
  "module": "FLTForHuman.ModularCurve.Defs.PhiGen",
  "cards": {
    "ModularCurve.EvalSymm": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"HahnSeries.powerSeriesAlgebra","module":"Mathlib.RingTheory.HahnSeries.PowerSeries","kind":"def"},{"where":"body","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"body","name":"Polynomial.aeval","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"body","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"body","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"body","name":"Unit","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":78,"column":0},"end":{"line":83,"column":57}},
      "name": "ModularCurve.EvalSymm",
      "module": "FLTForHuman.ModularCurve.Defs.PhiGen",
      "kind": "def",
      "elaborated_type": "Polynomial (Polynomial ℤ) → Prop",
      "doc": "`Φ` is symmetric in its two variables when evaluating it at `(x, y)` and at\n`(y, x)` agree. ",
      "short": "EvalSymm",
      "signature_source": "def EvalSymm (Φ : Polynomial (Polynomial ℤ)) : Prop :=",
      "body_source": "∀ x y : LaurentSeries ℚ,\n    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y\n      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/PhiGen.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.PhiIrreducible": {
      "refs": [{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"body","name":"ModularCurve.jq","module":"FLTForHuman.ModularCurve.Defs.Jq","kind":"def"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"HahnSeries.powerSeriesAlgebra","module":"Mathlib.RingTheory.HahnSeries.PowerSeries","kind":"def"},{"where":"body","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"body","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"body","name":"Irreducible","module":"Mathlib.Algebra.Group.Irreducible.Defs","kind":"inductive"},{"where":"body","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"body","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"body","name":"Unit","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":119,"column":0},"end":{"line":122,"column":27}},
      "name": "ModularCurve.PhiIrreducible",
      "module": "FLTForHuman.ModularCurve.Defs.PhiGen",
      "kind": "def",
      "elaborated_type": "{N : ℕ} → [inst : NeZero N] → ModularCurve.ModularPolynomialData N → Prop",
      "doc": "The irreducibility half of the splitting input, transported into\n`ℚ(j(q))[Y]`. ",
      "short": "PhiIrreducible",
      "signature_source": "def PhiIrreducible (data : ModularPolynomialData N) : Prop :=",
      "body_source": "Irreducible data.toAdjoin",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/PhiGen.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
