window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.P1.DXCoeff"] = {
  "module": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
  "cards": {
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne": {
      "refs": [{"where":"type","name":"AlgebraicCurve.HasPrincipalDivisors","module":"FLTForHuman.AlgebraicCurve.Defs.Divisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.IsCurveOver","module":"FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.KaehlerRankOne","module":"FLTForHuman.AlgebraicCurve.P1.DXCoeff","kind":"def"},{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.FiniteResidue","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":28,"column":0},"end":{"line":33,"column":29}},
      "name": "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne",
      "module": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F]\n  [AlgebraicCurve.HasPrincipalDivisors K F] [∀ (v : AlgebraicCurve.Place K F), v.FiniteResidue],\n  AlgebraicCurve.KaehlerRankOne K F → AlgebraicCurve.IsCurveOver K F",
      "doc": "Pin row #234. ",
      "short": "of_finiteResidue_of_kaehlerRankOne",
      "signature_source": "theorem of_finiteResidue_of_kaehlerRankOne\n    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]\n    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where\n  finiteResidue v := Place.FiniteResidue.finite (v := v)\n  kaehler_free_rank_one := hΩ",
      "body_source": "",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/P1/DXCoeff.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.KaehlerRankOne": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"Module.Free","module":"Mathlib.LinearAlgebra.FreeModule.Basic","kind":"inductive"},{"where":"body","name":"Module.finrank","module":"Mathlib.LinearAlgebra.Dimension.Finrank","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":20,"column":0},"end":{"line":22,"column":52}},
      "name": "AlgebraicCurve.KaehlerRankOne",
      "module": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
      "kind": "def",
      "elaborated_type": "(K : Type u_1) → (F : Type u_2) → [inst : Field K] → [inst_1 : Field F] → [Algebra K F] → Prop",
      "doc": "Pin row #233. ",
      "short": "KaehlerRankOne",
      "signature_source": "def KaehlerRankOne : Prop :=",
      "body_source": "Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/P1/DXCoeff.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne": {
      "refs": [{"where":"type","name":"AlgebraicCurve.IsCurveOver","module":"FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.KaehlerRankOne","module":"FLTForHuman.AlgebraicCurve.P1.DXCoeff","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"RatFunc","module":"Mathlib.FieldTheory.RatFunc.Defs","kind":"inductive"}],
      "range": {"start":{"line":41,"column":0},"end":{"line":44,"column":51}},
      "name": "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne",
      "module": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
      "kind": "theorem",
      "elaborated_type": "∀ (K : Type u_3) [inst : Field K],\n  AlgebraicCurve.KaehlerRankOne K (RatFunc K) → AlgebraicCurve.IsCurveOver K (RatFunc K)",
      "doc": "Pin row #235. ",
      "short": "isCurveOver_of_kaehlerRankOne",
      "signature_source": "theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :\n    IsCurveOver K (RatFunc K) :=",
      "body_source": "IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/P1/DXCoeff.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
