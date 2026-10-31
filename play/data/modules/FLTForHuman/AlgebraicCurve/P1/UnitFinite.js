window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.P1.UnitFinite"] = {
  "module": "FLTForHuman.AlgebraicCurve.P1.UnitFinite",
  "cards": {
    "AlgebraicCurve.kaehlerRankOne_ratFunc": {
      "refs": [{"where":"type","name":"AlgebraicCurve.KaehlerRankOne","module":"FLTForHuman.AlgebraicCurve.P1.DXCoeff","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"RatFunc","module":"Mathlib.FieldTheory.RatFunc.Defs","kind":"inductive"}],
      "range": {"start":{"line":61,"column":0},"end":{"line":63,"column":75}},
      "name": "AlgebraicCurve.kaehlerRankOne_ratFunc",
      "module": "FLTForHuman.AlgebraicCurve.P1.UnitFinite",
      "kind": "theorem",
      "elaborated_type": "∀ (K : Type u_1) [inst : Field K], AlgebraicCurve.KaehlerRankOne K (RatFunc K)",
      "doc": "",
      "short": "kaehlerRankOne_ratFunc",
      "signature_source": "theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=",
      "body_source": "⟨Module.Free.of_basis (kaehlerRatFuncBasis K),\n    (Module.finrank_eq_card_basis (kaehlerRatFuncBasis K)).trans (by simp)⟩",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/P1/UnitFinite.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
