window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus"] = {
  "module": "FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus",
  "cards": {
    "AlgebraicCurve.Place.min_ord_le_ord_add": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.ord","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Min.min","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":60,"column":0},"end":{"line":78,"column":9}},
      "name": "AlgebraicCurve.Place.min_ord_le_ord_add",
      "module": "FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F]\n  (v : AlgebraicCurve.Place K F) {f g : F}, f + g ≠ 0 → min (v.ord f) (v.ord g) ≤ v.ord (f + g)",
      "doc": "Pin `Place.min_ord_le_ord_add`\n(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1070`). ",
      "short": "min_ord_le_ord_add",
      "signature_source": "theorem min_ord_le_ord_add {f g : F} (hfg : f + g ≠ 0) :\n    min (v.ord f) (v.ord g) ≤ v.ord (f + g) :=",
      "body_source": "by\n  rcases eq_or_ne f 0 with rfl | hf\n  · simp\n  rcases eq_or_ne g 0 with rfl | hg\n  · simp\n  have h1 : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=\n    Valuation.map_add _ f g\n  have hje : v.adicValuation (f + g) ≠ 0 := v.adicValuation_ne_zero hfg\n  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>\n    rw [hmax] at h1\n  · have h2 := (WithZero.log_le_log hje (v.adicValuation_ne_zero hf)).mpr h1\n    simp only [ord]\n    omega\n  · have h2 := (WithZero.log_le_log hje (v.adicValuation_ne_zero hg)).mpr h1\n    simp only [ord]\n    omega",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Defs/PlaceCalculus.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
