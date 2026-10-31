window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Defs.PushPull"] = {
  "module": "FLTForHuman.AlgebraicCurve.Defs.PushPull",
  "cards": {
    "AlgebraicCurve.Place.mem_iff_ord_nonneg": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.ord","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"ValuationSubring","module":"Mathlib.RingTheory.Valuation.ValuationSubring","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":82,"column":0},"end":{"line":85,"column":47}},
      "name": "AlgebraicCurve.Place.mem_iff_ord_nonneg",
      "module": "FLTForHuman.AlgebraicCurve.Defs.PushPull",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F]\n  (v : AlgebraicCurve.Place K F) {f : F}, f ≠ 0 → (f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f)",
      "doc": "",
      "short": "mem_iff_ord_nonneg",
      "signature_source": "theorem mem_iff_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)\n    {f : F} (hf : f ≠ 0) :\n    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=",
      "body_source": "⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Defs/PushPull.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
