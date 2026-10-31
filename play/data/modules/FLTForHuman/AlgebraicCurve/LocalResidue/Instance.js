window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.LocalResidue.Instance"] = {
  "module": "FLTForHuman.AlgebraicCurve.LocalResidue.Instance",
  "cards": {
    "AlgebraicCurve.HasSeparableResidue.of_perfectField": {
      "refs": [{"where":"type","name":"AlgebraicCurve.HasSeparableResidue","module":"FLTForHuman.AlgebraicCurve.Defs.LocalResidue","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.FiniteResidue","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"PerfectField","module":"Mathlib.FieldTheory.Perfect","kind":"inductive"}],
      "range": {"start":{"line":78,"column":0},"end":{"line":80,"column":37}},
      "name": "AlgebraicCurve.HasSeparableResidue.of_perfectField",
      "module": "FLTForHuman.AlgebraicCurve.LocalResidue.Instance",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F] [PerfectField K]\n  [∀ (v : AlgebraicCurve.Place K F), v.FiniteResidue], AlgebraicCurve.HasSeparableResidue K F",
      "doc": "",
      "short": "of_perfectField",
      "signature_source": "instance HasSeparableResidue.of_perfectField [PerfectField K]\n    [∀ v : Place K F, v.FiniteResidue] : HasSeparableResidue K F :=",
      "body_source": "hasSeparableResidue_of_perfectField",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/LocalResidue/Instance.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
