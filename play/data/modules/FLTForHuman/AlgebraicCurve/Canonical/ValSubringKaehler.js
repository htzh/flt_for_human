window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler"] = {
  "module": "FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler",
  "cards": {
    "AlgebraicCurve.ValSubringKaehlerFinite": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"Module.Finite","module":"Mathlib.RingTheory.Finiteness.Defs","kind":"inductive"},{"where":"body","name":"ValuationSubring","module":"Mathlib.RingTheory.Valuation.ValuationSubring","kind":"inductive"}],
      "range": {"start":{"line":290,"column":0},"end":{"line":291,"column":79}},
      "name": "AlgebraicCurve.ValSubringKaehlerFinite",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler",
      "kind": "def",
      "elaborated_type": "(K : Type u_1) → (F : Type u_2) → [inst : Field K] → [inst_1 : Field F] → [Algebra K F] → Prop",
      "doc": "",
      "short": "ValSubringKaehlerFinite",
      "signature_source": "def ValSubringKaehlerFinite : Prop :=",
      "body_source": "∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/ValSubringKaehler.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.ValSubringKaehlerSpanTop": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Place.uniformizerSubring","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"def"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"body","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.span","module":"Mathlib.LinearAlgebra.Span.Defs","kind":"def"},{"where":"body","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"body","name":"ValuationSubring","module":"Mathlib.RingTheory.Valuation.ValuationSubring","kind":"inductive"}],
      "range": {"start":{"line":86,"column":0},"end":{"line":89,"column":85}},
      "name": "AlgebraicCurve.ValSubringKaehlerSpanTop",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler",
      "kind": "def",
      "elaborated_type": "(K : Type u_1) → (F : Type u_2) → [inst : Field K] → [inst_1 : Field F] → [Algebra K F] → Prop",
      "doc": "",
      "short": "ValSubringKaehlerSpanTop",
      "signature_source": "def ValSubringKaehlerSpanTop : Prop :=",
      "body_source": "∀ v : Place K F,\n    Submodule.span v.toValuationSubring\n      {KaehlerDifferential.D K v.toValuationSubring (Place.uniformizerSubring v)} = ⊤",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/ValSubringKaehler.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
