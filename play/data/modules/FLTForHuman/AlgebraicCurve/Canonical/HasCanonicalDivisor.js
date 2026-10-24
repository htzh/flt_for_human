window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor"] = {
  "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
  "cards": {
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.DCoordGenerates","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.FiniteResidue","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.ValSubringKaehlerFinite","module":"FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"PerfectField","module":"Mathlib.FieldTheory.Perfect","kind":"inductive"}],
      "range": {"start":{"line":1064,"column":0},"end":{"line":1071,"column":72}},
      "name": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F] [PerfectField K]\n  [∀ (v : AlgebraicCurve.Place K F), v.FiniteResidue],\n  AlgebraicCurve.ValSubringKaehlerFinite K F → ∀ (v : AlgebraicCurve.Place K F), v.DCoordGenerates",
      "doc": "",
      "short": "dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "signature_source": "theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField\n    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]\n    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :\n    v.DCoordGenerates :=",
      "body_source": "haveI : ∀ v : Place K F,\n      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=\n    isSeparable_residueField_forall_of_perfectField\n  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable hfin v",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.DCoordGenerates","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.ValSubringKaehlerSpanTop","module":"FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":987,"column":0},"end":{"line":1008,"column":80}},
      "name": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F],\n  AlgebraicCurve.ValSubringKaehlerSpanTop K F → ∀ (v : AlgebraicCurve.Place K F), v.DCoordGenerates",
      "doc": "",
      "short": "dCoordGenerates_of_valSubringKaehlerSpanTop",
      "signature_source": "theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop\n    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :\n    v.DCoordGenerates :=",
      "body_source": "by\n  constructor\n  rw [eq_top_iff,\n    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization (R := K)\n      (S := v.toValuationSubring) (T := F) (nonZeroDivisors v.toValuationSubring),\n    Submodule.span_le]\n  rintro _ ⟨f, rfl⟩\n\n  have hDf : KaehlerDifferential.D K v.toValuationSubring f\n      ∈ (⊤ : Submodule v.toValuationSubring Ω[v.toValuationSubring⁄K]) := Submodule.mem_top\n  rw [← hspan v] at hDf\n  have hmap : (KaehlerDifferential.map K K v.toValuationSubring F ∘\n        KaehlerDifferential.D K v.toValuationSubring) f\n      ∈ Submodule.map (KaehlerDifferential.map K K v.toValuationSubring F)\n        (Submodule.span v.toValuationSubring _) :=\n    Submodule.mem_map_of_mem hDf\n  rw [Submodule.map_span, Set.image_singleton,\n    v.kaehlerMap_subring_D_uniformizer] at hmap\n\n  exact Submodule.span_le_restrictScalars v.toValuationSubring F {v.dCoord} hmap",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.ValSubringKaehlerFinite": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"Module.Finite","module":"Mathlib.RingTheory.Finiteness.Defs","kind":"inductive"},{"where":"body","name":"ValuationSubring","module":"Mathlib.RingTheory.Valuation.ValuationSubring","kind":"inductive"}],
      "range": {"start":{"line":291,"column":0},"end":{"line":292,"column":79}},
      "name": "AlgebraicCurve.ValSubringKaehlerFinite",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "def",
      "elaborated_type": "(K : Type u_1) → (F : Type u_2) → [inst : Field K] → [inst_1 : Field F] → [Algebra K F] → Prop",
      "doc": "",
      "short": "ValSubringKaehlerFinite",
      "signature_source": "def ValSubringKaehlerFinite : Prop :=",
      "body_source": "∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.ValSubringKaehlerSpanTop": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Place.uniformizerSubring'","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"def"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"body","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.span","module":"Mathlib.LinearAlgebra.Span.Defs","kind":"def"},{"where":"body","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"body","name":"ValuationSubring","module":"Mathlib.RingTheory.Valuation.ValuationSubring","kind":"inductive"}],
      "range": {"start":{"line":79,"column":0},"end":{"line":82,"column":86}},
      "name": "AlgebraicCurve.ValSubringKaehlerSpanTop",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "def",
      "elaborated_type": "(K : Type u_1) → (F : Type u_2) → [inst : Field K] → [inst_1 : Field F] → [Algebra K F] → Prop",
      "doc": "",
      "short": "ValSubringKaehlerSpanTop",
      "signature_source": "def ValSubringKaehlerSpanTop : Prop :=",
      "body_source": "∀ v : Place K F,\n    Submodule.span v.toValuationSubring\n      {KaehlerDifferential.D K v.toValuationSubring (Place.uniformizerSubring' v)} = ⊤",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": {
      "refs": [{"where":"type","name":"AlgebraicCurve.HasCanonicalDivisor","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.IsCurveOver","module":"FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.EssFiniteType","module":"Mathlib.RingTheory.EssentialFiniteness","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"PerfectField","module":"Mathlib.FieldTheory.Perfect","kind":"inductive"}],
      "range": {"start":{"line":1563,"column":0},"end":{"line":1567,"column":40}},
      "name": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F] [PerfectField K]\n  [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F], AlgebraicCurve.HasCanonicalDivisor",
      "doc": "",
      "short": "hasCanonicalDivisor_of_isCurveOver",
      "signature_source": "theorem hasCanonicalDivisor_of_isCurveOver\n    {K F : Type*} [Field K] [Field F] [Algebra K F]\n    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :\n    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=",
      "body_source": "hasCanonicalDivisor_of_isCurveOver_s12",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
