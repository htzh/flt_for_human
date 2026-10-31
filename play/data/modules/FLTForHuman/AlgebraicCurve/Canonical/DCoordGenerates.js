window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates"] = {
  "module": "FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates",
  "cards": {
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.DCoordGenerates","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.FiniteResidue","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.ValSubringKaehlerFinite","module":"FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"PerfectField","module":"Mathlib.FieldTheory.Perfect","kind":"inductive"}],
      "range": {"start":{"line":128,"column":0},"end":{"line":135,"column":72}},
      "name": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F] [PerfectField K]\n  [∀ (v : AlgebraicCurve.Place K F), v.FiniteResidue],\n  AlgebraicCurve.ValSubringKaehlerFinite K F → ∀ (v : AlgebraicCurve.Place K F), v.DCoordGenerates",
      "doc": "",
      "short": "dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "signature_source": "theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField\n    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]\n    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :\n    v.DCoordGenerates :=",
      "body_source": "haveI : ∀ v : Place K F,\n      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=\n    isSeparable_residueField_forall_of_perfectField\n  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable hfin v",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/DCoordGenerates.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": {
      "refs": [{"where":"type","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.Place.DCoordGenerates","module":"FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","kind":"inductive"},{"where":"type","name":"AlgebraicCurve.ValSubringKaehlerSpanTop","module":"FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":51,"column":0},"end":{"line":72,"column":80}},
      "name": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
      "module": "FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {F : Type u_2} [inst : Field K] [inst_1 : Field F] [inst_2 : Algebra K F],\n  AlgebraicCurve.ValSubringKaehlerSpanTop K F → ∀ (v : AlgebraicCurve.Place K F), v.DCoordGenerates",
      "doc": "",
      "short": "dCoordGenerates_of_valSubringKaehlerSpanTop",
      "signature_source": "theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop\n    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :\n    v.DCoordGenerates :=",
      "body_source": "by\n  constructor\n  rw [eq_top_iff,\n    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization (R := K)\n      (S := v.toValuationSubring) (T := F) (nonZeroDivisors v.toValuationSubring),\n    Submodule.span_le]\n  rintro _ ⟨f, rfl⟩\n\n  have hDf : KaehlerDifferential.D K v.toValuationSubring f\n      ∈ (⊤ : Submodule v.toValuationSubring Ω[v.toValuationSubring⁄K]) := Submodule.mem_top\n  rw [← hspan v] at hDf\n  have hmap : (KaehlerDifferential.map K K v.toValuationSubring F ∘\n        KaehlerDifferential.D K v.toValuationSubring) f\n      ∈ Submodule.map (KaehlerDifferential.map K K v.toValuationSubring F)\n        (Submodule.span v.toValuationSubring _) :=\n    Submodule.mem_map_of_mem hDf\n  rw [Submodule.map_span, Set.image_singleton,\n    v.kaehlerMap_subring_D_uniformizer] at hmap\n\n  exact Submodule.span_le_restrictScalars v.toValuationSubring F {v.dCoord} hmap",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Canonical/DCoordGenerates.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
