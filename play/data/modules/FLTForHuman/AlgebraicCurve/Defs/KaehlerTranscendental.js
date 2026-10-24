window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental"] = {
  "module": "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
  "cards": {
    "KaehlerDifferential.D_ne_zero_of_transcendental": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.IsSeparable","module":"Mathlib.FieldTheory.Separable","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Transcendental","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":88,"column":0},"end":{"line":92,"column":31}},
      "name": "KaehlerDifferential.D_ne_zero_of_transcendental",
      "module": "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
      "kind": "theorem",
      "elaborated_type": "∀ (K : Type u_1) [inst : Field K] {F : Type u_2} [inst_1 : Field F] [inst_2 : Algebra K F] (x : F),\n  Transcendental K x → ∀ [Algebra.IsSeparable (↥K⟮x⟯) F], (KaehlerDifferential.D K F) x ≠ 0",
      "doc": "",
      "short": "D_ne_zero_of_transcendental",
      "signature_source": "theorem D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)\n    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :\n    KaehlerDifferential.D K F x ≠ 0 :=",
      "body_source": "by\n  obtain ⟨b, hb⟩ := FF2.exists_basis hx\n  simpa [hb] using b.ne_zero ()",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Defs/KaehlerTranscendental.lean",
      "has_source": true,
      "has_refs": true
    },
    "KaehlerDifferential.span_D_eq_top_of_transcendental": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.IsSeparable","module":"Mathlib.FieldTheory.Separable","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Algebra.to_smulCommClass","module":"Mathlib.Algebra.Algebra.Basic","kind":"theorem"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"KaehlerDifferential","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"KaehlerDifferential.D","module":"Mathlib.RingTheory.Kaehler.Basic","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.span","module":"Mathlib.LinearAlgebra.Span.Defs","kind":"def"},{"where":"type","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"type","name":"Transcendental","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"},{"where":"type","name":"smulCommClass_self","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"}],
      "range": {"start":{"line":81,"column":0},"end":{"line":86,"column":99}},
      "name": "KaehlerDifferential.span_D_eq_top_of_transcendental",
      "module": "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
      "kind": "theorem",
      "elaborated_type": "∀ (K : Type u_1) [inst : Field K] {F : Type u_2} [inst_1 : Field F] [inst_2 : Algebra K F] (x : F),\n  Transcendental K x → ∀ [Algebra.IsSeparable (↥K⟮x⟯) F], F ∙ (KaehlerDifferential.D K F) x = ⊤",
      "doc": "",
      "short": "span_D_eq_top_of_transcendental",
      "signature_source": "theorem span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)\n    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :\n    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ :=",
      "body_source": "by\n  obtain ⟨b, hb⟩ := FF2.exists_basis hx\n  have h := b.span_eq\n  rwa [show Set.range b = {KaehlerDifferential.D K F x} by ext ω; simp [Set.range_unique, hb]] at h",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Defs/KaehlerTranscendental.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
