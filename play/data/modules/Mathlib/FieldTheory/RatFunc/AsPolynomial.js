window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.RatFunc.AsPolynomial"] = {
  "module": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
  "cards": {
    "RatFunc.X": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RatFunc","module":"Mathlib.FieldTheory.RatFunc.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"body","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
      "range": {"start":{"line":70,"column":0},"end":{"line":72,"column":35}},
      "name": "RatFunc.X",
      "module": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
      "kind": "def",
      "elaborated_type": "{K : Type u} → [inst : CommRing K] → [IsDomain K] → RatFunc K",
      "doc": "`RatFunc.X` is the polynomial variable (aka indeterminate). ",
      "short": "X",
      "signature_source": "def X : K⟮X⟯ :=",
      "body_source": "algebraMap K[X] K⟮X⟯ Polynomial.X",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "RatFunc.algEquivOfTranscendental": {
      "refs": [{"where":"type","name":"AlgEquiv","module":"Mathlib.Algebra.Algebra.Equiv","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"IntermediateField.algebra'","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"def"},{"where":"type","name":"IsScalarTower.left","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"RatFunc","module":"Mathlib.FieldTheory.RatFunc.Defs","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Transcendental","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"},{"where":"body","name":"Algebra.adjoin","module":"Mathlib.Algebra.Algebra.Subalgebra.Lattice","kind":"def"},{"where":"body","name":"IsFractionRing.algEquivOfAlgEquiv","module":"Mathlib.RingTheory.Localization.FractionRing","kind":"def"},{"where":"body","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"body","name":"Polynomial.algEquivOfTranscendental","module":"Mathlib.RingTheory.Algebraic.Basic","kind":"def"},{"where":"body","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"body","name":"Subalgebra.algebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"def"}],
      "range": {"start":{"line":223,"column":0},"end":{"line":226,"column":79}},
      "name": "RatFunc.algEquivOfTranscendental",
      "module": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
      "kind": "def",
      "elaborated_type": "{K : Type u_1} →\n  {L : Type u_2} →\n    [inst : Field K] →\n      [inst_1 : Field L] → [inst_2 : Algebra K L] → (f : L) → Transcendental K f → RatFunc K ≃ₐ[K] ↥K⟮f⟯",
      "doc": "Given a transcendental `f : L`, the `K`-algebra isomorphism between `RatFunc K` and `L` given\nby sending `X` to `f`. ",
      "short": "algEquivOfTranscendental",
      "signature_source": "noncomputable def algEquivOfTranscendental : RatFunc K ≃ₐ[K] K⟮f⟯ :=",
      "body_source": "IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivOfTranscendental K f h)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "RatFunc.algEquivOfTranscendental_X": {
      "refs": [{"where":"type","name":"AlgEquiv","module":"Mathlib.Algebra.Algebra.Equiv","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"IntermediateField.algebra'","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"def"},{"where":"type","name":"IsScalarTower.left","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"RatFunc","module":"Mathlib.FieldTheory.RatFunc.Defs","kind":"inductive"},{"where":"type","name":"RatFunc.X","module":"Mathlib.FieldTheory.RatFunc.AsPolynomial","kind":"def"},{"where":"type","name":"RatFunc.algEquivOfTranscendental","module":"Mathlib.FieldTheory.RatFunc.AsPolynomial","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Transcendental","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"}],
      "range": {"start":{"line":235,"column":0},"end":{"line":238,"column":23}},
      "name": "RatFunc.algEquivOfTranscendental_X",
      "module": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (f : L)\n  (h : Transcendental K f), ↑((RatFunc.algEquivOfTranscendental f h) RatFunc.X) = f",
      "doc": "",
      "short": "algEquivOfTranscendental_X",
      "signature_source": "@[simp]\ntheorem algEquivOfTranscendental_X :\n    algEquivOfTranscendental f h (X : RatFunc K) = f :=",
      "body_source": "by\n  simp [← algebraMap_X]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
