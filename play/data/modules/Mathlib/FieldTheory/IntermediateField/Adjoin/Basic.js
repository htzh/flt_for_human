window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.IntermediateField.Adjoin.Basic"] = {
  "module": "Mathlib.FieldTheory.IntermediateField.Adjoin.Basic",
  "cards": {
    "IntermediateField.adjoin.finrank": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"IntermediateField.module'","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"def"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"IsScalarTower.left","module":"Mathlib.Algebra.Group.Action.Defs","kind":"theorem"},{"where":"type","name":"Module.finrank","module":"Mathlib.LinearAlgebra.Dimension.Finrank","kind":"def"},{"where":"type","name":"Polynomial.natDegree","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"minpoly","module":"Mathlib.FieldTheory.Minpoly.Basic","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":486,"column":0},"end":{"line":492,"column":5}},
      "name": "IntermediateField.adjoin.finrank",
      "module": "Mathlib.FieldTheory.IntermediateField.Adjoin.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u} [inst : Field K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},\n  IsIntegral K x → Module.finrank K ↥K⟮x⟯ = (minpoly K x).natDegree",
      "doc": "If `x` is an algebraic element of field `K`, then its minimal polynomial has degree\n`[K(x) : K]`. ",
      "short": "finrank",
      "signature_source": "@[stacks 09GN]\ntheorem adjoin.finrank {x : L} (hx : IsIntegral K x) :\n    Module.finrank K K⟮x⟯ = (minpoly K x).natDegree :=",
      "body_source": "by\n  rw [PowerBasis.finrank (adjoin.powerBasis hx :)]\n  rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "IntermediateField.mem_adjoin_simple_iff": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.aeval","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":61,"column":0},"end":{"line":64,"column":43}},
      "name": "IntermediateField.mem_adjoin_simple_iff",
      "module": "Mathlib.FieldTheory.IntermediateField.Adjoin.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] {α : E} (x : E),\n  x ∈ F⟮α⟯ ↔ ∃ r s, x = (Polynomial.aeval α) r / (Polynomial.aeval α) s",
      "doc": "",
      "short": "mem_adjoin_simple_iff",
      "signature_source": "theorem mem_adjoin_simple_iff {α : E} (x : E) :\n    x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s :=",
      "body_source": "by\n  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,\n    AlgHom.mem_range, exists_exists_eq_and]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
