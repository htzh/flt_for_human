window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.FiniteDimensional.Basic"] = {
  "module": "Mathlib.LinearAlgebra.FiniteDimensional.Basic",
  "cards": {
    "exists_smul_eq_of_finrank_eq_one": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"DivisionRing","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.finrank","module":"Mathlib.LinearAlgebra.Dimension.Finrank","kind":"def"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":560,"column":0},"end":{"line":570,"column":33}},
      "name": "exists_smul_eq_of_finrank_eq_one",
      "module": "Mathlib.LinearAlgebra.FiniteDimensional.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],\n  Module.finrank K V = 1 → ∀ {x : V}, x ≠ 0 → ∀ (y : V), ∃ c, c • x = y",
      "doc": "In a one-dimensional space, any vector is a multiple of any nonzero vector ",
      "short": "exists_smul_eq_of_finrank_eq_one",
      "signature_source": "lemma exists_smul_eq_of_finrank_eq_one\n    (h : finrank K V = 1) {x : V} (hx : x ≠ 0) (y : V) :\n    ∃ (c : K), c • x = y :=",
      "body_source": "by\n  have : Submodule.span K {x} = ⊤ := by\n    have : FiniteDimensional K V := .of_finrank_eq_succ h\n    apply eq_top_of_finrank_eq\n    rw [h]\n    exact finrank_span_singleton hx\n  have : y ∈ Submodule.span K {x} := by rw [this]; exact mem_top\n  exact mem_span_singleton.1 this",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
