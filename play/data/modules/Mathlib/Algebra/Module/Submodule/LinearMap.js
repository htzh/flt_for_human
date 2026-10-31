window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.LinearMap"] = {
  "module": "Mathlib.Algebra.Module.Submodule.LinearMap",
  "cards": {
    "Submodule.subtype": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"}],
      "range": {"start":{"line":81,"column":0},"end":{"line":85,"column":22}},
      "name": "Submodule.subtype",
      "module": "Mathlib.Algebra.Module.Submodule.LinearMap",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {M : Type v} →\n    [inst : Semiring R] → [inst_1 : AddCommMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → ↥p →ₗ[R] M",
      "doc": "Embedding of a submodule `p` to the ambient space `M`. ",
      "short": "subtype",
      "signature_source": "protected def subtype : p →ₗ[R] M where\n  toFun := Subtype.val\n  map_add' := by simp\n  map_smul' := by simp",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/LinearMap.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
