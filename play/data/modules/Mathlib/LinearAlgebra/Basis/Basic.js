window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Basis.Basic"] = {
  "module": "Mathlib.LinearAlgebra.Basis.Basic",
  "cards": {
    "Module.Basis.ne_zero": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"Nontrivial","module":"Mathlib.Basic.Nontrivial.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":93,"column":0},"end":{"line":94,"column":31}},
      "name": "Module.Basis.ne_zero",
      "module": "Mathlib.LinearAlgebra.Basis.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M]\n  [inst_2 : _root_.Module R M] (b : Module.Basis ι R M) [Nontrivial R] (i : ι), b i ≠ 0",
      "doc": "",
      "short": "ne_zero",
      "signature_source": "protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=",
      "body_source": "b.linearIndependent.ne_zero i",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Module.Basis.singleton": {
      "refs": [{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Unique","module":"Mathlib.Basic.Unique","kind":"inductive"},{"where":"body","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"Finsupp.module","module":"Mathlib.Data.Finsupp.SMul","kind":"def"},{"where":"body","name":"Finsupp.single","module":"Mathlib.Data.Finsupp.Single","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"body","name":"Inhabited.default","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":247,"column":0},"end":{"line":255,"column":39}},
      "name": "Module.Basis.singleton",
      "module": "Mathlib.LinearAlgebra.Basis.Basic",
      "kind": "def",
      "elaborated_type": "(ι : Type u_6) → (R : Type u_7) → [Unique ι] → [inst : Semiring R] → Module.Basis ι R R",
      "doc": "`Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. ",
      "short": "singleton",
      "signature_source": "protected def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=",
      "body_source": "ofRepr\n    { toFun := fun x => Finsupp.single default x\n      invFun := fun f => f default\n      left_inv := fun x => by simp\n      right_inv := fun f => Finsupp.unique_ext (by simp)\n      map_add' := fun x y => by simp\n      map_smul' := fun c x => by simp }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Module.Basis.span_eq": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Set.range","module":"Mathlib.Data.Set.Operations","kind":"def"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.span","module":"Mathlib.LinearAlgebra.Span.Defs","kind":"def"},{"where":"type","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"}],
      "range": {"start":{"line":71,"column":0},"end":{"line":73,"column":40}},
      "name": "Module.Basis.span_eq",
      "module": "Mathlib.LinearAlgebra.Basis.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M]\n  [inst_2 : _root_.Module R M] (b : Module.Basis ι R M), Submodule.span R (Set.range ⇑b) = ⊤",
      "doc": "",
      "short": "span_eq",
      "signature_source": "@[simp]\nprotected theorem span_eq : span R (range b) = ⊤ :=",
      "body_source": "eq_top_iff.mpr fun x _ => b.mem_span x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
