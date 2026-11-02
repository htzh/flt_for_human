window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.IntegralClosure.Algebra.Basic"] = {
  "module": "Mathlib.RingTheory.IntegralClosure.Algebra.Basic",
  "cards": {
    "IsIntegral.of_mem_of_fg": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"OrderEmbedding","module":"Mathlib.Order.Hom.Basic","kind":"abbrev"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.FG","module":"Mathlib.RingTheory.Finiteness.Defs","kind":"def"}],
      "range": {"start":{"line":79,"column":0},"end":{"line":84,"column":86}},
      "name": "IsIntegral.of_mem_of_fg",
      "module": "Mathlib.RingTheory.IntegralClosure.Algebra.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {B : Type u_3} [inst : CommRing R] [inst_1 : Ring B] [inst_2 : Algebra R B] (S : Subalgebra R B),\n  (Subalgebra.toSubmodule S).FG → ∀ x ∈ S, IsIntegral R x",
      "doc": "If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-module,\nthen all elements of `S` are integral over `R`. ",
      "short": "of_mem_of_fg",
      "signature_source": "theorem IsIntegral.of_mem_of_fg (S : Subalgebra R B)\n    (HS : S.toSubmodule.FG) (x : B) (hx : x ∈ S) : IsIntegral R x :=",
      "body_source": "have : Module.Finite R S := .of_fg HS\n  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
