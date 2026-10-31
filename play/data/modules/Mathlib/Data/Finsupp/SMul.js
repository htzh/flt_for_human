window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Finsupp.SMul"] = {
  "module": "Mathlib.Data.Finsupp.SMul",
  "cards": {
    "Finsupp.module": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"DistribMulAction","module":"Mathlib.Algebra.GroupWithZero.Action.Defs","kind":"inductive"},{"where":"body","name":"Finsupp.distribMulAction","module":"Mathlib.Data.Finsupp.SMul","kind":"def"}],
      "range": {"start":{"line":129,"column":0},"end":{"line":132,"column":58}},
      "name": "Finsupp.module",
      "module": "Mathlib.Data.Finsupp.SMul",
      "kind": "def",
      "elaborated_type": "(α : Type u_1) →\n  (M : Type u_3) →\n    {R : Type u_6} → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → _root_.Module R (α →₀ M)",
      "doc": "",
      "short": "module",
      "signature_source": "instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α →₀ M) :=",
      "body_source": "{ toDistribMulAction := Finsupp.distribMulAction α M\n    zero_smul := fun _ => ext fun _ => zero_smul _ _\n    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Finsupp/SMul.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
