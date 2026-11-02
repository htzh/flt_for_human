window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.IntegralClosure.Algebra.Defs"] = {
  "module": "Mathlib.RingTheory.IntegralClosure.Algebra.Defs",
  "cards": {
    "Algebra.IsIntegral": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":32,"column":0},"end":{"line":34,"column":38}},
      "name": "Algebra.IsIntegral",
      "module": "Mathlib.RingTheory.IntegralClosure.Algebra.Defs",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_1) → (A : Type u_2) → [inst : CommRing R] → [inst_1 : Ring A] → [Algebra R A] → Prop",
      "doc": "An algebra is integral if every element of the extension is integral over the base ring. ",
      "short": "IsIntegral",
      "signature_source": "@[mk_iff] protected class Algebra.IsIntegral : Prop where\n  isIntegral : ∀ x : A, IsIntegral R x",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
