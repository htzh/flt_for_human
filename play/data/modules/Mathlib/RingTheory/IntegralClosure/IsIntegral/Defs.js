window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs"] = {
  "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs",
  "cards": {
    "IsIntegral": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom.IsIntegralElem","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":54,"column":35}},
      "name": "IsIntegral",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → {A : Type u_3} → [inst : CommRing R] → [inst_1 : Ring A] → [Algebra R A] → A → Prop",
      "doc": "An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,\nif it is a root of some monic polynomial `p : R[X]`.\nEquivalently, the element is integral over `R` with respect to the induced `algebraMap` ",
      "short": "IsIntegral",
      "signature_source": "def IsIntegral (x : A) : Prop :=",
      "body_source": "(algebraMap R A).IsIntegralElem x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.IsIntegralElem": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"body","name":"Polynomial.Monic","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"body","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"}],
      "range": {"start":{"line":37,"column":0},"end":{"line":40,"column":39}},
      "name": "RingHom.IsIntegralElem",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → {A : Type u_3} → [inst : CommRing R] → [inst_1 : Ring A] → (R →+* A) → A → Prop",
      "doc": "An element `x` of `A` is said to be integral over `R` with respect to `f`\nif it is a root of a monic polynomial `p : R[X]` evaluated under `f` ",
      "short": "IsIntegralElem",
      "signature_source": "def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=",
      "body_source": "∃ p : R[X], Monic p ∧ eval₂ f x p = 0",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
