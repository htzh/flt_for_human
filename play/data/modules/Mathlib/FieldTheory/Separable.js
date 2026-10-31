window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.Separable"] = {
  "module": "Mathlib.FieldTheory.Separable",
  "cards": {
    "Algebra.IsSeparable": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":541,"column":0},"end":{"line":550,"column":41}},
      "name": "Algebra.IsSeparable",
      "module": "Mathlib.FieldTheory.Separable",
      "kind": "inductive",
      "elaborated_type": "(F : Type u_1) → (K : Type u_3) → [inst : CommRing F] → [inst_1 : Ring K] → [Algebra F K] → Prop",
      "doc": "Typeclass for separable field extension: `K` is a separable field extension of `F` iff\nthe minimal polynomial of every `x : K` is separable. This implies that `K/F` is an algebraic\nextension, because the minimal polynomial of a non-integral element is `0`, which is not\nseparable.\n\nWe define this for general (commutative) rings and only assume `F` and `K` are fields if this\nis needed for a proof. ",
      "short": "IsSeparable",
      "signature_source": "@[mk_iff isSeparable_def, stacks 09H1 \"third part\"]\nprotected class Algebra.IsSeparable : Prop where\n  isSeparable' : ∀ x : K, IsSeparable F x",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Separable.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsSeparable": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.Separable","module":"Mathlib.FieldTheory.Separable","kind":"def"},{"where":"body","name":"minpoly","module":"Mathlib.FieldTheory.Minpoly.Basic","kind":"def"}],
      "range": {"start":{"line":533,"column":0},"end":{"line":539,"column":68}},
      "name": "IsSeparable",
      "module": "Mathlib.FieldTheory.Separable",
      "kind": "def",
      "elaborated_type": "(F : Type u_1) → {K : Type u_3} → [inst : CommRing F] → [inst_1 : Ring K] → [Algebra F K] → K → Prop",
      "doc": "An element `x` of an algebra `K` over a commutative ring `F` is said to be *separable*, if its\nminimal polynomial over `K` is separable. Note that the minimal polynomial of any element not\nintegral over `F` is defined to be `0`, which is not a separable polynomial.\n",
      "short": "IsSeparable",
      "signature_source": "@[stacks 09H1 \"second part\"]\ndef IsSeparable (x : K) : Prop :=",
      "body_source": "Polynomial.Separable (minpoly F x)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Separable.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.Separable": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"body","name":"IsCoprime","module":"Mathlib.RingTheory.Coprime.Basic","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.derivative","module":"Mathlib.Algebra.Polynomial.Derivative","kind":"def"},{"where":"body","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":42,"column":0},"end":{"line":45,"column":28}},
      "name": "Polynomial.Separable",
      "module": "Mathlib.FieldTheory.Separable",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : CommSemiring R] → Polynomial R → Prop",
      "doc": "A polynomial is separable iff it is coprime with its derivative. ",
      "short": "Separable",
      "signature_source": "@[stacks 09H1 \"first part\"]\ndef Separable (f : R[X]) : Prop :=",
      "body_source": "IsCoprime f (derivative f)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Separable.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
