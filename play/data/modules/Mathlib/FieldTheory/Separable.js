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
    }
  }
};
