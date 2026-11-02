window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.AlgebraicIndependent.Basic"] = {
  "module": "Mathlib.RingTheory.AlgebraicIndependent.Basic",
  "cards": {
    "Algebra.trdeg": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Cardinal","module":"Mathlib.SetTheory.Cardinal.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AlgebraicIndepOn","module":"Mathlib.RingTheory.AlgebraicIndependent.Defs","kind":"abbrev"},{"where":"body","name":"Cardinal.mk","module":"Mathlib.SetTheory.Cardinal.Defs","kind":"def"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Set.Elem","module":"Mathlib.Data.Set.CoeSort","kind":"def"},{"where":"body","name":"iSup","module":"Mathlib.Order.SetNotation","kind":"def"}],
      "range": {"start":{"line":43,"column":0},"end":{"line":46,"column":72}},
      "name": "Algebra.trdeg",
      "module": "Mathlib.RingTheory.AlgebraicIndependent.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u_2) → (A : Type v) → [inst : CommRing R] → [inst_1 : CommRing A] → [Algebra R A] → Cardinal.{v}",
      "doc": "The transcendence degree of a commutative algebra `A` over a commutative ring `R` is\ndefined to be the maximal cardinality of an `R`-algebraically independent set in `A`. ",
      "short": "trdeg",
      "signature_source": "@[stacks 030G] def Algebra.trdeg : Cardinal.{v} :=",
      "body_source": "⨆ ι : { s : Set A // AlgebraicIndepOn R _root_.id s }, Cardinal.mk ι.1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
