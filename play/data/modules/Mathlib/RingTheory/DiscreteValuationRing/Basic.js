window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.DiscreteValuationRing.Basic"] = {
  "module": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
  "cards": {
    "IsDiscreteValuationRing": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":56,"column":0},"end":{"line":60,"column":35}},
      "name": "IsDiscreteValuationRing",
      "module": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → [inst : CommRing R] → [IsDomain R] → Prop",
      "doc": "An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which\nis not a field. ",
      "short": "IsDiscreteValuationRing",
      "signature_source": "class IsDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R] : Prop\n    extends IsPrincipalIdealRing R, IsLocalRing R where\n  not_a_field' : maximalIdeal R ≠ ⊥",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsDiscreteValuationRing.exists_irreducible": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Irreducible","module":"Mathlib.Algebra.Group.Irreducible.Defs","kind":"inductive"},{"where":"type","name":"IsDiscreteValuationRing","module":"Mathlib.RingTheory.DiscreteValuationRing.Basic","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":104,"column":0},"end":{"line":107,"column":68}},
      "name": "IsDiscreteValuationRing.exists_irreducible",
      "module": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ (R : Type u) [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], ∃ ϖ, Irreducible ϖ",
      "doc": "Uniformizers exist in a DVR. ",
      "short": "exists_irreducible",
      "signature_source": "theorem exists_irreducible : ∃ ϖ : R, Irreducible ϖ :=",
      "body_source": "by\n  simp_rw [irreducible_iff_uniformizer]\n  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
