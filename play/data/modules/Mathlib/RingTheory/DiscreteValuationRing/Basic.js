window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.DiscreteValuationRing.Basic"] = {
  "module": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
  "cards": {
    "Irreducible.maximalIdeal_eq": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.span","module":"Mathlib.RingTheory.Ideal.Span","kind":"abbrev"},{"where":"type","name":"Irreducible","module":"Mathlib.Algebra.Group.Irreducible.Defs","kind":"inductive"},{"where":"type","name":"IsDiscreteValuationRing","module":"Mathlib.RingTheory.DiscreteValuationRing.Basic","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing.maximalIdeal","module":"Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":98,"column":0},"end":{"line":100,"column":38}},
      "name": "Irreducible.maximalIdeal_eq",
      "module": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ϖ : R},\n  Irreducible ϖ → IsLocalRing.maximalIdeal R = Ideal.span {ϖ}",
      "doc": "",
      "short": "maximalIdeal_eq",
      "signature_source": "theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :\n    maximalIdeal R = Ideal.span {ϖ} :=",
      "body_source": "(irreducible_iff_uniformizer _).mp h",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
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
    },
    "IsDiscreteValuationRing.irreducible_iff_uniformizer": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.span","module":"Mathlib.RingTheory.Ideal.Span","kind":"abbrev"},{"where":"type","name":"Irreducible","module":"Mathlib.Algebra.Group.Irreducible.Defs","kind":"inductive"},{"where":"type","name":"IsDiscreteValuationRing","module":"Mathlib.RingTheory.DiscreteValuationRing.Basic","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing.maximalIdeal","module":"Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs","kind":"def"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":91,"column":0},"end":{"line":96,"column":70}},
      "name": "IsDiscreteValuationRing.irreducible_iff_uniformizer",
      "module": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] (ϖ : R),\n  Irreducible ϖ ↔ IsLocalRing.maximalIdeal R = Ideal.span {ϖ}",
      "doc": "An element of a DVR is irreducible iff it is a uniformizer, that is, generates the\nmaximal ideal of `R`. ",
      "short": "irreducible_iff_uniformizer",
      "signature_source": "theorem irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ} :=",
      "body_source": "⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,\n    fun h => irreducible_of_span_eq_maximalIdeal ϖ\n      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
