window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.HahnSeries.Multiplication"] = {
  "module": "Mathlib.RingTheory.HahnSeries.Multiplication",
  "cards": {
    "HahnSeries.embDomainRingHom": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"HahnSeries","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"inductive"},{"where":"type","name":"IsOrderedCancelAddMonoid","module":"Mathlib.Algebra.Order.Monoid.Defs","kind":"inductive"},{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"PartialOrder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Function.Injective","module":"Init.Data.Function","kind":"def"},{"where":"body","name":"HahnSeries.embDomain","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"def"}],
      "range": {"start":{"line":886,"column":0},"end":{"line":894,"column":29}},
      "name": "HahnSeries.embDomainRingHom",
      "module": "Mathlib.RingTheory.HahnSeries.Multiplication",
      "kind": "def",
      "elaborated_type": "{Γ : Type u_1} →\n  {R : Type u_3} →\n    [inst : AddCommMonoid Γ] →\n      [inst_1 : PartialOrder Γ] →\n        [inst_2 : IsOrderedCancelAddMonoid Γ] →\n          {Γ' : Type u_6} →\n            [inst_3 : AddCommMonoid Γ'] →\n              [inst_4 : PartialOrder Γ'] →\n                [inst_5 : IsOrderedCancelAddMonoid Γ'] →\n                  [inst_6 : NonAssocSemiring R] →\n                    (f : Γ →+ Γ') →\n                      Function.Injective ⇑f → (∀ (g g' : Γ), f g ≤ f g' ↔ g ≤ g') → HahnSeries Γ R →+* HahnSeries Γ' R",
      "doc": "Extending the domain of Hahn series is a ring homomorphism. ",
      "short": "embDomainRingHom",
      "signature_source": "@[simps]\ndef embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)\n    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : R⟦Γ⟧ →+* R⟦Γ'⟧ where\n  toFun := embDomain ⟨⟨f, hfi⟩, hf _ _⟩\n  map_one' := embDomain_one _ f.map_zero\n  map_mul' := embDomain_mul _ f.map_add\n  map_zero' := embDomain_zero\n  map_add' := embDomain_add _",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
