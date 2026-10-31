window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.LocalRing.ResidueField.Basic"] = {
  "module": "Mathlib.RingTheory.LocalRing.ResidueField.Basic",
  "cards": {
    "IsLocalRing.ResidueField.algebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing","module":"Mathlib.RingTheory.LocalRing.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing.ResidueField","module":"Mathlib.RingTheory.LocalRing.ResidueField.Defs","kind":"def"},{"where":"type","name":"IsLocalRing.ResidueField.field","module":"Mathlib.RingTheory.LocalRing.ResidueField.Defs","kind":"def"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":52,"column":39}},
      "name": "IsLocalRing.ResidueField.algebra",
      "module": "Mathlib.RingTheory.LocalRing.ResidueField.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  [inst : CommRing R] →\n    [inst_1 : IsLocalRing R] →\n      {R₀ : Type u_4} → [inst_2 : CommRing R₀] → [Algebra R₀ R] → Algebra R₀ (IsLocalRing.ResidueField R)",
      "doc": "",
      "short": "algebra",
      "signature_source": "instance ResidueField.algebra {R₀} [CommRing R₀] [Algebra R₀ R] :\n    Algebra R₀ (ResidueField R) :=",
      "body_source": "inferInstanceAs <| Algebra R₀ (_ ⧸ _)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
