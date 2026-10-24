window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.LocalRing.ResidueField.Defs"] = {
  "module": "Mathlib.RingTheory.LocalRing.ResidueField.Defs",
  "cards": {
    "IsLocalRing.ResidueField": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing","module":"Mathlib.RingTheory.LocalRing.Defs","kind":"inductive"},{"where":"body","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"body","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"body","name":"IsLocalRing.maximalIdeal","module":"Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs","kind":"def"}],
      "range": {"start":{"line":28,"column":0},"end":{"line":32,"column":28}},
      "name": "IsLocalRing.ResidueField",
      "module": "Mathlib.RingTheory.LocalRing.ResidueField.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → [inst : CommRing R] → [IsLocalRing R] → Type u_1",
      "doc": "The residue field of a local ring is the quotient of the ring by its maximal ideal. ",
      "short": "ResidueField",
      "signature_source": "@[wikidata Q7315530]\ndef ResidueField :=",
      "body_source": "R ⧸ maximalIdeal R\nderiving CommRing, Inhabited",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsLocalRing.ResidueField.field": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing","module":"Mathlib.RingTheory.LocalRing.Defs","kind":"inductive"},{"where":"type","name":"IsLocalRing.ResidueField","module":"Mathlib.RingTheory.LocalRing.ResidueField.Defs","kind":"def"},{"where":"body","name":"DivInvMonoid.div'","module":"Mathlib.Algebra.Group.DivInvMonoid","kind":"def"},{"where":"body","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"body","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"body","name":"Ideal.Quotient.groupWithZero","module":"Mathlib.RingTheory.Ideal.Quotient.Basic","kind":"abbrev"},{"where":"body","name":"Ideal.Quotient.one","module":"Mathlib.RingTheory.Ideal.Quotient.Defs","kind":"def"},{"where":"body","name":"IsLocalRing.maximalIdeal","module":"Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs","kind":"def"},{"where":"body","name":"NNRat","module":"Mathlib.Data.Rat.Init","kind":"def"},{"where":"body","name":"NNRat.cast","module":"Mathlib.Data.Rat.Init","kind":"def"},{"where":"body","name":"NNRat.castRec","module":"Mathlib.Algebra.Field.Defs","kind":"def"},{"where":"body","name":"Rat.castRec","module":"Mathlib.Algebra.Field.Defs","kind":"def"},{"where":"body","name":"zpowRec","module":"Mathlib.Algebra.Group.DivInvMonoid","kind":"def"},{"where":"body","name":"Classical.choose","module":"Init.Classical","kind":"def"},{"where":"body","name":"Classical.propDecidable","module":"Init.Classical","kind":"def"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"body","name":"Rat.cast","module":"Batteries.Classes.RatCast","kind":"def"},{"where":"body","name":"npowRec","module":"Init.Data.Zero","kind":"def"}],
      "range": {"start":{"line":34,"column":0},"end":{"line":35,"column":54}},
      "name": "IsLocalRing.ResidueField.field",
      "module": "Mathlib.RingTheory.LocalRing.ResidueField.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → [inst : CommRing R] → [inst_1 : IsLocalRing R] → Field (IsLocalRing.ResidueField R)",
      "doc": "",
      "short": "field",
      "signature_source": "noncomputable instance ResidueField.field : Field (ResidueField R) :=",
      "body_source": "fast_instance% Ideal.Quotient.field (maximalIdeal R)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
