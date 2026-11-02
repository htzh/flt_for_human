window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Ideal.Quotient.Defs"] = {
  "module": "Mathlib.RingTheory.Ideal.Quotient.Defs",
  "cards": {
    "Ideal.Quotient.mk": {
      "refs": [{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.IsTwoSided","module":"Mathlib.RingTheory.Ideal.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"Submodule.Quotient.mk","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"}],
      "range": {"start":{"line":82,"column":0},"end":{"line":88,"column":21}},
      "name": "Ideal.Quotient.mk",
      "module": "Mathlib.RingTheory.Ideal.Quotient.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Ring R] → (I : Ideal R) → [inst_1 : I.IsTwoSided] → R →+* R ⧸ I",
      "doc": "The ring homomorphism from a ring `R` to a quotient ring `R/I`. ",
      "short": "mk",
      "signature_source": "def mk : R →+* R ⧸ I where\n  toFun a := Submodule.Quotient.mk a\n  map_zero' := rfl\n  map_one' := rfl\n  map_mul' _ _ := rfl\n  map_add' _ _ := rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
