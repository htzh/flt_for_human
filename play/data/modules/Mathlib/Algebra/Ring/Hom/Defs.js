window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.Hom.Defs"] = {
  "module": "Mathlib.Algebra.Ring.Hom.Defs",
  "cards": {
    "RingHom": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":292,"column":0},"end":{"line":298,"column":35}},
      "name": "RingHom",
      "module": "Mathlib.Algebra.Ring.Hom.Defs",
      "kind": "inductive",
      "elaborated_type": "(α : Type u_5) → (β : Type u_6) → [NonAssocSemiring α] → [NonAssocSemiring β] → Type (max u_5 u_6)",
      "doc": "Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.\n\nThis extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a\nsensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`. ",
      "short": "RingHom",
      "signature_source": "@[wikidata Q1194212]\nstructure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends\n  α →* β, α →+ β, α →ₙ+* β, α →*₀ β",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "RingHom.id": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":513,"column":0},"end":{"line":520,"column":21}},
      "name": "RingHom.id",
      "module": "Mathlib.Algebra.Ring.Hom.Defs",
      "kind": "def",
      "elaborated_type": "(α : Type u_5) → [inst : NonAssocSemiring α] → α →+* α",
      "doc": "The identity ring homomorphism from a semiring to itself. ",
      "short": "id",
      "signature_source": "@[instance_reducible]\ndef id (α : Type*) [NonAssocSemiring α] : α →+* α where\n  toFun x := x\n  map_zero' := rfl\n  map_one' := rfl\n  map_add' _ _ := rfl\n  map_mul' _ _ := rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
