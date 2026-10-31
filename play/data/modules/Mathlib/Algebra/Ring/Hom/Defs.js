window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.Hom.Defs"] = {
  "module": "Mathlib.Algebra.Ring.Hom.Defs",
  "cards": {
    "RingHom": {
      "refs": [{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
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
      "has_refs": true
    },
    "RingHom.comp": {
      "refs": [{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"NonUnitalRingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"NonUnitalRingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":542,"column":0},"end":{"line":545,"column":97}},
      "name": "RingHom.comp",
      "module": "Mathlib.Algebra.Ring.Hom.Defs",
      "kind": "def",
      "elaborated_type": "{α : Type u_2} →\n  {β : Type u_3} →\n    {γ : Type u_4} →\n      {x : NonAssocSemiring α} →\n        {x_1 : NonAssocSemiring β} → {x_2 : NonAssocSemiring γ} → (β →+* γ) → (α →+* β) → α →+* γ",
      "doc": "Composition of ring homomorphisms is a ring homomorphism. ",
      "short": "comp",
      "signature_source": "@[instance_reducible]\ndef comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=",
      "body_source": "{ g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun x := g (f x), map_one' := by simp }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.id": {
      "refs": [{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
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
      "has_refs": true
    },
    "RingHomClass": {
      "refs": [{"where":"type","name":"FunLike","module":"Mathlib.Data.FunLike.Basic","kind":"abbrev"},{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"outParam","module":"Init.Prelude","kind":"def"}],
      "range": {"start":{"line":321,"column":0},"end":{"line":329,"column":85}},
      "name": "RingHomClass",
      "module": "Mathlib.Algebra.Ring.Hom.Defs",
      "kind": "inductive",
      "elaborated_type": "(F : Type u_5) →\n  (α : outParam (Type u_6)) →\n    (β : outParam (Type u_7)) → [NonAssocSemiring α] → [NonAssocSemiring β] → [FunLike F α β] → Prop",
      "doc": "`RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.\nYou should extend this class when you extend `RingHom`.\n\nThis extends from both `MonoidHomClass` and `MonoidWithZeroHomClass` in\norder to put the fields in a sensible order, even though\n`MonoidWithZeroHomClass` already extends `MonoidHomClass`. ",
      "short": "RingHomClass",
      "signature_source": "class RingHomClass (F : Type*) (α β : outParam Type*)\n    [NonAssocSemiring α] [NonAssocSemiring β] [FunLike F α β] : Prop\n  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
