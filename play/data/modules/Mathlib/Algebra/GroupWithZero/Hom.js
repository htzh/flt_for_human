window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.GroupWithZero.Hom"] = {
  "module": "Mathlib.Algebra.GroupWithZero.Hom",
  "cards": {
    "MonoidWithZeroHom": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":64,"column":0},"end":{"line":74,"column":36}},
      "name": "MonoidWithZeroHom",
      "module": "Mathlib.Algebra.GroupWithZero.Hom",
      "kind": "inductive",
      "elaborated_type": "(α : Type u_7) → (β : Type u_8) → [MulZeroOneClass α] → [MulZeroOneClass β] → Type (max u_7 u_8)",
      "doc": "`α →*₀ β` is the type of functions `α → β` that preserve\nthe `MonoidWithZero` structure.\n\n`MonoidWithZeroHom` is also used for group homomorphisms.\n\nWhen possible, instead of parametrizing results over `(f : α →*₀ β)`,\nyou should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`.\n\nWhen you extend this structure, make sure to extend `MonoidWithZeroHomClass`. ",
      "short": "MonoidWithZeroHom",
      "signature_source": "structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]\n  extends ZeroHom α β, MonoidHom α β",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "MonoidWithZeroHom.funLike": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":89,"column":0},"end":{"line":92,"column":83}},
      "name": "MonoidWithZeroHom.funLike",
      "module": "Mathlib.Algebra.GroupWithZero.Hom",
      "kind": "def",
      "elaborated_type": "{α : Type u_2} → {β : Type u_3} → [inst : MulZeroOneClass α] → [inst_1 : MulZeroOneClass β] → FunLike (α →*₀ β) α β",
      "doc": "",
      "short": "funLike",
      "signature_source": "@[macro_inline]\ninstance funLike : FunLike (α →*₀ β) α β where\n  coe f := f.toFun\n  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
