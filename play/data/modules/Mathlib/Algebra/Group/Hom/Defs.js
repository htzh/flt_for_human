window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Hom.Defs"] = {
  "module": "Mathlib.Algebra.Group.Hom.Defs",
  "cards": {
    "AddMonoidHom": {
      "refs": [{"where":"type","name":"AddZero","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"}],
      "range": {"start":{"line":135,"column":0},"end":{"line":145,"column":33}},
      "name": "AddMonoidHom",
      "module": "Mathlib.Algebra.Group.Hom.Defs",
      "kind": "inductive",
      "elaborated_type": "(M : Type u_10) → (N : Type u_11) → [AddZero M] → [AddZero N] → Type (max u_10 u_11)",
      "doc": "`M →+ N` is the type of functions `M → N` that preserve the `AddZero` structure.\n\n`AddMonoidHom` is also used for group homomorphisms.\n\nWhen possible, instead of parametrizing results over `(f : M →+ N)`,\nyou should parametrize over `(F : Type*) [AddMonoidHomClass F M N] (f : F)`.\n\nWhen you extend this structure, make sure to extend `AddMonoidHomClass`.\n\n\n[Wikidata Q868169](https://www.wikidata.org/wiki/Q868169)",
      "short": "AddMonoidHom",
      "signature_source": "structure AddMonoidHom (M : Type*) (N : Type*) [AddZero M] [AddZero N]\n  extends ZeroHom M N, AddHom M N",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "ZeroHom": {
      "refs": [{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":78,"column":0},"end":{"line":89,"column":35}},
      "name": "ZeroHom",
      "module": "Mathlib.Algebra.Group.Hom.Defs",
      "kind": "inductive",
      "elaborated_type": "(M : Type u_10) → (N : Type u_11) → [Zero M] → [Zero N] → Type (max u_10 u_11)",
      "doc": "`ZeroHom M N` is the type of functions `M → N` that preserve zero.\n\nWhen possible, instead of parametrizing results over `(f : ZeroHom M N)`,\nyou should parametrize over `(F : Type*) [ZeroHomClass F M N] (f : F)`.\n\nWhen you extend this structure, make sure to also extend `ZeroHomClass`.\n",
      "short": "ZeroHom",
      "signature_source": "structure ZeroHom (M : Type*) (N : Type*) [Zero M] [Zero N] where\n  /-- The underlying function -/\n  protected toFun : M → N\n  /-- The proposition that the function preserves 0 -/\n  protected map_zero' : toFun 0 = 0",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "ZeroHom.funLike": {
      "refs": [{"where":"type","name":"FunLike","module":"Mathlib.Data.FunLike.Basic","kind":"abbrev"},{"where":"type","name":"ZeroHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":191,"column":2},"end":{"line":191,"column":36}},
      "name": "ZeroHom.funLike",
      "module": "Mathlib.Algebra.Group.Hom.Defs",
      "kind": "def",
      "elaborated_type": "{M : Type u_4} → {N : Type u_5} → [inst : Zero M] → [inst_1 : Zero N] → FunLike (ZeroHom M N) M N",
      "doc": "",
      "short": "funLike",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
