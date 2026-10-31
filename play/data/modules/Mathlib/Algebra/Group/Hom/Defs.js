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
    }
  }
};
