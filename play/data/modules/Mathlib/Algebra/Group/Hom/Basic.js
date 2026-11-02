window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Hom.Basic"] = {
  "module": "Mathlib.Algebra.Group.Hom.Basic",
  "cards": {
    "AddMonoidHom.add": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"AddZeroClass","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Add","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":238,"column":2},"end":{"line":238,"column":13}},
      "name": "AddMonoidHom.add",
      "module": "Mathlib.Algebra.Group.Hom.Basic",
      "kind": "def",
      "elaborated_type": "{M : Type u_2} → {N : Type u_3} → [inst : AddZeroClass M] → [inst_1 : AddCommMonoid N] → Add (M →+ N)",
      "doc": "Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,\n`f + g` is the additive monoid morphism sending `x` to `f x + g x`. ",
      "short": "add",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
