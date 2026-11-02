window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Subgroup.Ker"] = {
  "module": "Mathlib.Algebra.Group.Subgroup.Ker",
  "cards": {
    "AddMonoidHom.ker": {
      "refs": [{"where":"type","name":"AddGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"AddSubgroup","module":"Mathlib.Algebra.Group.Subgroup.Defs","kind":"inductive"},{"where":"type","name":"AddZeroClass","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"body","name":"AddMonoidHom.mker","module":"Mathlib.Algebra.Group.Submonoid.Operations","kind":"def"},{"where":"body","name":"AddSubmonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"}],
      "range": {"start":{"line":235,"column":2},"end":{"line":237,"column":28}},
      "name": "AddMonoidHom.ker",
      "module": "Mathlib.Algebra.Group.Subgroup.Ker",
      "kind": "def",
      "elaborated_type": "{G : Type u_1} → [inst : AddGroup G] → {M : Type u_6} → [inst_1 : AddZeroClass M] → (G →+ M) → AddSubgroup G",
      "doc": "The additive kernel of an `AddMonoid` homomorphism is the `AddSubgroup` of elements\nsuch that `f x = 0` ",
      "short": "ker",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
