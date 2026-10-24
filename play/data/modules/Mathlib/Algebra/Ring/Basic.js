window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.Basic"] = {
  "module": "Mathlib.Algebra.Ring.Basic",
  "cards": {
    "AddMonoidHom.mulRight": {
      "refs": [{"where":"type","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"NonUnitalNonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":60,"column":0},"end":{"line":64,"column":31}},
      "name": "AddMonoidHom.mulRight",
      "module": "Mathlib.Algebra.Ring.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : NonUnitalNonAssocSemiring R] → R → R →+ R",
      "doc": "Right multiplication by an element of a (semi)ring is an `AddMonoidHom` ",
      "short": "mulRight",
      "signature_source": "def mulRight (r : R) : R →+ R where\n  toFun a := a * r\n  map_zero' := zero_mul r\n  map_add' _ _ := add_mul _ _ r",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
