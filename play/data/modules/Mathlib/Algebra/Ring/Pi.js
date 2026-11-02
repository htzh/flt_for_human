window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.Pi"] = {
  "module": "Mathlib.Algebra.Ring.Pi",
  "cards": {
    "Pi.nonAssocSemiring": {
      "refs": [{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AddMonoidWithOne","module":"Mathlib.Data.Nat.Cast.Defs","kind":"inductive"},{"where":"body","name":"MulZeroOneClass","module":"Mathlib.Algebra.GroupWithZero.Defs","kind":"inductive"},{"where":"body","name":"NonUnitalNonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Pi.addMonoidWithOne","module":"Mathlib.Algebra.Ring.Pi","kind":"def"},{"where":"body","name":"Pi.mulZeroOneClass","module":"Mathlib.Algebra.GroupWithZero.Pi","kind":"def"},{"where":"body","name":"Pi.nonUnitalNonAssocSemiring","module":"Mathlib.Algebra.Ring.Pi","kind":"def"}],
      "range": {"start":{"line":61,"column":0},"end":{"line":62,"column":80}},
      "name": "Pi.nonAssocSemiring",
      "module": "Mathlib.Algebra.Ring.Pi",
      "kind": "def",
      "elaborated_type": "{I : Type u} → {f : I → Type v} → [(i : I) → NonAssocSemiring (f i)] → NonAssocSemiring ((i : I) → f i)",
      "doc": "",
      "short": "nonAssocSemiring",
      "signature_source": "instance nonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) :=",
      "body_source": "{ Pi.nonUnitalNonAssocSemiring, Pi.mulZeroOneClass, Pi.addMonoidWithOne with }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/Pi.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
