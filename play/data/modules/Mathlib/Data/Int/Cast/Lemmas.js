window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Int.Cast.Lemmas"] = {
  "module": "Mathlib.Data.Int.Cast.Lemmas",
  "cards": {
    "Int.castRingHom": {
      "refs": [{"where":"type","name":"NonAssocRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Int.cast_mul","module":"Mathlib.Algebra.Ring.Int.Defs","kind":"theorem"},{"where":"body","name":"Int.cast","module":"Init.Data.Int.Basic","kind":"def"}],
      "range": {"start":{"line":83,"column":0},"end":{"line":90,"column":22}},
      "name": "Int.castRingHom",
      "module": "Mathlib.Data.Int.Cast.Lemmas",
      "kind": "def",
      "elaborated_type": "(α : Type u_2) → [inst : NonAssocRing α] → ℤ →+* α",
      "doc": "`coe : ℤ → α` as a `RingHom`. ",
      "short": "castRingHom",
      "signature_source": "@[instance_reducible]\ndef castRingHom : ℤ →+* α where\n  toFun := Int.cast\n  map_zero' := cast_zero\n  map_add' := cast_add\n  map_one' := cast_one\n  map_mul' := cast_mul",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Int/Cast/Lemmas.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.ext_int": {
      "refs": [{"where":"type","name":"NonAssocSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":348,"column":0},"end":{"line":349,"column":86}},
      "name": "RingHom.ext_int",
      "module": "Mathlib.Data.Int.Cast.Lemmas",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_4} [inst : NonAssocSemiring R] (f g : ℤ →+* R), f = g",
      "doc": "",
      "short": "ext_int",
      "signature_source": "theorem ext_int {R : Type*} [NonAssocSemiring R] (f g : ℤ →+* R) : f = g :=",
      "body_source": "coe_addMonoidHom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Int/Cast/Lemmas.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
