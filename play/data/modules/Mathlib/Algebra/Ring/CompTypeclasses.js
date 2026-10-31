window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.CompTypeclasses"] = {
  "module": "Mathlib.Algebra.Ring.CompTypeclasses",
  "cards": {
    "RingHomInvPair.ids": {
      "refs": [{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":103,"column":0},"end":{"line":104,"column":12}},
      "name": "RingHomInvPair.ids",
      "module": "Mathlib.Algebra.Ring.CompTypeclasses",
      "kind": "theorem",
      "elaborated_type": "∀ {R₁ : Type u_1} [inst : Semiring R₁], RingHomInvPair (RingHom.id R₁) (RingHom.id R₁)",
      "doc": "",
      "short": "ids",
      "signature_source": "instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=",
      "body_source": "⟨rfl, rfl⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/CompTypeclasses.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHomSurjective.ids": {
      "refs": [{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomSurjective","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":173,"column":0},"end":{"line":174,"column":17}},
      "name": "RingHomSurjective.ids",
      "module": "Mathlib.Algebra.Ring.CompTypeclasses",
      "kind": "theorem",
      "elaborated_type": "∀ {R₁ : Type u_1} [inst : Semiring R₁], RingHomSurjective (RingHom.id R₁)",
      "doc": "",
      "short": "ids",
      "signature_source": "instance ids : RingHomSurjective (RingHom.id R₁) :=",
      "body_source": "⟨is_surjective⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/CompTypeclasses.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
