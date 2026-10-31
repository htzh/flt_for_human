window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Hom"] = {
  "module": "Mathlib.Algebra.Algebra.Hom",
  "cards": {
    "AlgHom": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":29,"column":0},"end":{"line":32,"column":66}},
      "name": "AlgHom",
      "module": "Mathlib.Algebra.Algebra.Hom",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) →\n  (A : Type v) →\n    (B : Type w) →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] → [Algebra R B] → Type (max v w)",
      "doc": "Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`. ",
      "short": "AlgHom",
      "signature_source": "structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends RingHom A B where\n  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgHom.funLike": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"FunLike","module":"Mathlib.Data.FunLike.Basic","kind":"abbrev"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":88,"column":0},"end":{"line":94,"column":9}},
      "name": "AlgHom.funLike",
      "module": "Mathlib.Algebra.Algebra.Hom",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {A : Type v} →\n    {B : Type w} →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] →\n          [inst_2 : Semiring B] → [inst_3 : Algebra R A] → [inst_4 : Algebra R B] → FunLike (A →ₐ[R] B) A B",
      "doc": "",
      "short": "funLike",
      "signature_source": "@[macro_inline]\ninstance funLike : FunLike (A →ₐ[R] B) A B where\n  coe f := f.toFun\n  coe_injective f g h := by\n    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩\n    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩\n    congr",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean",
      "has_source": true,
      "has_refs": true
    },
    "AlgHom.toRingHom": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":30,"column":0},"end":{"line":32,"column":66}},
      "name": "AlgHom.toRingHom",
      "module": "Mathlib.Algebra.Algebra.Hom",
      "kind": "abbrev",
      "elaborated_type": "{R : Type u} →\n  {A : Type v} →\n    {B : Type w} →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] →\n          [inst_2 : Semiring B] → [inst_3 : Algebra R A] → [inst_4 : Algebra R B] → (A →ₐ[R] B) → A →+* B",
      "doc": "Reinterpret an `AlgHom` as a `RingHom` ",
      "short": "toRingHom",
      "signature_source": "structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends RingHom A B where\n  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
