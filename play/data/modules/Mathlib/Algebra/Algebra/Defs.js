window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Defs"] = {
  "module": "Mathlib.Algebra.Algebra.Defs",
  "cards": {
    "Algebra": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":91,"column":0},"end":{"line":99,"column":45}},
      "name": "Algebra",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (A : Type v) → [CommSemiring R] → [Semiring A] → Type (max u v)",
      "doc": "An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.\n\nSee the implementation notes in this file for discussion of the details of this definition.\n",
      "short": "Algebra",
      "signature_source": "class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where\n  /-- Embedding `R →+* A` given by `Algebra` structure. -/\n  algebraMap (R) (A) : R →+* A\n  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r\n  smul_def' : ∀ r x, r • x = algebraMap r * x",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Algebra.algebraMap": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":97,"column":2},"end":{"line":97,"column":12}},
      "name": "Algebra.algebraMap",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "abbrev",
      "elaborated_type": "(R : Type u) → (A : Type v) → {inst : CommSemiring R} → {inst_1 : Semiring A} → [self : Algebra R A] → R →+* A",
      "doc": "Embedding `R →+* A` given by `Algebra` structure. ",
      "short": "algebraMap",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    },
    "Algebra.id": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"SMul","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":384,"column":0},"end":{"line":390,"column":32}},
      "name": "Algebra.id",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u) → [inst : CommSemiring R] → Algebra R R",
      "doc": "The identity map inducing an `Algebra` structure. ",
      "short": "id",
      "signature_source": "instance (priority := 1100) id : Algebra R R where\n  -- We override `toFun` and `toSMul` because `RingHom.id` is not reducible and cannot\n  -- be made so without a significant performance hit.\n  -- see library note [reducible non-instances].\n  toSMul := instSMulOfMul\n  __ := (RingHom.id R).toAlgebra",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Algebra.linearMap": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
      "range": {"start":{"line":367,"column":0},"end":{"line":371,"column":76}},
      "name": "Algebra.linearMap",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u) → (A : Type w) → [inst : CommSemiring R] → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → R →ₗ[R] A",
      "doc": "The canonical ring homomorphism `algebraMap R A : R →+* A` for any `R`-algebra `A`,\npackaged as an `R`-linear map.\n",
      "short": "linearMap",
      "signature_source": "protected def linearMap : R →ₗ[R] A :=",
      "body_source": "{ algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsScalarTower.right": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":307,"column":0},"end":{"line":309,"column":80}},
      "name": "IsScalarTower.right",
      "module": "Mathlib.Algebra.Algebra.Defs",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A",
      "doc": "This has high priority because it is almost always the right instance when it applies. ",
      "short": "right",
      "signature_source": "instance (priority := high) _root_.IsScalarTower.right : IsScalarTower R A A :=",
      "body_source": "⟨fun x y z => by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
