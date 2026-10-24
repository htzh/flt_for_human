window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Subalgebra.Basic"] = {
  "module": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
  "cards": {
    "Subalgebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":28,"column":0},"end":{"line":34,"column":58}},
      "name": "Subalgebra",
      "module": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (A : Type v) → [inst : CommSemiring R] → [inst_1 : Semiring A] → [Algebra R A] → Type v",
      "doc": "A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. ",
      "short": "Subalgebra",
      "signature_source": "structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v\n    extends Subsemiring A where\n  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/\n  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier\n  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0\n  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Subalgebra.algebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"body","name":"Subalgebra.algebra'","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"def"}],
      "range": {"start":{"line":336,"column":0},"end":{"line":336,"column":44}},
      "name": "Subalgebra.algebra",
      "module": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {A : Type v} →\n    [inst : CommSemiring R] → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → (S : Subalgebra R A) → Algebra R ↥S",
      "doc": "",
      "short": "algebra",
      "signature_source": "instance algebra : Algebra R S :=",
      "body_source": "S.algebra'",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Subalgebra.algebra'": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom.codRestrict","module":"Mathlib.Algebra.Ring.Subsemiring.Basic","kind":"def"},{"where":"body","name":"SubmoduleClass.module'","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"}],
      "range": {"start":{"line":320,"column":0},"end":{"line":334,"column":61}},
      "name": "Subalgebra.algebra'",
      "module": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
      "kind": "def",
      "elaborated_type": "{R' : Type u'} →\n  {R : Type u} →\n    {A : Type v} →\n      [inst : CommSemiring R] →\n        [inst_1 : Semiring A] →\n          [inst_2 : Algebra R A] →\n            (S : Subalgebra R A) →\n              [inst_3 : CommSemiring R'] →\n                [inst_4 : SMul R' R] → [inst_5 : Algebra R' A] → [IsScalarTower R' R A] → Algebra R' ↥S",
      "doc": "More general form of `Subalgebra.algebra`.\n\nThis instance should have low priority since it is slow to fail:\nbefore failing, it will cause a search through all `SMul R' R` instances,\nwhich can quickly get expensive.\n",
      "short": "algebra'",
      "signature_source": "instance (priority := 500) algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A]\n    [IsScalarTower R' R A] :\n    Algebra R' S where\n  algebraMap := (algebraMap R' A).codRestrict S fun x => by\n    rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←\n      Algebra.algebraMap_eq_smul_one]\n    exact algebraMap_mem S _\n  commutes' := fun _ _ => Subtype.ext <| Algebra.commutes _ _\n  smul_def' := fun _ _ => Subtype.ext <| Algebra.smul_def _ _",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
