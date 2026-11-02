window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.Defs"] = {
  "module": "Mathlib.Algebra.Module.Submodule.Defs",
  "cards": {
    "Submodule": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":38,"column":0},"end":{"line":42,"column":44}},
      "name": "Submodule",
      "module": "Mathlib.Algebra.Module.Submodule.Defs",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (M : Type v) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type v",
      "doc": "A submodule of a module is one which is closed under vector operations.\nThis is a sufficient condition for the subset of vectors in the submodule\nto themselves form a module. ",
      "short": "Submodule",
      "signature_source": "structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v\n    extends AddSubmonoid M, SubMulAction R M",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.addCommGroup": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.addSubgroupClass","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"theorem"}],
      "range": {"start":{"line":366,"column":0},"end":{"line":366,"column":75}},
      "name": "Submodule.addCommGroup",
      "module": "Mathlib.Algebra.Module.Submodule.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {M : Type v} →\n    [inst : Ring R] → [inst_1 : AddCommGroup M] → {module_M : _root_.Module R M} → (p : Submodule R M) → AddCommGroup ↥p",
      "doc": "",
      "short": "addCommGroup",
      "signature_source": "instance addCommGroup : AddCommGroup p :=",
      "body_source": "AddSubgroupClass.toAddCommGroup p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.addCommMonoid": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.addSubmonoidClass","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"theorem"}],
      "range": {"start":{"line":296,"column":0},"end":{"line":296,"column":79}},
      "name": "Submodule.addCommMonoid",
      "module": "Mathlib.Algebra.Module.Submodule.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {M : Type v} →\n    [inst : Semiring R] →\n      [inst_1 : AddCommMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → AddCommMonoid ↥p",
      "doc": "",
      "short": "addCommMonoid",
      "signature_source": "instance addCommMonoid : AddCommMonoid p :=",
      "body_source": "AddSubmonoidClass.toAddCommMonoid p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.module": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.module'","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"}],
      "range": {"start":{"line":306,"column":0},"end":{"line":307,"column":11}},
      "name": "Submodule.module",
      "module": "Mathlib.Algebra.Module.Submodule.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {M : Type v} →\n    [inst : Semiring R] →\n      [inst_1 : AddCommMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → _root_.Module R ↥p",
      "doc": "",
      "short": "module",
      "signature_source": "instance module : Module R p :=",
      "body_source": "p.module'",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.module'": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Submodule.smul","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"}],
      "range": {"start":{"line":298,"column":0},"end":{"line":304,"column":54}},
      "name": "Submodule.module'",
      "module": "Mathlib.Algebra.Module.Submodule.Defs",
      "kind": "def",
      "elaborated_type": "{S : Type u'} →\n  {R : Type u} →\n    {M : Type v} →\n      [inst : Semiring R] →\n        [inst_1 : AddCommMonoid M] →\n          {module_M : _root_.Module R M} →\n            (p : Submodule R M) →\n              [inst_2 : Semiring S] →\n                [inst_3 : SMul S R] → [inst_4 : _root_.Module S M] → [IsScalarTower S R M] → _root_.Module S ↥p",
      "doc": "",
      "short": "module'",
      "signature_source": "instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :\n    Module S p :=",
      "body_source": "fast_instance%\n  { (show MulAction S p from p.toSubMulAction.mulAction') with\n    smul_zero := fun a => by ext; simp\n    zero_smul := fun a => by ext; simp\n    add_smul := fun a b x => by ext; simp [add_smul]\n    smul_add := fun a x y => by ext; simp [smul_add] }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
