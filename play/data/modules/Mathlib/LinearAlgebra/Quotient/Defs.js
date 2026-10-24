window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Quotient.Defs"] = {
  "module": "Mathlib.LinearAlgebra.Quotient.Defs",
  "cards": {
    "Submodule.Quotient.addCommMonoid": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.hasQuotient","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"Submodule.Quotient.addMonoid","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"}],
      "range": {"start":{"line":134,"column":0},"end":{"line":135,"column":56}},
      "name": "Submodule.Quotient.addCommMonoid",
      "module": "Mathlib.LinearAlgebra.Quotient.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : Ring R] →\n      [inst_1 : AddCommGroup M] → [inst_2 : _root_.Module R M] → (p : Submodule R M) → AddCommMonoid (M ⧸ p)",
      "doc": "",
      "short": "addCommMonoid",
      "signature_source": "instance addCommMonoid : AddCommMonoid (M ⧸ p) :=",
      "body_source": "inferInstanceAs <| AddCommMonoid (M ⧸ p.toAddSubgroup)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.Quotient.module": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.Quotient.addCommMonoid","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"type","name":"Submodule.hasQuotient","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"Submodule.Quotient.module'","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"}],
      "range": {"start":{"line":198,"column":0},"end":{"line":199,"column":20}},
      "name": "Submodule.Quotient.module",
      "module": "Mathlib.LinearAlgebra.Quotient.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : Ring R] →\n      [inst_1 : AddCommGroup M] → [inst_2 : _root_.Module R M] → (P : Submodule R M) → _root_.Module R (M ⧸ P)",
      "doc": "",
      "short": "module",
      "signature_source": "instance module (P : Submodule R M) : Module R (M ⧸ P) :=",
      "body_source": "Quotient.module' P",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.hasQuotient": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"HasQuotient","module":"Mathlib.Algebra.Quotient","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.quotientRel","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"Quotient","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":54,"column":0},"end":{"line":56,"column":37}},
      "name": "Submodule.hasQuotient",
      "module": "Mathlib.LinearAlgebra.Quotient.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_2} →\n    [inst : Ring R] → [inst_1 : AddCommGroup M] → [inst_2 : _root_.Module R M] → HasQuotient M (Submodule R M)",
      "doc": "The quotient of a module `M` by a submodule `p ⊆ M`. ",
      "short": "hasQuotient",
      "signature_source": "instance hasQuotient : HasQuotient M (Submodule R M) :=",
      "body_source": "⟨fun p => Quotient (quotientRel p)⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
