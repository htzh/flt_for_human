window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Torsion.Basic"] = {
  "module": "Mathlib.Algebra.Module.Torsion.Basic",
  "cards": {
    "Submodule.mem_torsionBy_iff": {
      "seed": true,
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.torsionBy","module":"Mathlib.Algebra.Module.Torsion.Basic","kind":"def"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":266,"column":0},"end":{"line":268,"column":9}},
      "name": "Submodule.mem_torsionBy_iff",
      "module": "Mathlib.Algebra.Module.Torsion.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (a : R)\n  (x : M), x ∈ Submodule.torsionBy R M a ↔ a • x = 0",
      "doc": "",
      "short": "mem_torsionBy_iff",
      "signature_source": "@[simp]\ntheorem mem_torsionBy_iff (x : M) : x ∈ torsionBy R M a ↔ a • x = 0 :=",
      "body_source": "Iff.rfl",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Torsion/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "Submodule.torsionBy": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":177,"column":0},"end":{"line":181,"column":37}},
      "name": "Submodule.torsionBy",
      "module": "Mathlib.Algebra.Module.Torsion.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  (M : Type u_2) →\n    [inst : CommSemiring R] → [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → R → Submodule R M",
      "doc": "The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that\n`a • x = 0`. ",
      "short": "torsionBy",
      "signature_source": "@[simps!]\ndef torsionBy (a : R) : Submodule R M :=",
      "body_source": "(DistribSMul.toLinearMap R M a).ker",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Torsion/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
