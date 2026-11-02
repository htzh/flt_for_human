window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.GroupTheory.OreLocalization.OreSet"] = {
  "module": "Mathlib.GroupTheory.OreLocalization.OreSet",
  "cards": {
    "OreLocalization.oreSetComm": {
      "refs": [{"where":"type","name":"CommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"OreLocalization.OreSet","module":"Mathlib.GroupTheory.OreLocalization.OreSet","kind":"inductive"},{"where":"type","name":"Submonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"}],
      "range": {"start":{"line":118,"column":0},"end":{"line":125,"column":32}},
      "name": "OreLocalization.oreSetComm",
      "module": "Mathlib.GroupTheory.OreLocalization.OreSet",
      "kind": "def",
      "elaborated_type": "{R : Type u_2} → [inst : CommMonoid R] → (S : Submonoid R) → OreLocalization.OreSet S",
      "doc": "Every submonoid of a commutative monoid is an Ore set. ",
      "short": "oreSetComm",
      "signature_source": "@[to_additive AddOreLocalization.addOreSetComm\n/-- Every submonoid of an additive commutative monoid is an Ore set. -/]\ninstance (priority := 100) oreSetComm {R} [CommMonoid R] (S : Submonoid R) : OreSet S where\n  ore_right_cancel m n s h := ⟨s, by rw [mul_comm (s : R) n, mul_comm (s : R) m, h]⟩\n  oreNum r _ := r\n  oreDenom _ s := s\n  ore_eq r s := by rw [mul_comm]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/OreSet.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
