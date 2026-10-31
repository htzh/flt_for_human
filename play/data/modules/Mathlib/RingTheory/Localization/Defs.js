window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Localization.Defs"] = {
  "module": "Mathlib.RingTheory.Localization.Defs",
  "cards": {
    "IsLocalization": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"body","name":"IsLocalization'","module":"Mathlib.RingTheory.Localization.Defs","kind":"inductive"}],
      "range": {"start":{"line":102,"column":0},"end":{"line":104,"column":41}},
      "name": "IsLocalization",
      "module": "Mathlib.RingTheory.Localization.Defs",
      "kind": "abbrev",
      "elaborated_type": "{R : Type u_4} →\n  [inst : CommSemiring R] → Submonoid R → (S : Type u_5) → [inst_1 : CommSemiring S] → [Algebra R S] → Prop",
      "doc": "The typeclass `IsLocalization (M : Submonoid R) S` where `S` is an `R`-algebra\nexpresses that `S` is isomorphic to the localization of `R` at `M`. ",
      "short": "IsLocalization",
      "signature_source": "abbrev IsLocalization :=",
      "body_source": "@IsLocalization'",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
