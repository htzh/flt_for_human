window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.GroupTheory.Perm.Cycle.Type"] = {
  "module": "Mathlib.GroupTheory.Perm.Cycle.Type",
  "cards": {
    "exists_prime_addOrderOf_dvd_card'": {
      "seed": true,
      "refs": [{"where":"type","name":"AddGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"type","name":"Fact","module":"Mathlib.Basic.Logic.Basic","kind":"inductive"},{"where":"type","name":"Finite","module":"Mathlib.Basic.Finite.Defs","kind":"inductive"},{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat.card","module":"Mathlib.SetTheory.Cardinal.Finite","kind":"def"},{"where":"type","name":"addOrderOf","module":"Mathlib.GroupTheory.OrderOfElement","kind":"def"},{"where":"type","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":539,"column":2},"end":{"line":540,"column":84}},
      "name": "exists_prime_addOrderOf_dvd_card'",
      "module": "Mathlib.GroupTheory.Perm.Cycle.Type",
      "kind": "theorem",
      "elaborated_type": "∀ {G : Type u_3} [inst : AddGroup G] [Finite G] (p : ℕ) [hp : Fact (Nat.Prime p)],\n  p ∣ Nat.card G → ∃ x, addOrderOf x = p",
      "doc": "For every prime `p` dividing the order of a finite additive group `G` there exists\nan element of order `p` in `G`. This is the additive version of Cauchy's theorem. ",
      "short": "exists_prime_addOrderOf_dvd_card'",
      "signature_source": "@[to_additive /-- For every prime `p` dividing the order of a finite additive group `G` there exists\nan element of order `p` in `G`. This is the additive version of Cauchy's theorem. -/]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Type.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
