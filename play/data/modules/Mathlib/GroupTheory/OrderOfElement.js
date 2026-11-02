window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.GroupTheory.OrderOfElement"] = {
  "module": "Mathlib.GroupTheory.OrderOfElement",
  "cards": {
    "addOrderOf": {
      "refs": [{"where":"type","name":"AddMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Function.minimalPeriod","module":"Mathlib.Dynamics.PeriodicPts.Defs","kind":"def"}],
      "range": {"start":{"line":179,"column":2},"end":{"line":181,"column":99}},
      "name": "addOrderOf",
      "module": "Mathlib.GroupTheory.OrderOfElement",
      "kind": "def",
      "elaborated_type": "{G : Type u_1} → [AddMonoid G] → G → ℕ",
      "doc": "`addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it\nexists. Otherwise, i.e. if `a` is of infinite order, then `addOrderOf a` is `0` by convention. ",
      "short": "addOrderOf",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    },
    "addOrderOf_dvd_of_nsmul_eq_zero": {
      "refs": [{"where":"type","name":"AddMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"addOrderOf","module":"Mathlib.GroupTheory.OrderOfElement","kind":"def"},{"where":"type","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":272,"column":2},"end":{"line":272,"column":13}},
      "name": "addOrderOf_dvd_of_nsmul_eq_zero",
      "module": "Mathlib.GroupTheory.OrderOfElement",
      "kind": "theorem",
      "elaborated_type": "∀ {G : Type u_1} [inst : AddMonoid G] {x : G} {n : ℕ}, n • x = 0 → addOrderOf x ∣ n",
      "doc": "",
      "short": "addOrderOf_dvd_of_nsmul_eq_zero",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
