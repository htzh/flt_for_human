window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Monoid"] = {
  "module": "Mathlib.Algebra.Group.Monoid",
  "cards": {
    "AddCommMonoid": {
      "refs": [],
      "range": {"start":{"line":524,"column":0},"end":{"line":525,"column":71}},
      "name": "AddCommMonoid",
      "module": "Mathlib.Algebra.Group.Monoid",
      "kind": "inductive",
      "elaborated_type": "Type u_2 → Type u_2",
      "doc": "An additive commutative monoid is an additive monoid with commutative `(+)`. ",
      "short": "AddCommMonoid",
      "signature_source": "class AddCommMonoid (M : Type*) extends AddMonoid M, AddCommSemigroup M",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Monoid.lean",
      "has_source": true,
      "has_refs": false
    },
    "AddMonoid": {
      "refs": [],
      "range": {"start":{"line":378,"column":0},"end":{"line":383,"column":82}},
      "name": "AddMonoid",
      "module": "Mathlib.Algebra.Group.Monoid",
      "kind": "inductive",
      "elaborated_type": "Type u_2 → Type u_2",
      "doc": "An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. ",
      "short": "AddMonoid",
      "signature_source": "class AddMonoid (M : Type*) extends Zero M, Add M, AddSemigroup M, AddZeroClass M, NSMul M where\n  /-- Multiplication by `(0 : ℕ)` gives `0`. -/\n  protected nsmul_zero (x : M) : 0 • x = 0 := by intros; rfl\n  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/\n  protected nsmul_succ (n : ℕ) (x : M) : (n + 1) • x = n • x + x := by intros; rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Monoid.lean",
      "has_source": true,
      "has_refs": false
    },
    "Monoid": {
      "refs": [],
      "range": {"start":{"line":388,"column":0},"end":{"line":395,"column":81}},
      "name": "Monoid",
      "module": "Mathlib.Algebra.Group.Monoid",
      "kind": "inductive",
      "elaborated_type": "Type u_2 → Type u_2",
      "doc": "A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. ",
      "short": "Monoid",
      "signature_source": "@[to_additive]\nclass Monoid (M : Type*) extends One M, Mul M, Semigroup M, MulOneClass M, NPow M where\n  npow := npowRecAuto\n  /-- Raising to the power `(0 : ℕ)` gives `1`. -/\n  protected npow_zero (x : M) : x ^ 0 = 1 := by intros; rfl\n  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/\n  protected npow_succ (n : ℕ) (x : M) : x ^ (n + 1) = x ^ n * x := by intros; rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Monoid.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
