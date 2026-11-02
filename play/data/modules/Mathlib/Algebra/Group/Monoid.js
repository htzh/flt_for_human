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
    },
    "npowRecAuto": {
      "refs": [{"where":"type","name":"Semigroup","module":"Mathlib.Algebra.Group.Semigroup","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"One","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"npowRec","module":"Init.Data.Zero","kind":"def"}],
      "range": {"start":{"line":318,"column":0},"end":{"line":328,"column":13}},
      "name": "npowRecAuto",
      "module": "Mathlib.Algebra.Group.Monoid",
      "kind": "abbrev",
      "elaborated_type": "{M : Type u_2} → [Semigroup M] → [One M] → ℕ → M → M",
      "doc": "An abbreviation for `npowRec` with an additional typeclass assumption on associativity\nso that we can use `@[csimp]` to replace it with an implementation by repeated squaring\nin compiled code.\n",
      "short": "npowRecAuto",
      "signature_source": "@[to_additive\n/-- An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity\nso that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled\ncode as an automatic parameter. -/]\nabbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=",
      "body_source": "npowRec k m",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Monoid.lean",
      "has_source": true,
      "has_refs": true
    },
    "pow_two": {
      "refs": [{"where":"type","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":432,"column":0},"end":{"line":433,"column":91}},
      "name": "pow_two",
      "module": "Mathlib.Algebra.Group.Monoid",
      "kind": "theorem",
      "elaborated_type": "∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a",
      "doc": "Note that most of the lemmas about powers of two refer to it as `sq`. ",
      "short": "pow_two",
      "signature_source": "@[to_additive two_nsmul] lemma pow_two (a : M) : a ^ 2 = a * a :=",
      "body_source": "by rw [pow_succ, pow_one]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Monoid.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
