window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.GroupWithZero.NonZeroDivisors"] = {
  "module": "Mathlib.Algebra.GroupWithZero.NonZeroDivisors",
  "cards": {
    "nonZeroDivisors": {
      "refs": [{"where":"type","name":"MonoidWithZero","module":"Mathlib.Algebra.GroupWithZero.Defs","kind":"inductive"},{"where":"type","name":"Submonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"body","name":"nonZeroDivisorsLeft","module":"Mathlib.Algebra.GroupWithZero.NonZeroDivisors","kind":"def"},{"where":"body","name":"nonZeroDivisorsRight","module":"Mathlib.Algebra.GroupWithZero.NonZeroDivisors","kind":"def"},{"where":"body","name":"Min.min","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":99,"column":0},"end":{"line":101,"column":50}},
      "name": "nonZeroDivisors",
      "module": "Mathlib.Algebra.GroupWithZero.NonZeroDivisors",
      "kind": "def",
      "elaborated_type": "(M₀ : Type u_1) → [inst : MonoidWithZero M₀] → Submonoid M₀",
      "doc": "The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`. ",
      "short": "nonZeroDivisors",
      "signature_source": "def nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀ :=",
      "body_source": "nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
