window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Dimension.Finrank"] = {
  "module": "Mathlib.LinearAlgebra.Dimension.Finrank",
  "cards": {
    "Module.finrank": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Cardinal","module":"Mathlib.SetTheory.Cardinal.Defs","kind":"def"},{"where":"body","name":"Module.rank","module":"Mathlib.LinearAlgebra.Dimension.Basic","kind":"def"},{"where":"body","name":"MonoidWithZeroHom","module":"Mathlib.Algebra.GroupWithZero.Hom","kind":"inductive"},{"where":"body","name":"MonoidWithZeroHom.funLike","module":"Mathlib.Algebra.GroupWithZero.Hom","kind":"def"}],
      "range": {"start":{"line":49,"column":0},"end":{"line":63,"column":34}},
      "name": "Module.finrank",
      "module": "Mathlib.LinearAlgebra.Dimension.Finrank",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → (M : Type u_2) → [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → ℕ",
      "doc": "The rank of a module as a natural number.\n\nFor a finite-dimensional vector space `V` over a field `k`, `Module.finrank k V` is equal to\nthe dimension of `V` over `k`.\n\nFor a general module `M` over a ring `R`, `Module.finrank R M` is defined to be the supremum of the\ncardinalities of the `R`-linearly independent subsets of `M`, if this supremum is finite. It is\ndefined by convention to be `0` if this supremum is infinite. See `Module.rank` for a\ncardinal-valued version where infinite rank modules have rank an infinite cardinal.\n\nNote that if `R` is not a field then there can exist modules `M` with `¬(Module.Finite R M)` but\n`finrank R M ≠ 0`. For example `ℚ` has `finrank` equal to `1` over `ℤ`, because the nonempty\n`ℤ`-linearly independent subsets of `ℚ` are precisely the nonzero singletons. ",
      "short": "finrank",
      "signature_source": "noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=",
      "body_source": "Cardinal.toNat (Module.rank R M)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
