window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots"] = {
  "module": "Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots",
  "cards": {
    "IsPrimitiveRoot": {
      "refs": [{"where":"type","name":"CommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":60,"column":0},"end":{"line":65,"column":48}},
      "name": "IsPrimitiveRoot",
      "module": "Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots",
      "kind": "inductive",
      "elaborated_type": "{M : Type u_1} → [CommMonoid M] → M → ℕ → Prop",
      "doc": "An element `ζ` is a primitive `k`-th root of unity if `ζ ^ k = 1`,\nand if `l` satisfies `ζ ^ l = 1` then `k ∣ l`. ",
      "short": "IsPrimitiveRoot",
      "signature_source": "@[mk_iff IsPrimitiveRoot.iff_def]\nstructure IsPrimitiveRoot (ζ : M) (k : ℕ) : Prop where\n  pow_eq_one : ζ ^ k = 1\n  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
