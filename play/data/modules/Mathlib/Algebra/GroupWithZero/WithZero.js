window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.GroupWithZero.WithZero"] = {
  "module": "Mathlib.Algebra.GroupWithZero.WithZero",
  "cards": {
    "WithZero.exp": {
      "refs": [{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"body","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"body","name":"Multiplicative.ofAdd","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"}],
      "range": {"start":{"line":363,"column":0},"end":{"line":364,"column":40}},
      "name": "WithZero.exp",
      "module": "Mathlib.Algebra.GroupWithZero.WithZero",
      "kind": "def",
      "elaborated_type": "{M : Type u_4} → M → WithZero (Multiplicative M)",
      "doc": "The exponential map as a function `M → Mᵐ⁰`. ",
      "short": "exp",
      "signature_source": "def exp (a : M) : Mᵐ⁰ :=",
      "body_source": "coe <| .ofAdd a",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean",
      "has_source": true,
      "has_refs": true
    },
    "WithZero.log": {
      "refs": [{"where":"type","name":"AddMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Multiplicative","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"body","name":"Equiv","module":"Mathlib.Logic.Equiv.Defs","kind":"inductive"},{"where":"body","name":"WithZero.recZeroCoe","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"}],
      "range": {"start":{"line":394,"column":0},"end":{"line":395,"column":60}},
      "name": "WithZero.log",
      "module": "Mathlib.Algebra.GroupWithZero.WithZero",
      "kind": "def",
      "elaborated_type": "{M : Type u_4} → [AddMonoid M] → WithZero (Multiplicative M) → M",
      "doc": "The logarithm as a function `Mᵐ⁰ → M` with junk value `log 0 = 0`. ",
      "short": "log",
      "signature_source": "def log (x : Mᵐ⁰) : M :=",
      "body_source": "x.recZeroCoe 0 Multiplicative.toAdd",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean",
      "has_source": true,
      "has_refs": true
    },
    "WithZero.one": {
      "refs": [{"where":"type","name":"WithZero","module":"Mathlib.Algebra.Group.WithOne.Defs","kind":"def"},{"where":"type","name":"One","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"One.one","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":51,"column":0},"end":{"line":52,"column":15}},
      "name": "WithZero.one",
      "module": "Mathlib.Algebra.GroupWithZero.WithZero",
      "kind": "def",
      "elaborated_type": "{α : Type u_1} → [One α] → One (WithZero α)",
      "doc": "",
      "short": "one",
      "signature_source": "instance one : One (WithZero α) where\n  __ := ‹One α›",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
