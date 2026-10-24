window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Units.Defs"] = {
  "module": "Mathlib.Algebra.Group.Units.Defs",
  "cards": {
    "IsUnit": {
      "refs": [{"where":"type","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"body","name":"Units","module":"Mathlib.Algebra.Group.Units.Defs","kind":"inductive"},{"where":"body","name":"Units.val","module":"Mathlib.Algebra.Group.Units.Defs","kind":"abbrev"}],
      "range": {"start":{"line":358,"column":0},"end":{"line":365,"column":23}},
      "name": "IsUnit",
      "module": "Mathlib.Algebra.Group.Units.Defs",
      "kind": "def",
      "elaborated_type": "{M : Type u_1} → [Monoid M] → M → Prop",
      "doc": "An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse.\nThe actual definition says that `a` is equal to some `u : Mˣ`, where\n`Mˣ` is a bundled version of `IsUnit`. ",
      "short": "IsUnit",
      "signature_source": "@[to_additive /-- An element `a : M` of an `AddMonoid` is an `AddUnit` if it has a two-sided\nadditive inverse. The actual definition says that `a` is equal to some `u : AddUnits M`,\nwhere `AddUnits M` is a bundled version of `IsAddUnit`. -/]\ndef IsUnit [Monoid M] (a : M) : Prop :=",
      "body_source": "∃ u : Mˣ, (u : M) = a",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Units": {
      "refs": [{"where":"type","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"}],
      "range": {"start":{"line":44,"column":0},"end":{"line":57,"column":25}},
      "name": "Units",
      "module": "Mathlib.Algebra.Group.Units.Defs",
      "kind": "inductive",
      "elaborated_type": "(α : Type u) → [Monoid α] → Type u",
      "doc": "Units of a `Monoid`, bundled version. Notation: `αˣ`.\n\nAn element of a `Monoid` is a unit if it has a two-sided inverse.\nThis version bundles the inverse element so that it can be computed.\nFor a predicate see `IsUnit`. ",
      "short": "Units",
      "signature_source": "structure Units (α : Type u) [Monoid α] where\n  /-- The underlying value in the base `Monoid`. -/\n  val : α\n  /-- The inverse value of `val` in the base `Monoid`. -/\n  inv : α\n  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/\n  val_inv : val * inv = 1\n  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/\n  inv_val : inv * val = 1",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Units.val": {
      "refs": [{"where":"type","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Units","module":"Mathlib.Algebra.Group.Units.Defs","kind":"inductive"}],
      "range": {"start":{"line":51,"column":2},"end":{"line":51,"column":5}},
      "name": "Units.val",
      "module": "Mathlib.Algebra.Group.Units.Defs",
      "kind": "abbrev",
      "elaborated_type": "{α : Type u} → [inst : Monoid α] → αˣ → α",
      "doc": "The underlying value in the base `Monoid`. ",
      "short": "val",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
