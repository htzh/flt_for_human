window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Squarefree.Basic"] = {
  "module": "Mathlib.Algebra.Squarefree.Basic",
  "cards": {
    "Squarefree": {
      "refs": [{"where":"type","name":"Monoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"body","name":"IsUnit","module":"Mathlib.Algebra.Group.Units.Defs","kind":"def"},{"where":"body","name":"semigroupDvd","module":"Mathlib.Algebra.Divisibility.Basic","kind":"def"},{"where":"body","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":40,"column":0},"end":{"line":43,"column":31}},
      "name": "Squarefree",
      "module": "Mathlib.Algebra.Squarefree.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [Monoid R] → R → Prop",
      "doc": "An element of a monoid is squarefree if the only squares that\ndivide it are the squares of units. ",
      "short": "Squarefree",
      "signature_source": "def Squarefree [Monoid R] (r : R) : Prop :=",
      "body_source": "∀ x : R, x * x ∣ r → IsUnit x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Squarefree/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
