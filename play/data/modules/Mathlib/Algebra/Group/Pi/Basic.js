window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Pi.Basic"] = {
  "module": "Mathlib.Algebra.Group.Pi.Basic",
  "cards": {
    "Pi.addCommGroup": {
      "refs": [{"where":"type","name":"AddCommGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"body","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"body","name":"AddGroup","module":"Mathlib.Algebra.Group.Defs","kind":"inductive"},{"where":"body","name":"Pi.addCommMonoid","module":"Mathlib.Algebra.Group.Pi.Basic","kind":"def"},{"where":"body","name":"Pi.addGroup","module":"Mathlib.Algebra.Group.Pi.Basic","kind":"def"}],
      "range": {"start":{"line":118,"column":2},"end":{"line":118,"column":13}},
      "name": "Pi.addCommGroup",
      "module": "Mathlib.Algebra.Group.Pi.Basic",
      "kind": "def",
      "elaborated_type": "{I : Type u} → {f : I → Type v₁} → [(i : I) → AddCommGroup (f i)] → AddCommGroup ((i : I) → f i)",
      "doc": "",
      "short": "addCommGroup",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    },
    "Pi.addCommMonoid": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"body","name":"Pi.addMonoid","module":"Mathlib.Algebra.Group.Pi.Basic","kind":"def"}],
      "range": {"start":{"line":84,"column":2},"end":{"line":84,"column":13}},
      "name": "Pi.addCommMonoid",
      "module": "Mathlib.Algebra.Group.Pi.Basic",
      "kind": "def",
      "elaborated_type": "{I : Type u} → {f : I → Type v₁} → [(i : I) → AddCommMonoid (f i)] → AddCommMonoid ((i : I) → f i)",
      "doc": "",
      "short": "addCommMonoid",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
