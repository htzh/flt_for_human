window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Set.Defs"] = {
  "module": "Mathlib.Data.Set.Defs",
  "cards": {
    "Set": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":44,"column":0},"end":{"line":51,"column":32}},
      "name": "Set",
      "module": "Mathlib.Data.Set.Defs",
      "kind": "def",
      "elaborated_type": "Type u → Type u",
      "doc": "A set is a collection of elements of some type `α`.\n\nAlthough `Set` is defined as `α → Prop`, this is an implementation detail which should not be\nrelied on. Instead, `Set.ofPred` (also written `{x | p x}`) and membership of a set (`∈`) should be\nused to convert between sets and predicates.\n",
      "short": "Set",
      "signature_source": "@[use_set_notation_for_order]\ndef Set (α : Type u) :=",
      "body_source": "α → Prop",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Set/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "Set.ofPred": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":65,"column":0},"end":{"line":68,"column":3}},
      "name": "Set.ofPred",
      "module": "Mathlib.Data.Set.Defs",
      "kind": "def",
      "elaborated_type": "{α : Type u} → (α → Prop) → Set α",
      "doc": "Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}` ",
      "short": "ofPred",
      "signature_source": "@[implicit_reducible]\ndef Set.ofPred {α : Type u} (p : α → Prop) : Set α :=",
      "body_source": "p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Set/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "Set.univ": {
      "seed": true,
      "refs": [{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Set.ofPred","module":"Mathlib.Data.Set.Defs","kind":"def"}],
      "range": {"start":{"line":210,"column":0},"end":{"line":215,"column":31}},
      "name": "Set.univ",
      "module": "Mathlib.Data.Set.Defs",
      "kind": "def",
      "elaborated_type": "{α : Type u} → Set α",
      "doc": "The universal set on a type `α` is the set containing all elements of `α`.\n\nThis is conceptually the \"same as\" `α` (in set theory, it is actually the same), but type theory\nmakes the distinction that `α` is a type while `Set.univ` is a term of type `Set α`. `Set.univ` can\nitself be coerced to a type `↥Set.univ` which is in bijection with (but distinct from) `α`. ",
      "short": "univ",
      "signature_source": "def univ : Set α :=",
      "body_source": "{_a | True}",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Set/Defs.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
