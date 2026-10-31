window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Ring.NegOnePow"] = {
  "module": "Mathlib.Algebra.Ring.NegOnePow",
  "cards": {
    "Int.negOnePow": {
      "refs": [{"where":"type","name":"Units","module":"Mathlib.Algebra.Group.Units.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Additive","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"},{"where":"body","name":"Additive.addCommGroup","module":"Mathlib.Algebra.Group.TypeTags.Basic","kind":"def"}],
      "range": {"start":{"line":29,"column":0},"end":{"line":30,"column":43}},
      "name": "Int.negOnePow",
      "module": "Mathlib.Algebra.Ring.NegOnePow",
      "kind": "def",
      "elaborated_type": "ℤ → ℤˣ",
      "doc": "The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`. ",
      "short": "negOnePow",
      "signature_source": "def negOnePow (n : ℤ) : ℤˣ :=",
      "body_source": "(-1 : ℤˣ) ^ n",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/NegOnePow.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
