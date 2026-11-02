window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.Defs.Polynomial"] = {
  "module": "FLTForHuman.ModularCurve.Defs.Polynomial",
  "cards": {
    "ModularCurve.ModularPolynomialData": {
      "refs": [{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"}],
      "range": {"start":{"line":31,"column":0},"end":{"line":43,"column":44}},
      "name": "ModularCurve.ModularPolynomialData",
      "module": "FLTForHuman.ModularCurve.Defs.Polynomial",
      "kind": "inductive",
      "elaborated_type": "(N : ℕ) → [NeZero N] → Type",
      "doc": "The modular polynomial datum at `N`: a monic `Φ ∈ ℤ[X][Y]` of degree\n`ψ(N)`, vanishing at `j(q ^ N)` when `Y` is evaluated at `jq`. The splitting\ninput is the assertion that such a `Φ` exists, is symmetric, and is\nirreducible. ",
      "short": "ModularPolynomialData",
      "signature_source": "structure ModularPolynomialData (N : ℕ) [NeZero N] : Type where\n\n  Φ : Polynomial (Polynomial ℤ)\n\n  monic : Φ.Monic\n\n  natDegree_eq : Φ.natDegree = dedekindPsi N\n\n  eval_eq_zero : Φ.eval₂ evalAtJ (jqN N) = 0",
      "body_source": "",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/Polynomial.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.ModularPolynomialData.Φ": {
      "refs": [{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"}],
      "range": {"start":{"line":37,"column":2},"end":{"line":37,"column":3}},
      "name": "ModularCurve.ModularPolynomialData.Φ",
      "module": "FLTForHuman.ModularCurve.Defs.Polynomial",
      "kind": "abbrev",
      "elaborated_type": "{N : ℕ} → [inst : NeZero N] → ModularCurve.ModularPolynomialData N → Polynomial (Polynomial ℤ)",
      "doc": "",
      "short": "Φ",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    }
  }
};
