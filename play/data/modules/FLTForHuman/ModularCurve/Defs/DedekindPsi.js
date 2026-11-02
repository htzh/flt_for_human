window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.Defs.DedekindPsi"] = {
  "module": "FLTForHuman.ModularCurve.Defs.DedekindPsi",
  "cards": {
    "ModularCurve.dedekindPsi": {
      "refs": [{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"dedekindPsi","module":"FLTForHuman.NumberTheory.DedekindPsi","kind":"def"}],
      "range": {"start":{"line":27,"column":0},"end":{"line":28,"column":51}},
      "name": "ModularCurve.dedekindPsi",
      "module": "FLTForHuman.ModularCurve.Defs.DedekindPsi",
      "kind": "def",
      "elaborated_type": "ℕ → ℕ",
      "doc": "The Dedekind psi function, at the pin's name and namespace. ",
      "short": "dedekindPsi",
      "signature_source": "def dedekindPsi (N : ℕ) : ℕ :=",
      "body_source": "_root_.dedekindPsi N",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/DedekindPsi.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.dedekindPsi_prime": {
      "refs": [{"where":"type","name":"ModularCurve.dedekindPsi","module":"FLTForHuman.ModularCurve.Defs.DedekindPsi","kind":"def"},{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":34,"column":0},"end":{"line":35,"column":29}},
      "name": "ModularCurve.dedekindPsi_prime",
      "module": "FLTForHuman.ModularCurve.Defs.DedekindPsi",
      "kind": "theorem",
      "elaborated_type": "∀ {p : ℕ}, Nat.Prime p → ModularCurve.dedekindPsi p = p + 1",
      "doc": "",
      "short": "dedekindPsi_prime",
      "signature_source": "theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=",
      "body_source": "_root_.dedekindPsi_prime hp",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/DedekindPsi.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
