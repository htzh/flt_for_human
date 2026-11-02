window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.NumberTheory.DedekindPsi"] = {
  "module": "FLTForHuman.NumberTheory.DedekindPsi",
  "cards": {
    "dedekindPsi": {
      "refs": [{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Finset.filter","module":"Mathlib.Data.Finset.Filter","kind":"def"},{"where":"body","name":"Finset.sum","module":"Mathlib.Algebra.BigOperators.Group.Finset.Defs","kind":"def"},{"where":"body","name":"Nat.divisors","module":"Mathlib.NumberTheory.Divisors","kind":"def"},{"where":"body","name":"Squarefree","module":"Mathlib.Algebra.Squarefree.Basic","kind":"def"}],
      "range": {"start":{"line":52,"column":0},"end":{"line":54,"column":72}},
      "name": "dedekindPsi",
      "module": "FLTForHuman.NumberTheory.DedekindPsi",
      "kind": "def",
      "elaborated_type": "ℕ → ℕ",
      "doc": "The Dedekind psi function: `ψ(N) = ∑_{d ∣ N, d squarefree} N / d`, which\nequals `N ∏_{p ∣ N} (1 + 1/p)`. ",
      "short": "dedekindPsi",
      "signature_source": "def dedekindPsi (N : ℕ) : ℕ :=",
      "body_source": "∑ d ∈ N.divisors with Squarefree d, N / d",
      "source_file": "lean/FLTForHuman/NumberTheory/DedekindPsi.lean",
      "has_source": true,
      "has_refs": true
    },
    "dedekindPsi_prime": {
      "refs": [{"where":"type","name":"dedekindPsi","module":"FLTForHuman.NumberTheory.DedekindPsi","kind":"def"},{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":61,"column":0},"end":{"line":65,"column":43}},
      "name": "dedekindPsi_prime",
      "module": "FLTForHuman.NumberTheory.DedekindPsi",
      "kind": "theorem",
      "elaborated_type": "∀ {p : ℕ}, Nat.Prime p → dedekindPsi p = p + 1",
      "doc": "`ψ(p) = p + 1` for a prime `p`. Part of the cone's outbound interface\n(indeg 72). ",
      "short": "dedekindPsi_prime",
      "signature_source": "theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=",
      "body_source": "by\n  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]\n  simp [hp.squarefree, Nat.div_self hp.pos]",
      "source_file": "lean/FLTForHuman/NumberTheory/DedekindPsi.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
