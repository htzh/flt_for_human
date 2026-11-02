window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.NumberTheory.Divisors"] = {
  "module": "Mathlib.NumberTheory.Divisors",
  "cards": {
    "Nat.divisors": {
      "refs": [{"where":"type","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Finset.Ico","module":"Mathlib.Order.Interval.Finset.Defs","kind":"def"},{"where":"body","name":"Finset.filter","module":"Mathlib.Data.Finset.Filter","kind":"def"},{"where":"body","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"Nat.decidable_dvd","module":"Init.Data.Nat.Dvd","kind":"def"}],
      "range": {"start":{"line":51,"column":0},"end":{"line":52,"column":54}},
      "name": "Nat.divisors",
      "module": "Mathlib.NumberTheory.Divisors",
      "kind": "def",
      "elaborated_type": "ℕ → Finset ℕ",
      "doc": "`divisors n` is the `Finset` of divisors of `n`. By convention, we set `divisors 0 = ∅`. ",
      "short": "divisors",
      "signature_source": "def divisors : Finset ℕ :=",
      "body_source": "{d ∈ Ico 1 (n + 1) | d ∣ n}",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/Divisors.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
