window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.LaurentSeries"] = {
  "module": "Mathlib.RingTheory.LaurentSeries",
  "cards": {
    "LaurentSeries": {
      "refs": [{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"HahnSeries","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"inductive"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":98,"column":0},"end":{"line":102,"column":50}},
      "name": "LaurentSeries",
      "module": "Mathlib.RingTheory.LaurentSeries",
      "kind": "abbrev",
      "elaborated_type": "(R : Type u) → [Zero R] → Type (max 0 u)",
      "doc": "`LaurentSeries R` is the type of formal Laurent series with coefficients in `R`, denoted `R⸨X⸩`.\n\nIt is implemented as a `HahnSeries` with value group `ℤ`.\n",
      "short": "LaurentSeries",
      "signature_source": "abbrev LaurentSeries (R : Type u) [Zero R] :=",
      "body_source": "R⟦ℤ⟧",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/LaurentSeries.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
