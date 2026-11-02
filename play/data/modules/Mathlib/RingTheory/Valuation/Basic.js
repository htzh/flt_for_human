window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Valuation.Basic"] = {
  "module": "Mathlib.RingTheory.Valuation.Basic",
  "cards": {
    "Valuation": {
      "refs": [{"where":"type","name":"LinearOrderedCommMonoidWithZero","module":"Mathlib.Algebra.Order.GroupWithZero.Canonical","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":77,"column":0},"end":{"line":82,"column":66}},
      "name": "Valuation",
      "module": "Mathlib.RingTheory.Valuation.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_3) → (Γ₀ : Type u_4) → [LinearOrderedCommMonoidWithZero Γ₀] → [Ring R] → Type (max u_3 u_4)",
      "doc": "The type of `Γ₀`-valued valuations on `R`.\n\nWhen you extend this structure, make sure to extend `ValuationClass`. ",
      "short": "Valuation",
      "signature_source": "structure Valuation extends R →*₀ Γ₀ where\n  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/\n  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
