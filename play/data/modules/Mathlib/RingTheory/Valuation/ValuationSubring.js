window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Valuation.ValuationSubring"] = {
  "module": "Mathlib.RingTheory.Valuation.ValuationSubring",
  "cards": {
    "ValuationSubring": {
      "refs": [{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":35,"column":0},"end":{"line":42,"column":56}},
      "name": "ValuationSubring",
      "module": "Mathlib.RingTheory.Valuation.ValuationSubring",
      "kind": "inductive",
      "elaborated_type": "(K : Type u) → [Field K] → Type u",
      "doc": "A valuation subring of a field `K` is a subring `A` such that for every `x : K`,\neither `x ∈ A` or `x⁻¹ ∈ A`.\n\nThis is equivalent to being maximal in the domination order\nof local subrings (the stacks project definition). See `LocalSubring.isMax_iff`.\n",
      "short": "ValuationSubring",
      "signature_source": "structure ValuationSubring extends Subring K where\n  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
