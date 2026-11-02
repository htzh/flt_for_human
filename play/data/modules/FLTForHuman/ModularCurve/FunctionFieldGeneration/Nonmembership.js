window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.FunctionFieldGeneration.Nonmembership"] = {
  "module": "FLTForHuman.ModularCurve.FunctionFieldGeneration.Nonmembership",
  "cards": {
    "ModularCurve.jqN_pow_not_mem_adjoin_full": {
      "refs": [{"where":"type","name":"ModularCurve.jqN","module":"FLTForHuman.ModularCurve.Defs.Jq","kind":"def"},{"where":"type","name":"ModularCurve.modularFunctionFieldFull","module":"FLTForHuman.ModularCurve.Defs.Fields","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Fact","module":"Mathlib.Basic.Logic.Basic","kind":"inductive"},{"where":"type","name":"HahnSeries.powerSeriesAlgebra","module":"Mathlib.RingTheory.HahnSeries.PowerSeries","kind":"def"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat.Prime.one_lt'","module":"Mathlib.Data.Nat.Prime.Defs","kind":"theorem"},{"where":"type","name":"NeZero.of_gt'","module":"Mathlib.Algebra.Order.IsBotOne","kind":"theorem"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Set.ofPred","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"type","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"type","name":"Unit","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Zero.ofOfNat0","module":"Init.Data.Zero","kind":"def"}],
      "range": {"start":{"line":611,"column":0},"end":{"line":621,"column":42}},
      "name": "ModularCurve.jqN_pow_not_mem_adjoin_full",
      "module": "FLTForHuman.ModularCurve.FunctionFieldGeneration.Nonmembership",
      "kind": "theorem",
      "elaborated_type": "∀ (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ),\n  ModularCurve.jqN p ∉ ModularCurve.modularFunctionFieldFull M →\n    ModularCurve.jqN (p ^ (a + 2)) ∉\n      IntermediateField.adjoin ℚ\n        (↑(ModularCurve.modularFunctionFieldFull M) ∪ {x | ∃ i ≤ a + 1, x = ModularCurve.jqN (p ^ i)})",
      "doc": "**The prime-power tower**: for `jqN p ∉ F_M^full`,\n`j(q ^ (p ^ (a + 2))) ∉ ℚ(F_M^full, j(q ^ p), …, j(q ^ (p ^ (a + 1))))`. This is\nthe `Inputs.jqN_pow_not_mem_adjoin_full` field. Verbatim from\n`Theorems/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`. ",
      "short": "jqN_pow_not_mem_adjoin_full",
      "signature_source": "theorem jqN_pow_not_mem_adjoin_full (M : ℕ) [NeZero M] (p : ℕ)\n    [hp : Fact (Nat.Prime p)] (a : ℕ)\n    (hF : jqN p ∉ modularFunctionFieldFull M) :\n    jqN (p ^ (a + 2)) ∉ IntermediateField.adjoin ℚ\n      ((modularFunctionFieldFull M : Set (LaurentSeries ℚ))\n        ∪ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a + 1 ∧ x = jqN (p ^ i)}) :=",
      "body_source": "jqN_pow_not_mem_adjoin_full_key M p a hF",
      "source_file": "lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Nonmembership.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
