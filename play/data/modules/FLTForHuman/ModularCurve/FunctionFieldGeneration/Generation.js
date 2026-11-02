window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation"] = {
  "module": "FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation",
  "cards": {
    "ModularCurve.full_eq_adjoin_full_div_prime": {
      "refs": [{"where":"type","name":"ModularCurve.jqN","module":"FLTForHuman.ModularCurve.Defs.Jq","kind":"def"},{"where":"type","name":"ModularCurve.modularFunctionFieldFull","module":"FLTForHuman.ModularCurve.Defs.Fields","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"Fact","module":"Mathlib.Basic.Logic.Basic","kind":"inductive"},{"where":"type","name":"HahnSeries.powerSeriesAlgebra","module":"Mathlib.RingTheory.HahnSeries.PowerSeries","kind":"def"},{"where":"type","name":"IntermediateField","module":"Mathlib.FieldTheory.IntermediateField.Basic","kind":"inductive"},{"where":"type","name":"IntermediateField.adjoin","module":"Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","kind":"def"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat.Prime.one_lt'","module":"Mathlib.Data.Nat.Prime.Defs","kind":"theorem"},{"where":"type","name":"NeZero.of_gt'","module":"Mathlib.Algebra.Order.IsBotOne","kind":"theorem"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"type","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"type","name":"Unit","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Zero.ofOfNat0","module":"Init.Data.Zero","kind":"def"}],
      "range": {"start":{"line":293,"column":0},"end":{"line":310,"column":86}},
      "name": "ModularCurve.full_eq_adjoin_full_div_prime",
      "module": "FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation",
      "kind": "theorem",
      "elaborated_type": "∀ (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ),\n  ¬p ∣ M →\n    ModularCurve.modularFunctionFieldFull (M * p ^ (a + 1)) =\n      IntermediateField.adjoin ℚ\n        (insert (ModularCurve.jqN (p ^ (a + 1))) ↑(ModularCurve.modularFunctionFieldFull (M * p ^ a)))",
      "doc": "**One new generator per prime power**: for `p ∤ M`,\n`F^full_{M p ^ (a + 1)} = ℚ(F^full_{M p ^ a}, j(q ^ (p ^ (a + 1))))`. This is the\n`Inputs.full_eq_adjoin_full_div_prime` field. Verbatim from\n`Theorems/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean`. ",
      "short": "full_eq_adjoin_full_div_prime",
      "signature_source": "theorem full_eq_adjoin_full_div_prime (M : ℕ) [NeZero M] (p : ℕ)\n    [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) :\n    modularFunctionFieldFull (M * p ^ (a + 1)) =\n      IntermediateField.adjoin ℚ\n        (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :\n          Set (LaurentSeries ℚ))) :=",
      "body_source": "by\n  refine le_antisymm ?_ ?_\n  · rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]\n    rintro x ⟨d, hd0, hdN, rfl⟩\n    exact w1_jqN_mem_adjoin_top_insert M p a hpM d hdN\n  · rw [IntermediateField.adjoin_le_iff]\n    rintro x (rfl | hx)\n    · exact jqd_mem_full (M * p ^ (a + 1)) (dvd_mul_left _ _)\n    · exact full_degeneracy_le (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ a))) hx",
      "source_file": "lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Generation.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
