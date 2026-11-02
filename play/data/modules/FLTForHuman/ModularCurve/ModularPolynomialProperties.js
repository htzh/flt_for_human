window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.ModularPolynomialProperties"] = {
  "module": "FLTForHuman.ModularCurve.ModularPolynomialProperties",
  "cards": {
    "ModularCurve.exists_phiIrreducible_evalSymm": {
      "refs": [{"where":"type","name":"ModularCurve.EvalSymm","module":"FLTForHuman.ModularCurve.Defs.PhiGen","kind":"def"},{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"ModularCurve.ModularPolynomialData.Φ","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"abbrev"},{"where":"type","name":"ModularCurve.PhiIrreducible","module":"FLTForHuman.ModularCurve.Defs.PhiGen","kind":"def"},{"where":"type","name":"Fact","module":"Mathlib.Basic.Logic.Basic","kind":"inductive"},{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat.Prime.one_lt'","module":"Mathlib.Data.Nat.Prime.Defs","kind":"theorem"},{"where":"type","name":"NeZero.of_gt'","module":"Mathlib.Algebra.Order.IsBotOne","kind":"theorem"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":135,"column":0},"end":{"line":168,"column":58}},
      "name": "ModularCurve.exists_phiIrreducible_evalSymm",
      "module": "FLTForHuman.ModularCurve.ModularPolynomialProperties",
      "kind": "theorem",
      "elaborated_type": "∀ (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)], ∃ data, ModularCurve.PhiIrreducible data ∧ ModularCurve.EvalSymm data.Φ",
      "doc": "There is an irreducible symmetric modular polynomial datum at every prime\n`ℓ`. Verbatim from the pin wrapper\n`Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`. ",
      "short": "exists_phiIrreducible_evalSymm",
      "signature_source": "theorem exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :\n    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ :=",
      "body_source": "by\n\n  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩\n  haveI hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=\n    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)\n  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=\n    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)\n  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=\n    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)\n  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)\n    (Set.mem_singleton ℓ) hℓ.out.ne_zero\n  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero\n  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by\n    rw [hzu.unit_spec]\n    exact hz\n  have hζ1 : hzu.unit ^ ℓ = 1 := by\n    refine Units.ext ?_\n    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]\n\n  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ\n\n  have hint : ∀ k, PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k\n  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=\n    fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k\n\n  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem\n  exact ⟨data,\n    PhiGen.phiIrreducible_of_splits ℓ hzu.unit hζ data\n      (PhiGen.splits_of_coeff_evalAtJ_eq hzu.unit hc data hcoeff),\n    PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff⟩",
      "source_file": "lean/FLTForHuman/ModularCurve/ModularPolynomialProperties.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
