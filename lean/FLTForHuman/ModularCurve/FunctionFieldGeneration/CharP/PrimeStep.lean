/-
  The `C` layer's prime step (workorder JQ2) — `j(q ^ M)` lies in the level-`M * p` field, over an
  arbitrary field.

  The node `ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime`: for `F` the level-`M * p`
  field `K⟮j(q), j(q ^ (M * p))⟯`, show `j(q ^ M) ∈ F`. This is the `C`-layer twin of the `ℚ`
  step `ModularCurve.jqN_div_mem_modularFunctionField`, and both are instances of one theorem.

  ## A delegation, not a second proof

  The comparison this node performs — the level-`p` equation and the transported minimal polynomial
  of `j(q ^ M)` over `F`, their root descriptions, and the case split that leaves a single common
  root — is `Generic/PrimeStep.lean`'s `levelSeries_mem_levelField_mul_prime`, ported from the `ℚ`
  proof (`FunctionFieldGeneration/Descent.lean`) after that proof was refactored into two producers
  and named index arithmetic. The `C` instance reads the theory at `K` itself (`κ = κ' = K`, the
  identity coefficient extension), so its one source condition is `rfl`; what stays here is the
  conversion between the theory's `levelField` and the pin's named `modularFunctionFieldC`.

  Consequently the pin's `S_` engine `jqNModC_mem_mffC_mul_prime_of_prod` — the same comparison
  written inline, taking the slot product as a hypothesis — is **not** carried: its content is the
  generic theorem, its only consumer was this headline, and restating it here would be the second
  proof of one theorem.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`.

  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.PrimeStep
import FLTForHuman.ModularCurve.FunctionFieldGeneration.CharP.LevelPackage

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- **The `C` prime step**: `j(q ^ M)` lies in the level-`M * p` field. The general theorem read at
`K` itself (identity coefficient extension, so the source condition is `rfl`), with the
absolute-to-relative step supplied by `coe_adjoin_baseField`. The pin's wrapper statement verbatim. -/
theorem jqNModC_mem_modularFunctionFieldC_mul_prime {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) := by
  have hmem : levelSeries (jqModC K) M ∈ levelField (jqModC K) (M * p) :=
    levelSeries_mem_levelField_mul_prime (jqModC K) rfl
      (M := M) (p := p) (ζ := ζ) (hζ := hζ) (pkg_pkgAt M hall)
  have hpair : ({jqModC K} ∪ {qExpand K (M * p) (jqModC K)} : Set (LaurentSeries K))
      = {jqModC K, qExpand K (M * p) (jqModC K)} := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  have hset : ((levelField (jqModC K) (M * p) : Set (LaurentSeries K)))
      = (modularFunctionFieldC K (M * p) : Set (LaurentSeries K)) := by
    rw [coe_adjoin_baseField, modularFunctionFieldC]
    simp only [levelSeries, jqNModC]
    rw [hpair]
  show levelSeries (jqModC K) M ∈ (modularFunctionFieldC K (M * p) : Set (LaurentSeries K))
  rw [← hset]
  exact hmem

end ModularCurve
