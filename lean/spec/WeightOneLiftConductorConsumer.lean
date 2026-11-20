/-
  SET-AF97 consumer: the conductor of the weight-one lift *is* the level's `q`-adic valuation —
  unconditionally.

  The two sets compose here. `LanglandsTunnell/WeightOneLiftCuspidalRealization.lean` (SET-AF97 A)
  proves that the lift of a primitive form is nonzero and invariant under the right action of
  `finiteLevelOne (ratLevel N)`. Those were the two hypotheses the SET-AF96 consumer had to assume:
  the span rows of `NumberTheory/LocalNewvector/AdelicSpanConductor.lean` need a nonzero function of
  level `N` to have a conductor index at all, and `LanglandsTunnell/
  WeightOneLiftFactorizationBound.lean` needs the same function for its converse inequality.

  With them discharged, the two inequalities meet at the lift: the conductor bound produces
  `c ≤ N.factorization q` together with a nonzero `padicK1 q c`-fixed vector in the `q`-adic orbit of
  the lift, and the factorization row reads that vector as `N.factorization q ≤ c`. So the lift's
  newvector conductor at `q` is exactly `N.factorization q` — Casselman's bound in the form the
  automorphic side consumes — and `LocalNewvector.hasNewvectorConductor_unique` says it is the only
  such index.

  `spec/` is outside every Lake library: this file is checked by
  `lake env lean spec/WeightOneLiftConductorConsumer.lean` and never enters the build.
-/

import FLTForHuman.LanglandsTunnell.WeightOneLiftCuspidalRealization
import FLTForHuman.NumberTheory.LocalNewvector.AdelicSpanConductor
import FLTForHuman.LanglandsTunnell.WeightOneLiftFactorizationBound

set_option autoImplicit false
noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm LocalNewvector
open DihedralWeightOne CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace WeightOneLiftConductorConsumer

/-- The newvector conductor of the lift at `q` is the level's `q`-adic valuation. -/
theorem conductor_eq_factorization
    {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) 1}
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] :
    ∃ c : ℕ, c = N.factorization q ∧
      HasNewvectorConductor q (AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))) c ∧
      ∀ c' : ℕ,
        HasNewvectorConductor q (AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))) c' →
          c' = c := by
  obtain ⟨hφ, hlev⟩ :=
    weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm N ψ f hf
  obtain ⟨c, hc, hcond⟩ :=
    AdelicSpan.exists_hasNewvectorConductor_le_factorization
      (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)) hφ (NeZero.ne N) hlev q
  obtain ⟨y, hy, hy0, hfix⟩ :=
    AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
      (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)) (NeZero.ne N) hlev q c hcond.1
  have hge : N.factorization q ≤ c :=
    factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1 N ψ f hf q c y hy hfix
      hy0
  exact ⟨c, le_antisymm hc hge, hcond, fun c' hc' => hasNewvectorConductor_unique q hc' hcond⟩

/-- The same statement in the form a consumer of the lift reads: the conductor's index bounds every
`padicK1` level at which the lift has a nonzero fixed vector, and is attained. -/
theorem conductor_le_iff
    {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) 1}
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] {m : ℕ} :
    (∃ y : AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)),
        y ≠ 0 ∧ y ∈ fixedSubmodule (padicK1 q m)
          (AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))) ∧
        y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
          x • AdelicSpan.self (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)))) →
      N.factorization q ≤ m := by
  rintro ⟨y, hy0, hfix, hy⟩
  exact factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1 N ψ f hf q m y hy
    hfix hy0

end WeightOneLiftConductorConsumer
