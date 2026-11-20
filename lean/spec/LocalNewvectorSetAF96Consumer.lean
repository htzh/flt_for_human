/-
  SET-AF96 consumer (A–D): the conductor of the weight-one lift at `q` is the level's `q`-adic
  valuation.

  **The rows.** `NumberTheory/LocalNewvector/AdelicSpanConductor.lean` (SET-AF96 A–C) carries two
  rows of the `padicK1`-span family: the span of an automorphic function of level `M` has a nonzero
  `padicK1 q a`-fixed vector inside the `q`-adic orbit of the function whenever its fixed submodule
  at `q` is nonzero, and the newvector conductor index of that span is at most `M.factorization p`.
  `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` (SET-AF96 D) carries the converse for the
  lift: a `padicK1 q m`-fixed vector in the span of a *primitive* form's lift forces
  `M.factorization q ≤ m`.

  **The reading.** At the lift the two inequalities meet: the conductor bound produces the index
  `c ≤ M.factorization q` together with a nonzero fixed vector at level `c`, and the factorization
  row reads that same vector as `M.factorization q ≤ c`. Their composition is the equality —
  Casselman's bound in the form the automorphic side consumes — and
  `LocalNewvector.hasNewvectorConductor_unique` (SET-AF96 B) says the index is the only one with that
  property.

  **What comes from outside the set.** The lift's nonvanishing and its right invariance under
  `finiteLevelOne (ratLevel M)` are the two AF-subject rows the SET-AF96 shelf re-read put on the
  ready shelf; they are hypotheses here, so this zone composes only what SET-AF96 itself landed.

  `spec/` is outside every Lake library: this file is checked by
  `lake env lean spec/LocalNewvectorSetAF96Consumer.lean` and never enters the build.
-/

import FLTForHuman.NumberTheory.LocalNewvector.AdelicSpanConductor
import FLTForHuman.LanglandsTunnell.WeightOneLiftFactorizationBound

set_option autoImplicit false
noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm LocalNewvector
open DihedralWeightOne CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace LocalNewvectorSetAF96Consumer

/-- The conductor index of the lift is the level's `q`-adic valuation. -/
theorem factorization_eq_conductor_of_isPrimitiveForm
    {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M} {f : CuspForm (Gamma1 M) 1}
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime]
    (hφ : weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f) ≠ 0)
    (hlev : ∀ g ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M), ∀ x,
      weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) =
        weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f) x) :
    ∃ c : ℕ, c = M.factorization q ∧
      HasNewvectorConductor q (AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f))) c ∧
      ∀ c' : ℕ,
        HasNewvectorConductor q (AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f))) c' →
          c' = c := by
  obtain ⟨c, hc, hcond⟩ :=
    AdelicSpan.exists_hasNewvectorConductor_le_factorization
      (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f)) hφ (NeZero.ne M) hlev q
  obtain ⟨y, hy, hy0, hfix⟩ :=
    AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
      (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f)) (NeZero.ne M) hlev q c hcond.1
  have hge : M.factorization q ≤ c :=
    factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1 M ψ f hf q c y hy hfix
      hy0
  exact ⟨c, le_antisymm hc hge, hcond, fun c' hc' => hasNewvectorConductor_unique q hc' hcond⟩

/-- The span row made explicit: the conductor bound's own inequality and the fixed vector it
produces, in one statement. -/
theorem exists_fixed_vector_at_conductor
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : φ ≠ 0) {M : ℕ} (hM : M ≠ 0)
    (hlev : ∀ g ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M), ∀ x,
      φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (q : ℕ) [Fact q.Prime] :
    ∃ c : ℕ, c ≤ M.factorization q ∧
      HasNewvectorConductor q (AdelicSpan φ) c ∧
      ∃ y : AdelicSpan φ,
        y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ) ∧
        y ≠ 0 ∧ y ∈ fixedSubmodule (padicK1 q c) (AdelicSpan φ) := by
  obtain ⟨c, hc, hcond⟩ :=
    AdelicSpan.exists_hasNewvectorConductor_le_factorization φ hφ hM hlev q
  obtain ⟨y, hy, hy0, hfix⟩ :=
    AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
      φ hM hlev q c hcond.1
  exact ⟨c, hc, hcond, y, hy, hy0, hfix⟩

end LocalNewvectorSetAF96Consumer
