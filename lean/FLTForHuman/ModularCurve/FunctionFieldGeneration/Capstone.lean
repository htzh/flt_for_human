/-
  The capstone of `functionFieldGeneration`: the unconditional theorem.

  `hall_all` is the module's strong induction: it carries the two invariants
  `Tight` (the relative degree of `ℚ⟮jq⟯(jqN d)` over `ℚ⟮jq⟯` is `ψ(d)`) and `Gen`
  (the two-generator field is already the full divisor field) over the divisor lattice.
  It is private — an internal induction with no consumer of its own — and
  `functionFieldGeneration` with the three corollaries below is the public surface.

  The induction applies, and only applies:

  * the induction hypothesis in the shape the induction gives it, `Hall (M * p ^ a)`;
  * `modularFunctionField_eq_full_of` for the `Gen` half — the descent and the
    divisor-lattice collapse in one step;
  * `relfinrank_full_eq_mul` for the `Tight` half, at `Hall M`;
  * `relfinrank_modularFunctionField`, `relfinrank_mul_relfinrank`, `full_degeneracy_le`,
    `full_congr`, `dedekindPsi_mul_prime_pow_succ` and `jqd_mem_full` for the degree
    arithmetic along the tower;
  * `tight_one`/`gen_one` for the base of the induction;
  * `functionFieldGeneration_iff_full_eq` for the headline.

  The descent is consumed in its `Hall M` form, `jqN_div_mem_modularFunctionField`,
  through `modularFunctionField_eq_full_of`.

  The private helpers are the induction's own data: the prime-power decomposition of a
  level `d ≠ 1` (`exists_eq_mul_pow_succ_of_ne_one`) and the bound below it
  (`lt_of_eq_mul_pow_succ`).

  spec-pin: Theorems/Thm_ModularCurve_functionFieldGeneration.lean
  spec-pin: Theorems/Thm_ModularCurve_modularFunctionField_eq_full.lean
  spec-pin: Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean
  spec-pin: Theorems/Thm_ModularCurve_relfinrank_full_eq_dedekindPsi.lean
-/
import Mathlib.FieldTheory.Relrank
import Mathlib.Data.Nat.Factorization.Basic
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent
import FLTForHuman.ModularCurve.FunctionFieldGeneration.DegreeStep
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-! ## The induction's own data -/

/-- `Hall` gives the relative degree of the full field: `relfinrank_modularFunctionField`
with `Gen` substituted. -/
private theorem relfinrank_full_of (N : ℕ) [NeZero N] (h : Hall N) :
    IntermediateField.relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull N) = dedekindPsi N := by
  obtain ⟨ht, hg⟩ := h N dvd_rfl
  unfold Gen at hg
  unfold Tight at ht
  rw [← hg, relfinrank_modularFunctionField N, ht]

private theorem F0_le_full (N : ℕ) [NeZero N] : ℚ⟮jq⟯ ≤ modularFunctionFieldFull N := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  have h := jqd_mem_full N (one_dvd N)
  rw [qExpand_one_apply] at h
  exact h

/-! ## The strong induction and the capstone -/

/-- **The level's top prime-power step.** For `d ≠ 1`, write `d = M * p ^ (a + 1)` with
`p = d.minFac` prime, `p ∤ M` and `M ≠ 0`: `M * p ^ a` is the divisor the strong induction
descends to, and `p ^ (a + 1)` the prime power the `Tight` half measures. -/
private theorem exists_eq_mul_pow_succ_of_ne_one {d : ℕ} [NeZero d] (h1 : d ≠ 1) :
    ∃ (M p a : ℕ), p.Prime ∧ ¬ p ∣ M ∧ M ≠ 0 ∧ d = M * p ^ (a + 1) := by
  have hp : d.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨k, M, hpM, hdM⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne d) d.minFac hp.ne_one
  have hM0 : M ≠ 0 := by rintro rfl; rw [mul_zero] at hdM; exact NeZero.ne d hdM
  obtain ⟨a, rfl⟩ := exists_eq_succ_of_eq_pow_mul hdM (Nat.minFac_dvd d) hpM
  exact ⟨M, d.minFac, a, hp, hpM, hM0, hdM.trans (mul_comm _ M)⟩

/-- **The induction's step down.** With `d = M * p ^ (a + 1)` and `p` prime, the level
`M * p ^ a` is a proper divisor of `d`, hence below it. -/
private theorem lt_of_eq_mul_pow_succ {d M p a : ℕ} (hM : M ≠ 0) (hp : p.Prime)
    (h : d = M * p ^ (a + 1)) : M * p ^ a < d :=
  lt_of_mul_prime_eq (mul_ne_zero hM (pow_ne_zero _ hp.ne_zero)) hp
    (by rw [h, pow_succ, mul_assoc])

/-- **The module's strong induction.** `Tight` and `Gen` hold at every divisor of every
`N ≠ 0`. It is the source of the corollary layer below (`modularFunctionField_eq_full`,
`finrank_adjoin_jqN_eq_dedekindPsi`, `relfinrank_full_eq_dedekindPsi`), so it is kept in
this module; `functionFieldGeneration` consumes it just below. -/
private theorem hall_all : ∀ N : ℕ, N ≠ 0 → Hall N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN d hdN hd
  by_cases hdlt : d < N
  · exact ih d hdlt (NeZero.ne d) d dvd_rfl
  have hNd : N = d := le_antisymm (not_lt.mp hdlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdN)
  subst hNd
  by_cases h1 : N = 1
  · subst h1; exact ⟨tight_one, gen_one⟩
  have hgen : Gen N := by
    unfold Gen
    exact modularFunctionField_eq_full_of N ih
  refine ⟨?_, hgen⟩
  unfold Tight
  obtain ⟨M, p, a, hp, hpM, hM0, hdM'⟩ := exists_eq_mul_pow_succ_of_ne_one h1
  have : NeZero M := ⟨hM0⟩
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hlow_lt : M * p ^ a < N := lt_of_eq_mul_pow_succ hM0 hp hdM'
  have hall_low : Hall (M * p ^ a) := ih _ hlow_lt (mul_ne_zero hM0 (pow_ne_zero _ hp.ne_zero))
  have hallM : Hall M := fun e he _ => hall_low e (he.trans ⟨p ^ a, rfl⟩)
  have hlowdeg : IntermediateField.relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull (M * p ^ a)) =
      dedekindPsi (M * p ^ a) := relfinrank_full_of _ hall_low
  have hstep := relfinrank_full_eq_mul M p a hpM hallM
  have htower := IntermediateField.relfinrank_mul_relfinrank (F0_le_full (M * p ^ a))
    (full_degeneracy_le (N := M * p ^ a) (M := M * p ^ (a + 1)) ⟨p, mul_pow_succ_eq⟩)
  rw [← relfinrank_modularFunctionField N]
  unfold Gen at hgen
  rw [hgen, full_congr hdM', ← htower, hlowdeg, hstep]
  rw [hdM']
  exact (dedekindPsi_mul_prime_pow_succ hp hpM).symm

/-- **The theorem.** For every `N ≠ 0`, every `j(q ^ d)` with `d ∣ N` lies in
`ℚ(j(q), j(q ^ N))`: the function field of `X₀(N)` is generated by `j` and `j_N`.
Unconditional. -/
theorem functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N :=
  (functionFieldGeneration_iff_full_eq N).mpr (hall_all N (NeZero.ne N) N dvd_rfl).2.symm

/-- The two-generator field is the full divisor field. -/
theorem modularFunctionField_eq_full (N : ℕ) [NeZero N] :
    modularFunctionField N = modularFunctionFieldFull N :=
  (hall_all N (NeZero.ne N) N dvd_rfl).2

/-- The modular equation at level `N` has full degree `ψ(N)`. -/
theorem finrank_adjoin_jqN_eq_dedekindPsi (N : ℕ) [NeZero N] :
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N :=
  (hall_all N (NeZero.ne N) N dvd_rfl).1

/-- The full field has degree `ψ(N)` over `ℚ(j)`. -/
theorem relfinrank_full_eq_dedekindPsi (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull N) = dedekindPsi N := by
  rw [← modularFunctionField_eq_full N, relfinrank_modularFunctionField N]
  exact finrank_adjoin_jqN_eq_dedekindPsi N

end ModularCurve

end

