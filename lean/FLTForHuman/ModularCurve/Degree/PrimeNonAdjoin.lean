/-
  The prime non-adjoin headline: `j(q ^ p)` is not in `K(j(q))`.

  ## What the module is

  Two layers:

  * **the engine** (`jqNModC_not_mem_adjoin_of_forall_aeval_ne`) — no polynomial
    in `j(q)` has the value `j(q ^ p)`, so `j(q ^ p)` is not in `K(j(q))`.
    `j(q)` is transcendental (`Degree/PhiDegree.lean`), so `K[j(q)]` is a
    polynomial ring, hence integrally closed; the modular relation
    `Φ_p(j(q), j(q^p)) = 0` (`exists_phiIrreducible_evalSymm`) is monic in its
    second variable, so a rational function integral over `K[j(q)]` is a
    polynomial. This is the pin's `S_` file at `S_:512`.
  * **the two headlines** — the same statement with the hypothesis discharged,
    once from the coefficient obstruction of the cyclotomic conjugates
    (`jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne`, a `Theorems/` headline
    though the pin keeps its wrapper `private` at `S_:557`) and once in
    characteristic zero (`jqNModC_prime_not_mem_adjoin_of_charZero`, `S_:568`).

  The pin's `jqNModC_prime_not_mem_adjoin_of_coeff_ne_zero` (`S_:562`) is
  `private` there and stays `private` here: it is the intermediate discharge
  that only the characteristic-zero headline consumes.

  ## Reuse

  `Degree/JqCyclotomicConjugates.lean` supplies the conjugates' structure — the
  pole/degree forcing (`coeff_aeval_jqModC_neg_natDegree`,
  `natDegree_eq_of_aeval_eq`, `monic_of_aeval_eq`), the modular relation at
  `jqNModC` (`phiAtSeed_jqNModC_eval`), the index congruence
  (`jqNModC_congr`) and the coefficient obstruction
  (`aeval_jqModC_ne_jqNModC`). `Defs/PhiAtSlot.lean` supplies `phiAtSeed`,
  `phiAtSeed_map` and `phiAtSeed_monic`; `Degree/PhiDegree.lean` supplies
  `transcendental_jqModC`; `ModularPolynomialProperties.lean` supplies
  `exists_phiIrreducible_evalSymm`; `JqCoeffPositivity.lean` supplies
  `one_le_coeff_jq`, the positivity of the `q`-coefficients of `j` used to see
  that one of them is nonzero in `ℤ`; `Defs/JqCoeff.lean` supplies
  `jqModC_eq_map_intCast` and `jqModC_rat`. Mathlib supplies
  `exists_integer_of_is_root_of_monic`
  (`Mathlib/RingTheory/Polynomial/RationalRoot.lean`),
  `Transcendental.uniqueFactorizationMonoid_adjoin`
  (`Mathlib/RingTheory/Algebraic/Basic.lean`) and the scoped
  `IntermediateField.algebraAdjoinAdjoin` instances
  (`Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean`).

  FLT provenance, pinned `aa2d8b3`:
  `Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean` and
  `…_of_forall_aeval_ne.lean` are the statement authority;
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean#L506-L583

  spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean
  spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean
-/
import FLTForHuman.ModularCurve.Degree.JqCyclotomicConjugates
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.JqCoeffPositivity
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

/-! ## The engine

`K[j(q)]` is a polynomial ring and the modular relation makes `j(q^p)` integral
over it; an integral element of a fraction field of a polynomial ring is a
polynomial. -/

section FieldLevel

open scoped IntermediateField.algebraAdjoinAdjoin

variable {K : Type*} [Field K]

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- If no polynomial in `jqModC K` takes the value `jqNModC K p`, then
`jqNModC K p` is not in the field `K(jqModC K)`. -/
theorem jqNModC_not_mem_adjoin_of_forall_aeval_ne
    (h : ∀ P : Polynomial K, Polynomial.aeval (jqModC K) P ≠ jqNModC K p) :
    jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  intro hmem
  have : UniqueFactorizationMonoid (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))) :=
    (ModularCurve.transcendental_jqModC K).uniqueFactorizationMonoid_adjoin
  obtain ⟨data, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have hrel : (phiAtSeed data (jqModC K)).eval (jqNModC K p) = 0 := by
    have h1 := phiAtSeed_jqNModC_eval (R := K) p data 1
    rwa [jqNModC_one, jqNModC_congr (Nat.one_mul p)] at h1
  have hQmap : (phiAtSeed data (⟨jqModC K, Algebra.self_mem_adjoin_singleton K (jqModC K)⟩ :
      Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))).map
        (algebraMap (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K))
      = phiAtSeed data (jqModC K) := by
    rw [phiAtSeed_map]
    rfl
  have hroot : Polynomial.aeval (⟨jqNModC K p, hmem⟩ : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (phiAtSeed data (⟨jqModC K, Algebra.self_mem_adjoin_singleton K (jqModC K)⟩ :
        Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))) = 0 := by
    apply (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K)).injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq, ← Polynomial.eval_map,
      hQmap]
    exact hrel
  obtain ⟨a, ha, -⟩ := exists_integer_of_is_root_of_monic (phiAtSeed_monic data _) hroot
  have hcoe : jqNModC K p = (a : LaurentSeries K) := by
    have h1 := congrArg
      (fun t : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) => (t : LaurentSeries K)) ha
    exact h1.trans (IntermediateField.algebraAdjoinAdjoin.coe_algebraMap K ({jqModC K} : Set (LaurentSeries K)) a)
  have hmemA : jqNModC K p ∈ Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
    rw [hcoe]
    exact a.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmemA
  obtain ⟨P, hP⟩ := (AlgHom.mem_range _).mp hmemA
  exact h P hP

end FieldLevel

/-! ## The two headlines -/

/-- The headline with the obstruction as hypothesis: verbatim from
`Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean`
(the pin keeps the wrapper `private` at `S_:557`; it is a `Theorems/` headline,
so it is promoted here). -/
theorem jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (h : ∀ P : Polynomial K, Polynomial.aeval (jqModC K) P ≠ jqNModC K p) : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
  jqNModC_not_mem_adjoin_of_forall_aeval_ne p h

/-- The intermediate discharge: `p ≠ 0` in `K` and one nonzero regular
coefficient of `jqModC K` refute the equation. -/
private theorem jqNModC_prime_not_mem_adjoin_of_coeff_ne_zero {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (hpK : (p : K) ≠ 0) (hw : ∃ m : ℕ, 0 < m ∧ (jqModC K).coeff ((p * m : ℕ) : ℤ) ≠ 0) : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  obtain ⟨m, hm, hw⟩ := hw
  exact jqNModC_not_mem_adjoin_of_forall_aeval_ne p fun P => aeval_jqModC_ne_jqNModC hpK hm hw P

/-- The characteristic-zero headline: verbatim from
`Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean`.
`p ≠ 0` in `K`, and positivity of the `q`-coefficients of `j` over `ℤ` gives the
nonzero regular coefficient the obstruction needs. -/
theorem jqNModC_prime_not_mem_adjoin_of_charZero {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact (Nat.Prime p)] : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  refine jqNModC_prime_not_mem_adjoin_of_coeff_ne_zero p (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    ⟨1, Nat.one_pos, ?_⟩
  have hz : (jqModC ℤ).coeff ((p * 1 : ℕ) : ℤ) ≠ 0 := by
    intro h0
    have h1 := ModularCurve.one_le_coeff_jq (p * 1)
    have h2 : jq.coeff ((p * 1 : ℕ) : ℤ) = (((jqModC ℤ).coeff ((p * 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
      rw [← jqModC_rat, jqModC_eq_map_intCast]
      rfl
    rw [h2, h0] at h1
    norm_num at h1
  have h3 : (jqModC K).coeff ((p * 1 : ℕ) : ℤ) = (((jqModC ℤ).coeff ((p * 1 : ℕ) : ℤ) : ℤ) : K) := by
    rw [jqModC_eq_map_intCast]
    rfl
  rw [h3]
  exact Int.cast_ne_zero.mpr hz

end ModularCurve

end

#print axioms ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne
#print axioms ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero
