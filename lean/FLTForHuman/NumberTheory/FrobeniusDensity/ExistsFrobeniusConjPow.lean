/-
  The Frobenius realisability theorem in valuation form
  (`FrobeniusDensity.exists_frobenius_conj_pow_of_statement`): a Galois element
  `σ` of `Gal(ℚ̄/ℚ)` is, on a finite intermediate field `L`, a conjugate of a
  power of a Frobenius `τ` at some place `A` over a prime outside any finite set
  `S`.

  The proof passes to the Galois closure `galoisLevel L`, applies the
  Frobenius-density statement there, lifts the arithmetic Frobenius at the prime
  of `𝓞 (galoisLevel L)` to `𝓞 ℚ̄` (`NumberField.exists_isFrobenius_lift_arithFrobAt`),
  and realises that lift as a valuation-theoretic Frobenius
  (`ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem`) via the
  localisation place `NumberField.exists_valuationSubring_eq_localization`.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_exists_frobenius_conj_pow_of_statement.lean`,
  105 lines); the pin's `C6P1CFD` block (`galoisLevel`, `le_galoisLevel`,
  `exists_pow_pow_eq`) is transcribed at the same public names in a private
  namespace. The mathematics is math/019 §4.
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.FrobeniusLift
import FLTForHuman.NumberTheory.FrobeniusDensity.ValuationSubringLocalization
import FLTForHuman.NumberTheory.FrobeniusDensity.TaylorWilesPrimes
import FLTForHuman.NumberTheory.FrobeniusAtPlace
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Algebra.Rat

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped NumberField Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace FrobeniusDensity

namespace ExistsFrobeniusConjPowAux

section S0

variable (L : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ L]

/-- The Galois closure of `L` inside `ℚ̄`, over which the density statement is
applied. -/
noncomputable abbrev galoisLevel : IntermediateField ℚ ℚ̄ := IntermediateField.normalClosure ℚ L ℚ̄

scoped instance : FiniteDimensional ℚ (galoisLevel L) := normalClosure.is_finiteDimensional ℚ L ℚ̄
scoped instance : IsGalois ℚ (galoisLevel L) := IsGalois.normalClosure ℚ L ℚ̄
scoped instance : NumberField (galoisLevel L) := NumberField.mk

omit [FiniteDimensional ℚ L] in
theorem le_galoisLevel : L ≤ galoisLevel L := IntermediateField.le_normalClosure L

end S0

/-- For `k` coprime to `orderOf g`, some power of `g ^ k` returns `g`. -/
theorem exists_pow_pow_eq {G : Type*} [Group G] [Finite G] (g : G) {k : ℕ} (hk : k.Coprime (orderOf g)) :
    ∃ j : ℕ, (g ^ k) ^ j = g := by
  rcases Nat.lt_or_ge 1 (orderOf g) with h1 | h1
  · obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1
    refine ⟨j, ?_⟩
    rw [← pow_mul, ← pow_mod_orderOf, hj, pow_one]
  · refine ⟨0, ?_⟩
    have : orderOf g = 1 := le_antisymm h1 (orderOf_pos g)
    rw [pow_zero, eq_comm, ← orderOf_eq_one_iff, this]

end ExistsFrobeniusConjPowAux

open ExistsFrobeniusConjPowAux in
theorem exists_frobenius_conj_pow_of_statement
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (j : ℕ),
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x := by

  obtain ⟨ℓ, hℓS, hℓ, hreal⟩ := hFD (galoisLevel L) (σ.restrictNormal (galoisLevel L)) S

  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (galoisLevel L)) (FrobeniusDensity.ratPrimeIdeal ℓ)
  haveI := hQmax; haveI := hQover
  haveI : Finite (𝓞 (galoisLevel L) ⧸ Q) :=
    FrobeniusDensity.finite_quotient_of_ne_bot (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := hreal Q inferInstance inferInstance inferInstance

  obtain ⟨Qt, hQt, τ, hQtQ, hres, hstab, hfrob⟩ := NumberField.exists_isFrobenius_lift_arithFrobAt (galoisLevel L) ℓ hℓ Q
  obtain ⟨A, hA⟩ := NumberField.exists_valuationSubring_eq_localization Qt
  have hℓQt : ((ℓ : ℕ) : 𝓞 ℚ̄) ∈ Qt := by
    have h1 : ((ℓ : ℤ) : 𝓞 (galoisLevel L)) ∈ Q := by
      have := (Ideal.mem_of_liesOver Q (FrobeniusDensity.ratPrimeIdeal ℓ) (ℓ : ℤ)).mp
        (Ideal.mem_span_singleton_self _)
      simpa using this
    have h2 := (Ideal.mem_of_liesOver Qt Q ((ℓ : ℤ) : 𝓞 (galoisLevel L))).mp h1
    simpa using h2
  obtain ⟨hAℓ, hAτ⟩ := ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem Qt ℓ hℓ hℓQt τ hstab hfrob A hA

  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨j, hj⟩ := exists_pow_pow_eq (σ.restrictNormal (galoisLevel L)) hk
  obtain ⟨γ, hγ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := galoisLevel L) (E := AlgebraicClosure ℚ) c⁻¹
  refine ⟨ℓ, hℓ, hℓS, A, τ, γ, j, hAℓ, hAτ, fun x hx => ?_⟩
  have key : (γ * τ ^ j * γ⁻¹).restrictNormal (galoisLevel L) = σ.restrictNormal (galoisLevel L) := by
    have hγ' : γ.restrictNormal (galoisLevel L) = c⁻¹ := hγ
    have e1 : (γ * τ ^ j * γ⁻¹).restrictNormal (galoisLevel L)
        = γ.restrictNormal (galoisLevel L) * (τ.restrictNormal (galoisLevel L)) ^ j * (γ.restrictNormal (galoisLevel L))⁻¹ := by
      change AlgEquiv.restrictNormalHom (galoisLevel L) (γ * τ ^ j * γ⁻¹) = AlgEquiv.restrictNormalHom (galoisLevel L) γ
        * (AlgEquiv.restrictNormalHom (galoisLevel L) τ) ^ j * (AlgEquiv.restrictNormalHom (galoisLevel L) γ)⁻¹
      rw [map_mul, map_mul, map_inv, map_pow]
    have hsk : σ.restrictNormal (galoisLevel L) ^ k = c⁻¹ * τ.restrictNormal (galoisLevel L) * c⁻¹⁻¹ := by
      rw [inv_inv, hres, ← hc]; simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [e1, hγ', ← hj, hsk, conj_pow]
  have hxE : x ∈ (galoisLevel L) := le_galoisLevel L hx
  have e2 := AlgEquiv.restrictNormal_commutes (γ * τ ^ j * γ⁻¹) (galoisLevel L) ⟨x, hxE⟩
  have e3 := AlgEquiv.restrictNormal_commutes σ (galoisLevel L) ⟨x, hxE⟩
  rw [key] at e2

  change (algebraMap (galoisLevel L) ℚ̄) ((σ.restrictNormal (galoisLevel L)) ⟨x, hxE⟩) = (γ * τ ^ j * γ⁻¹) x at e2
  change (algebraMap (galoisLevel L) ℚ̄) ((σ.restrictNormal (galoisLevel L)) ⟨x, hxE⟩) = σ x at e3
  rw [← e2, ← e3]

end FrobeniusDensity
