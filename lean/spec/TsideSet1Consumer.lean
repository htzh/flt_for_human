/-
  Consumer specification for T12 SET 1, the surjection half of `R = T`.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the four SET-1 modules, one per subject home:

  * `FLTForHuman/NumberTheory/ValuationAtPlace.lean`  — `mem_of_isIntegral`,
    `exists_integral_mul_eq_of_liesOverPrime`;
  * `FLTForHuman/NumberTheory/FrobeniusAtPlace.lean`  — `exists_isFrobeniusAt_rat`,
    `exists_isFrobeniusAt_of_liesOverPrime`;
  * `FLTForHuman/GaloisRep/AdicCharpoly.lean`         — the two charpoly bridges;
  * `FLTForHuman/HeckeGalois/Surjective.lean`         — the two R=T interface
    statements.

  The zone below is a real cross-module composition, not a list of `#check`s and
  not `sorry`-terminated (playbook §7.2): the wire test instantiates the
  number-theoretic Frobenius existence at a prime, feeds the resulting place
  through both charpoly bridges together with T11's `charpoly_frob`, and derives
  the trace membership that the surjection argument consumes; the HeckeGalois
  theorems then close the loop. It is deliberately **not part of any library**
  (nothing globs `spec/`), so it can never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet1Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.NumberTheory.ValuationAtPlace
import FLTForHuman.NumberTheory.FrobeniusAtPlace
import FLTForHuman.GaloisRep.AdicCharpoly
import FLTForHuman.HeckeGalois.Surjective

set_option autoImplicit false

noncomputable section

open Polynomial

/-! ## Zone `[surjection]` — the SET-1 wire test across all four homes -/

namespace TsideSet1

variable {N : ℕ} [NeZero N] {S : Set ℕ}
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type}
  [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
  [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

-- NumberTheory (`ValuationAtPlace`): an element of `ℚ̄` integral over `ℤ` lies in
-- every place.
example (A : ValuationSubring (AlgebraicClosure ℚ)) {b : AlgebraicClosure ℚ}
    (hb : IsIntegral ℤ b) : b ∈ A :=
  ValuationSubring.mem_of_isIntegral A b hb

-- NumberTheory (`FrobeniusAtPlace`): over every prime there is a place carrying
-- an arithmetic Frobenius.
example (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ :=
  ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ

-- The wire test. At a Frobenius place over `ℓ`, transport the datum's charpoly
-- identity across the base-change isomorphism: `exists_isFrobeniusAt_rat`
-- (NumberTheory) supplies `A, σ`, T11's `charpoly_frob` supplies the equation for
-- `H.ρ`, `charpoly_eq_of_isEquiv` moves it to `ρR.baseChangeAlong φ`, and
-- `charpoly_baseChangeAlong` reads the result over `T`. The `X`-coefficient of
-- the conclusion is the trace membership `π (T_ℓ) ∈ φ.range` — the input of the
-- surjection argument, produced here without the HeckeGalois module.
example (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) {R : Type} [CommRing R]
    [IsLocalRing R] [Algebra 𝒪 R] (ρR : GaloisRepAdic R) (φ : R →ₐ[𝒪] T)
    (hφ : IsLocalHom (φ : R →+* T))
    (he : (ρR.baseChangeAlong (φ : R →+* T) hφ).IsEquiv H.ρ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) :
    H.π (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ∈ φ.range := by
  obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
  have h1 := H.charpoly_frob ℓ hℓ hℓN hℓS A hA σ hσ
  have h2 := GaloisRepAdic.charpoly_eq_of_isEquiv he σ
  have h3 := GaloisRepAdic.charpoly_baseChangeAlong (φ : R →+* T) hφ ρR σ
  have h4 := congrArg (fun p : T[X] => p.coeff 1) (h1.symm.trans (h2.symm.trans h3))
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, coeff_map,
    mul_one, ite_eq_right (show (1 : ℕ) ≠ 2 by decide), ite_eq_right (show (1 : ℕ) ≠ 0 by decide),
    zero_sub, add_zero, RingHom.coe_coe] at h4
  exact ⟨-(LinearMap.charpoly (ρR.ρ σ)).coeff 1,
    by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]; rw [map_neg, ← h4, neg_neg]⟩

-- HeckeGalois (`Surjective`): the trace input above is exactly what makes `φ`
-- surjective.
example (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra 𝒪 R] (ρR : GaloisRepAdic R) (φ : R →ₐ[𝒪] T)
    (hφ : IsLocalHom (φ : R →+* T))
    (he : (ρR.baseChangeAlong (φ : R →+* T) hφ).IsEquiv H.ρ) : Function.Surjective φ :=
  H.surjective_of_isEquiv_baseChangeAlong hS ρR φ hφ he

-- HeckeGalois (`Surjective`), the universal-property form: the deformation
-- ring's `R → T` map exists and is surjective.
example {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧
      ∃ hφ : IsLocalHom (φ : D.R →+* T),
        (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ :=
  D.exists_surjective_algHom_of_heckeGaloisRepDatum H hS h𝒟 hres

end TsideSet1

end
