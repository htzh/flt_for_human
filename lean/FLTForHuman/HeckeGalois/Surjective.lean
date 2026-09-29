/-
  The surjection half of `R = T`: `HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong`
  says an `𝒪`-algebra map `φ : R → T` whose base-changed adic representation is
  isomorphic to the Eichler–Shimura representation `H.ρ` is surjective, because
  the traces of the `φ`-images of the Hecke operators `T_ℓ` are already in the
  image (via the Frobenius charpoly identity and the two charpoly bridges) and
  those operators generate `T` over `𝒪`. The universal-property corollary
  `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`
  produces such a `φ` from the universal deformation ring and concludes it is
  surjective.

  Ported verbatim from
  `P2M/Sol/S_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong.lean`
  and `P2M/Sol/S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean`
  (pinned `aa2d8b3`, 51 + 9 lines); the statements are the pin's `Theorems/`
  wrappers. The two charpoly bridges live in `GaloisRep/AdicCharpoly.lean` and
  the place-existence lemma in `NumberTheory/FrobeniusAtPlace.lean`. The
  mathematics is math/018 §§3.1, 4.
-/
import FLTForHuman.GaloisRep.AdicCharpoly
import FLTForHuman.NumberTheory.FrobeniusAtPlace
import FLTForHuman.GaloisRep.Defs.DeformationRingData
import FLTForHuman.HeckeGalois.Defs.HeckeGaloisRepDatum

set_option autoImplicit false

open Polynomial

theorem CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong {N : ℕ}
    [NeZero N] {S : Set ℕ} {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type}
    [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
    [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra 𝒪 R] (ρR : GaloisRepAdic R) (φ : R →ₐ[𝒪] T)
    (hφ : IsLocalHom (φ : R →+* T))
    (he : (ρR.baseChangeAlong (φ : R →+* T) hφ).IsEquiv H.ρ) : Function.Surjective φ := by

  have hgen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      H.π (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ∈ φ.range := by
    intro ℓ hℓ hℓN hℓS
    obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
    have h1 := H.charpoly_frob ℓ hℓ hℓN hℓS A hA σ hσ
    have h2 := GaloisRepAdic.charpoly_eq_of_isEquiv he σ
    have h3 := GaloisRepAdic.charpoly_baseChangeAlong (φ : R →+* T) hφ ρR σ
    have h4 := congrArg (fun p : T[X] => p.coeff 1) (h1.symm.trans (h2.symm.trans h3))
    simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, coeff_map,
      mul_one, ite_eq_right (show (1 : ℕ) ≠ 2 by decide), ite_eq_right (show (1 : ℕ) ≠ 0 by decide), zero_sub,
      add_zero, RingHom.coe_coe] at h4

    exact ⟨-(LinearMap.charpoly (ρR.ρ σ)).coeff 1, by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]; rw [map_neg, ← h4, neg_neg]⟩

  have hπ : ∀ t : CuspForm.heckeAlgebra N 2 S, H.π t ∈ φ.range := by
    rintro ⟨t, ht⟩
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
        · exact hgen ℓ hℓ hℓN hℓS
        · exact absurd (hS q hq hqN) hqS
    | algebraMap r =>
        have h : H.π ⟨algebraMap ℤ _ r, Subalgebra.algebraMap_mem _ r⟩ = (r : T) :=
          eq_intCast (H.π.comp (algebraMap ℤ (CuspForm.heckeAlgebra N 2 S))) r
        rw [h]
        exact intCast_mem φ.range r
    | add x y hx hy ihx ihy =>
        have h : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : CuspForm.heckeAlgebra N 2 S) =
            ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [h, H.π.map_add]
        exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
        have h : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : CuspForm.heckeAlgebra N 2 S) =
            ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [h, H.π.map_mul]
        exact mul_mem ihx ihy
  have hle : Algebra.adjoin 𝒪 (Set.range H.π) ≤ φ.range :=
    Algebra.adjoin_le (by rintro _ ⟨t, rfl⟩; exact hπ t)
  rw [H.adjoin_range_π, top_le_iff] at hle
  exact (AlgHom.range_eq_top φ).mp hle

theorem GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type}
    [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
    [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧
      ∃ hφ : IsLocalHom (φ : D.R →+* T),
        (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ := by
  obtain ⟨φ, ⟨hφ, he⟩, -⟩ := D.universal T H.residue_surjective H.ρ h𝒟 hres
  exact ⟨φ, H.surjective_of_isEquiv_baseChangeAlong hS D.ρ φ hφ he, hφ, he⟩
