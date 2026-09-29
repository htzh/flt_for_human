/-
  Consumer specification for T12 SET 7, the driver's closing set.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the two SET-7 nodes:

  * `FLTForHuman/Patching/Exit.lean` — the abstract patching exit
    `Algebra.PatchingDatum.bijective_and_free_of_surjective`; and
  * `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` — the now-**verbatim
    unconditional** `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`,
    which discharges SET 3's frozen `{r} (L) (hfree) (hann) (hker)` inputs.

  Zone `[exit]` applies the exit to an arbitrary `Algebra.PatchingDatum`, a
  compatible surjection and the two side conditions.

  Zone `[assembly]` applies the verbatim assembly to a full T-side context
  (`GaloisRep.DeformationRingData`, `CuspForm.HeckeGaloisRepDatum`, the compatible
  map `φ`, and the patching datum `P`), concluding `W.IsModularModelOfLevel …`.

  Zone `[compose]` is the real end-to-end composition (playbook §7.2, the
  `Universal.lean` lesson): from the single datum `P` and map `φ` it derives the
  surjectivity of `φ` with SET 1, runs the exit to get
  `Function.Bijective φ` and freeness over both `R` and `T`, and runs the
  assembly to get the modularity conclusion — so the file needs the SET-1, SET-4,
  SET-6, exit and assembly modules together, and deleting any of them fails it.

  It is deliberately **not part of any library** (nothing globs `spec/`), so it can
  never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet7Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.Patching.Exit
import FLTForHuman.WeierstrassCurve.ModularityLifting
import FLTForHuman.HeckeGalois.Surjective
import FLTForHuman.HeckeGalois.Defs.HeckeGaloisRepDatum
import FLTForHuman.GaloisRep.Defs.DeformationRingData
import FLTForHuman.GaloisRep.Defs.Adic
import FLTForHuman.Patching.Defs.PatchingDatum

set_option autoImplicit false

open Polynomial

namespace TsideSet7

/-! ## Zone `[exit]` — the abstract patching exit -/

example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M)
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module T M]
    (RtoT : R →ₐ[𝒪] T) (hsurj : Function.Surjective RtoT)
    (hcompat : ∀ (x : R) (m : M), RtoT x • m = x • m) :
    Function.Bijective RtoT ∧ Module.Free R M ∧ Module.Free T M ∧
      Module.annihilator R M = ⊥ ∧
      ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
        Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) :=
  Algebra.PatchingDatum.bijective_and_free_of_surjective hℓ P RtoT hsurj hcompat

/-! ## Zone `[assembly]` — the verbatim unconditional `R ≅ T` capstone -/

example
    (p : ℕ) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    {N : ℕ} [NeZero N] {S : Finset ℕ} (hSprime : ∀ q ∈ S, q.Prime)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hN : CuspForm.HasIntegralStructure N 2)
    {θ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N (S : Set ℕ) 𝒪 θ T)
    (φ : D.R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : D.R →+* T))
    (hφρ : (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ)
    {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M]
    (hcompat : ∀ (x : D.R) (m : M), φ x • m = x • m)
    {r : ℕ} (P : Algebra.PatchingDatum 𝒪 p r D.R M)
    (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW)
    (hWres : ρW.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))))
    (hWfrob : ∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρW.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) :
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) :=
  WeierstrassCurve.isModularModelOfLevel_of_patchingDatum p W hΔ hp𝒪 D hSprime hNS hN H
    φ hφ hφρ hcompat P ρW h𝒟W hWres hWfrob

/-! ## Zone `[compose]` — the driver end to end, from one patching datum -/

example
    (p : ℕ) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    {N : ℕ} [NeZero N] {S : Finset ℕ} (hSprime : ∀ q ∈ S, q.Prime)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hN : CuspForm.HasIntegralStructure N 2)
    {θ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N (S : Set ℕ) 𝒪 θ T)
    (φ : D.R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : D.R →+* T))
    (hφρ : (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ)
    {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M]
    (hcompat : ∀ (x : D.R) (m : M), φ x • m = x • m)
    {r : ℕ} (P : Algebra.PatchingDatum 𝒪 p r D.R M)
    (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW)
    (hWres : ρW.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))))
    (hWfrob : ∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρW.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) :
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) ∧
      Function.Bijective φ ∧ Module.Free D.R M ∧ Module.Free T M := by
  have hsurj : Function.Surjective φ :=
    H.surjective_of_isEquiv_baseChangeAlong (fun q hq hqN => Finset.mem_coe.mpr (hNS q hq hqN))
      D.ρ φ hφ hφρ
  obtain ⟨hbij, hfreeR, hfreeT, -, -⟩ :=
    Algebra.PatchingDatum.bijective_and_free_of_surjective hp𝒪 P φ hsurj hcompat
  exact ⟨WeierstrassCurve.isModularModelOfLevel_of_patchingDatum p W hΔ hp𝒪 D hSprime hNS hN H
      φ hφ hφρ hcompat P ρW h𝒟W hWres hWfrob,
    hbij, hfreeR, hfreeT⟩

end TsideSet7
