/-
  Consumer specification for T12 SET 3, the conditional `R ≅ T` capstone.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the SET-3 module
  `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` (the conditional capstone
  `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel`), composed with the
  SET-1 module `FLTForHuman/HeckeGalois/Surjective.lean`.

  The `[capstone]` zone below is a real cross-module composition (not a list of
  `#check`s and not `sorry`-terminated, playbook §7.2): from a
  `GaloisRep.DeformationRingData` `D` and a `CuspForm.HeckeGaloisRepDatum` `H`,
  SET 1's `DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`
  produces the algebra map `φ : D.R → T`, its local-homomorphism proof and the
  base-change isomorphism of its adic representation; the conditional capstone
  then consumes those together with the three patching hypotheses
  (`hfree`/`hann`/`hker`) extracted from an `Algebra.PatchingLevel`, a
  `GaloisRepAdic` and its `hWfrob`, and concludes `W.IsModularModelOfLevel`.
  Deleting either the SET-1 or the SET-3 module fails this file.

  Because the map `φ` is *produced* inside the composition, the module-compatibility
  input `hcompat` is taken in the quantified form `∀ φ hφ, IsEquiv … → compatible`;
  that is the shape the capstone's `hcompat` has once `φ` is fixed.

  It is deliberately **not part of any library** (nothing globs `spec/`), so it can
  never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet3Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.WeierstrassCurve.ModularityLifting
import FLTForHuman.HeckeGalois.Surjective
import FLTForHuman.HeckeGalois.Defs.HeckeGaloisRepDatum
import FLTForHuman.GaloisRep.Defs.DeformationRingData
import FLTForHuman.GaloisRep.Defs.Adic
import FLTForHuman.Patching.Defs.PatchingDatum

set_option autoImplicit false

noncomputable section

open Polynomial

namespace TsideSet3

/-! ## Zone `[capstone]` — the universal map composed with the conditional `R ≅ T` -/

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
    (h𝒟H : 𝒟 H.ρ)
    (hresH : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T))))
    {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M]
    (hcompat : ∀ (φ : D.R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : D.R →+* T)),
      (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ →
      ∀ (x : D.R) (m : M), φ x • m = x • m)
    {r : ℕ} (L : Algebra.PatchingLevel 𝒪 r D.R M ⊥)
    (hfree : Module.Free D.R M) (hann : Module.annihilator D.R M = ⊥)
    (hker : RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i)))
    (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW)
    (hWres : ρW.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))))
    (hWfrob : ∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρW.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) :
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) := by
  obtain ⟨φ, -, hφ, hφρ⟩ :=
    GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum
      D H (fun q hq hqN => Finset.mem_coe.mpr (hNS q hq hqN)) h𝒟H hresH
  exact WeierstrassCurve.isModularModelOfLevel_of_patchingLevel p W hΔ hp𝒪 D hSprime hNS hN H
    φ hφ hφρ (hcompat φ hφ hφρ) L hfree hann hker ρW h𝒟W hWres hWfrob

/-! ## Zone `[inputs]` — the annihilator hypothesis is a free-module consequence -/

-- The capstone takes `hann : Module.annihilator D.R M = ⊥` as one of the three
-- outputs of `Algebra.PatchingLevel.free_and_ker_eq_span`. Over a nontrivial free
-- module it is mathlib's `Module.annihilator_eq_bot` at `FaithfulSMul`, so SET 4
-- may discharge it from either the patching lemma or freeness.
example {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (hfree : Module.Free R M) : Module.annihilator R M = ⊥ :=
  Module.annihilator_eq_bot.mpr inferInstance

end TsideSet3

end
