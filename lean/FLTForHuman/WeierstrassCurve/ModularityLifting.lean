/-
  The capstone of the T side: the `R ≅ T` assembly, conditional and unconditional.

  `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel` is the port of the pin
  node `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`
  (`P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`,
  pinned `aa2d8b3`, 145 lines), stated **conditionally**: in place of the pin's
  `(P : Algebra.PatchingDatum 𝒪 p r D.R M)` and its two consumers
  (`P.nonempty_patchingLevel_bot hp𝒪` and `L.free_and_ker_eq_span`), the three
  outputs of `Algebra.PatchingLevel.free_and_ker_eq_span` are taken as hypotheses
  (`hfree`, `hann`, `hker`).

  `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` (SET 7) is the pin's
  statement **verbatim**: it takes the `PatchingDatum` back, discharges the three
  frozen hypotheses with `P.nonempty_patchingLevel_bot hp𝒪` (SET 6) and
  `L.free_and_ker_eq_span` (SET 4), and applies the conditional capstone. This is
  why the 3,761-line patching construction is now on this module's import path;
  before SET 7 the conditional split kept it off, so the assembly's proof could be
  exercised without it.

  The argument is the pin's, with the two patching lines removed. It is almost
  entirely *application* of already-ported lemmas:

  * the surjection `Function.Surjective φ` is
    `CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong` (T12 SET 1);
  * the free nontrivial patched module gives the annihilator, hence injectivity,
    through `Module.annihilator_eq_bot` (mathlib);
  * `AlgEquiv.ofBijective` turns `φ` into `e : D.R ≃ₐ[𝒪] T`;
  * the post-isomorphism argument builds `ψW : T →ₐ[𝒪] 𝒪` from the universal
    property `D.universal` and compares Frobenius characteristic polynomials with
    `GaloisRepAdic.charpoly_baseChangeAlong` / `charpoly_eq_of_isEquiv` (SET 1) and
    `ValuationSubring.exists_isFrobeniusAt_rat` (SET 1);
  * the eigenform is extracted by
    `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` and
    `Ideal.exists_ringHom_integralClosure_ker_eq` (SET 2), its level raised by
    `CuspForm.exists_isNormalizedEigenform_of_dvd` (SET 2), with
    `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra` (T10) supplying the
    finiteness the prime-kernel lemma needs.

  The only genuinely new proof content is the `ψW` construction and the `hχ`
  charpoly coefficient read-off. The mathematics is math/018 §4; the driver plan
  and the conditional split are studies/t-side-driver.md §2, §4 and playbook §7.3.
-/
import FLTForHuman.GaloisRep.AdicCharpoly
import FLTForHuman.NumberTheory.FrobeniusAtPlace
import FLTForHuman.HeckeGalois.Surjective
import FLTForHuman.GaloisRep.Defs.DeformationRingData
import FLTForHuman.HeckeGalois.Defs.HeckeGaloisRepDatum
import FLTForHuman.Patching.Defs.PatchingDatum
import FLTForHuman.Algebra.IntegralExtensionCharacters
import FLTForHuman.ModularForms.EigenformExtraction
import FLTForHuman.ModularForms.EigenformLevel
import FLTForHuman.ModularForms.HeckeFiniteAlgebra
import FLTForHuman.WeierstrassCurve.Defs.Modularity
import FLTForHuman.Patching.PatchingConstruction
import FLTForHuman.Patching.LevelDescent

set_option autoImplicit false
-- The pin's proof is transcribed verbatim: it introduces instances with `haveI`
-- inside `Prop` goals, and its signature keeps binders (`hΔ`, `hp𝒪`, and — after
-- the patching substitution — `hfree`/`hker`) that the pin's own argument does not
-- reference. SET 4 consumes the kept binders when it discharges the patching
-- hypotheses, so they stay.
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Polynomial

/-- **The conditional `R ≅ T` capstone.** The pin's
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` with the patching datum
replaced by the three facts
`Algebra.PatchingLevel.free_and_ker_eq_span` extracts from it: a free patching
level `L`, the freeness and trivial-annihilator of its module, and the kernel
identification for `L.ψ`. The conclusion is the pin's, verbatim. -/
theorem WeierstrassCurve.isModularModelOfLevel_of_patchingLevel
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
  classical

  have hsurj : Function.Surjective φ :=
    H.surjective_of_isEquiv_baseChangeAlong (fun q hq hqN => Finset.mem_coe.mpr (hNS q hq hqN))
      D.ρ φ hφ hφρ

  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hmem : x ∈ Module.annihilator D.R M := Module.mem_annihilator.mpr fun m => by
      rw [← hcompat x m, hx, zero_smul]
    rwa [hann] at hmem
  let e : D.R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

  have hres𝒪 : Function.Surjective (IsLocalRing.residue 𝒪 ∘ algebraMap 𝒪 𝒪) := fun x => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨y, rfl⟩
  obtain ⟨φW, ⟨hφW, hEqW⟩, -⟩ := D.universal 𝒪 hres𝒪 ρW h𝒟W hWres

  let ψW : T →ₐ[𝒪] 𝒪 := φW.comp (e.symm : T →ₐ[𝒪] D.R)
  have hψW : ∀ x : D.R, ψW (φ x) = φW x := fun x => by
    show φW (e.symm (e x)) = φW x
    rw [e.symm_apply_apply]

  have hχ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), W.IsGoodPrimeFor ℓ →
      ψW (H.π (CuspForm.heckeAlgebra.T hℓ hℓN (show ℓ ∉ (S : Set ℕ) from
        fun h => hℓS (Finset.mem_coe.mp h)))) = ((W.apOfModel ℓ : ℤ) : 𝒪) := by
    intro ℓ hℓ hℓN hℓS hgood
    obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
    have h1 := H.charpoly_frob ℓ hℓ hℓN (fun h => hℓS (Finset.mem_coe.mp h)) A hA σ hσ
    have h2 := GaloisRepAdic.charpoly_eq_of_isEquiv hφρ σ
    have h3 := GaloisRepAdic.charpoly_baseChangeAlong (φ : D.R →+* T) hφ D.ρ σ
    have h4 := GaloisRepAdic.charpoly_eq_of_isEquiv hEqW σ
    have h5 := GaloisRepAdic.charpoly_baseChangeAlong (φW : D.R →+* 𝒪) hφW D.ρ σ
    have h6 := hWfrob ℓ hℓ hgood hℓS A hA σ hσ

    have hcomp : (ψW : T →+* 𝒪).comp (φ : D.R →+* T) = (φW : D.R →+* 𝒪) := by
      ext x
      exact hψW x
    have h7 : (LinearMap.charpoly (H.ρ.ρ σ)).map (ψW : T →+* 𝒪) = LinearMap.charpoly (ρW.ρ σ) := by
      rw [← h2, h3, Polynomial.map_map, hcomp, ← h5, h4]
    rw [h1, h6] at h7
    have h8 := congrArg (fun q : 𝒪[X] => q.coeff 1) h7
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C,
      mul_one, ite_eq_right (show (1 : ℕ) ≠ 2 by decide),
      ite_eq_right (show (1 : ℕ) ≠ 0 by decide), zero_sub, add_zero, RingHom.coe_coe] at h8
    exact neg_injective h8

  let χ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* 𝒪 := (ψW : T →+* 𝒪).comp H.π
  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N 2 (S : Set ℕ)) :=
    CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN one_le_two _
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨f𝔓, hf𝔓⟩ := Ideal.exists_ringHom_integralClosure_ker_eq (RingHom.ker χ) inferInstance
    (fun n hn => by
      rw [RingHom.mem_ker, map_intCast] at hn
      exact Int.cast_injective (α := 𝒪) (hn.trans Int.cast_zero.symm))
  let χℂ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* ℂ :=
    (algebraMap (integralClosure ℤ ℂ) ℂ).comp f𝔓
  have hχℂ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), W.IsGoodPrimeFor ℓ →
      χℂ (CuspForm.heckeAlgebra.T hℓ hℓN (show ℓ ∉ (S : Set ℕ) from
        fun h => hℓS (Finset.mem_coe.mp h))) = ((W.apOfModel ℓ : ℤ) : ℂ) := by
    intro ℓ hℓ hℓN hℓS hgood
    have hmem : CuspForm.heckeAlgebra.T hℓ hℓN (show ℓ ∉ (S : Set ℕ) from
        fun h => hℓS (Finset.mem_coe.mp h)) - ((W.apOfModel ℓ : ℤ) : CuspForm.heckeAlgebra N 2 (S : Set ℕ))
          ∈ RingHom.ker f𝔓 := by
      rw [hf𝔓, RingHom.sub_mem_ker_iff, map_intCast]
      exact hχ ℓ hℓ hℓN hℓS hgood
    have hmem' := (RingHom.sub_mem_ker_iff f𝔓).mp hmem
    rw [map_intCast f𝔓] at hmem'
    show algebraMap (integralClosure ℤ ℂ) ℂ (f𝔓 _) = _
    rw [hmem', map_intCast]

  obtain ⟨f, hf, hfT, -⟩ :=
    CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq hN χℂ

  have hN0 : N ≠ 0 := NeZero.ne N
  have hP0 : (∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => (hSprime q (Finset.mem_filter.mp hq).1).ne_zero
  haveI : NeZero (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) := ⟨mul_ne_zero hN0 hP0⟩
  obtain ⟨g, hg, hgf⟩ :=
    CuspForm.exists_isNormalizedEigenform_of_dvd (N := N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q)
      (dvd_mul_right N _) f hf
  refine ⟨g, hg, fun ℓ hℓ hgood hℓN' => ?_⟩
  have hℓN : ¬ ℓ ∣ N := fun h => hℓN' (h.mul_right _)
  have hℓS : ℓ ∉ S := fun h =>
    hℓN' ((Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_filter.mpr ⟨h, hℓN⟩)).mul_left N)
  rw [hgf ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN'), hfT ℓ hℓ hℓN (fun h => hℓS (Finset.mem_coe.mp h)),
    hχℂ ℓ hℓ hℓN hℓS hgood]

/-- **The unconditional `R ≅ T` assembly.** The pinned statement
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`, verbatim from
`Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`. The
three hypotheses SET 3 froze are discharged here: SET 6's
`Algebra.PatchingDatum.nonempty_patchingLevel_bot` supplies a patching level at
the zero ideal, and SET 4's `Algebra.PatchingLevel.free_and_ker_eq_span` supplies
the freeness, the vanishing annihilator and the kernel identification for it. -/
theorem WeierstrassCurve.isModularModelOfLevel_of_patchingDatum
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
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) := by
  obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hp𝒪
  obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span
  exact WeierstrassCurve.isModularModelOfLevel_of_patchingLevel p W hΔ hp𝒪 D hSprime hNS hN H
    φ hφ hφρ hcompat L hfree hann hker ρW h𝒟W hWres hWfrob
