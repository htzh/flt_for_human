/-
The differentials bridge: Kähler differentials to Weil differentials, the
regular-differentials submodule, and the linear equivalence onto `omegaSpace 0`,
after FLT's
`P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean`
(295 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean>).

Statements are transcribed textually from the pin; the public headline
`exists_linearEquiv_regularDifferentials_omegaSpace_zero` is spelled from its
`Theorems/Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean`
wrapper.  It is **conditional** on `(hC : ConstantsAreBase K F)` and
`(hRT : ResidueTheorem K F)` together with
`[HasCanonicalDivisor (K := K) (F := F)]`, exactly as the pin states it; none of
those is discharged here.

## Boundary: two helper targets, promoted in the refactor round

The pin's `S_` file imports the two wrappers
`Theorems/Thm_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean`
and `Theorems/Thm_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean`, whose
bodies live in
`P2M/Sol/S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean:9`
(18 ln) and
`P2M/Sol/S_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean:146–196`
(199 ln).  Neither name was in `rr_homes.txt` §H3 (the 25-row union), in Set D,
H1a, H1b or H2: the 14-`S_`-file measurement misses prerequisites that only the
targets' proofs reach (the same gap class the H2 friction entry records).  H3
therefore re-provisioned them `private` here, per PLAN-P1.md §2.  **The refactor round
has promoted them**: both now live publicly in `Defs/WeilOfKaehler.lean` (with the
pin-public support lemmas and the pin-`private` helpers), and this module imports
them.  No statement changed.
-/
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisorUniformizer
import FLTForHuman.AlgebraicCurve.Defs.LocalResidue
import FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem ord_nonneg_of_mem_vs {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · have hle : v.adicValuation f ≤ 1 := by
      rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have hlog : WithZero.log (v.adicValuation f) ≤ 0 := by
      rw [← WithZero.exp_zero] at hle
      exact (WithZero.log_le_iff_le_exp (v.adicValuation_ne_zero hf0)).mpr hle
    unfold Place.ord
    omega

theorem mem_vs_of_ord_nonneg {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem differentialCoeff_add_s2 (ω η : Ω[F⁄K]) :
    v.differentialCoeff (ω + η) = v.differentialCoeff ω + v.differentialCoeff η :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_smul_algebraMap_s2 (c : K) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = algebraMap K F c * v.differentialCoeff ω := by
  rw [← v.differentialCoeff_smul, algebraMap_smul]

end Place

theorem nonempty_place_of_constantsAreBase [Nontrivial Ω[F⁄K]] (hC : ConstantsAreBase K F) :
    Nonempty (Place K F) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsurj : Function.Surjective (algebraMap K F) := fun f => by
    have hf : f ∈ LSpace (0 : Divisor K F) := fun v => (IsEmpty.false v).elim
    rw [hC] at hf
    obtain ⟨c, hc⟩ := hf
    exact ⟨c, hc⟩
  have hrange : ∀ x ∈ Set.range (KaehlerDifferential.D K F), (x : Ω[F⁄K]) = 0 := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨c, rfl⟩ := hsurj f
    exact Derivation.map_algebraMap _ c
  have htop : (⊤ : Submodule F Ω[F⁄K]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    exact hrange
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have : x ∈ (⊥ : Submodule F Ω[F⁄K]) := htop ▸ Submodule.mem_top
  exact hx ((Submodule.mem_bot F).mp this)

/-! ## The residue-theorem half of the boundary helper (promoted)

`S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean` (18 ln),
statement from its `Theorems/` wrapper; now public in `Defs/WeilOfKaehler.lean`. -/

section Generic

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem canonicalDivisorOf_nonneg_of_mem_regularDifferentials {ω : Ω[F⁄K]} (hω0 : ω ≠ 0)
    (hω : ω ∈ regularDifferentials K F) : 0 ≤ canonicalDivisorOf hω0 := by
  refine Finsupp.le_def.mpr fun v => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, canonicalDivisorOf_apply]
  obtain ⟨g, hg, hωg⟩ := hω v
  show 0 ≤ v.ord (v.differentialCoeff ω)
  rw [v.differentialCoeff_unique hωg]
  exact v.ord_nonneg_of_mem_vs hg

theorem mem_regularDifferentials_of_canonicalDivisorOf_nonneg {ω : Ω[F⁄K]} (hω0 : ω ≠ 0)
    (h : 0 ≤ canonicalDivisorOf hω0) : ω ∈ regularDifferentials K F := by
  intro v
  refine ⟨v.differentialCoeff ω, ?_, (v.differentialCoeff_smul_dCoord ω).symm⟩
  apply v.mem_vs_of_ord_nonneg
  have hv := Finsupp.le_def.mp h v
  rw [Finsupp.coe_zero, Pi.zero_apply, canonicalDivisorOf_apply] at hv
  exact hv

theorem kaehlerResidueTerm_add_left_s2 (ω η : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (ω + η) α v = kaehlerResidueTerm ω α v + kaehlerResidueTerm η α v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_add_s2, mul_add, map_add, map_add]

theorem kaehlerResidueTerm_smul_left_s2 (c : K) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (c • ω) α v = c * kaehlerResidueTerm ω α v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul_algebraMap_s2, mul_left_comm, ← Algebra.smul_def, map_smul, map_smul,
    smul_eq_mul]

theorem kaehlerResidueTerm_zero_left_s2 (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (0 : Ω[F⁄K]) α v = 0 :=
  kaehlerResidueTerm_eq_zero_of_ord_nonneg (Or.inl (by rw [v.differentialCoeff_zero, mul_zero]))

theorem kaehlerResidueTerm_fsmul_left (f : F) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (f • ω) α v = kaehlerResidueTerm ω (mulAdele K f α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply, mul_left_comm, mul_assoc]

variable [HasPrincipalDivisors K F]

theorem kaehlerResidueTerm_support_finite_of_adeleSpace' (ω : Ω[F⁄K]) (α : adeleSpace K F) :
    (Function.support (kaehlerResidueTerm ω (α : Place K F → F))).Finite := by
  rcases eq_or_ne ω 0 with rfl | hω
  · refine Set.Finite.subset Set.finite_empty fun v hv => ?_
    exact hv (kaehlerResidueTerm_zero_left_s2 _ v)
  · exact kaehlerResidueTerm_support_finite_of_adeleSpace hω α.2

noncomputable def kaehlerToWeil (ω : Ω[F⁄K]) : Module.Dual K (adeleSpace K F) where
  toFun α := ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v
  map_add' α β := by
    rw [← finsum_add_distrib (kaehlerResidueTerm_support_finite_of_adeleSpace' ω α)
      (kaehlerResidueTerm_support_finite_of_adeleSpace' ω β)]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]
  map_smul' c α := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc,
      ← Algebra.smul_def, map_smul, map_smul]

theorem kaehlerToWeil_apply (ω : Ω[F⁄K]) (α : adeleSpace K F) :
    kaehlerToWeil ω α = ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v := rfl

theorem kaehlerToWeil_eq_weilOfKaehler {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    kaehlerToWeil ω = weilOfKaehler K F hω :=
  LinearMap.ext fun _ => rfl

theorem kaehlerToWeil_zero : kaehlerToWeil (0 : Ω[F⁄K]) = (0 : Module.Dual K (adeleSpace K F)) :=
  LinearMap.ext fun α => finsum_eq_zero_of_forall_eq_zero fun v => kaehlerResidueTerm_zero_left_s2 _ v

theorem kaehlerToWeil_add (ω η : Ω[F⁄K]) :
    kaehlerToWeil (ω + η) = (kaehlerToWeil ω + kaehlerToWeil η : Module.Dual K (adeleSpace K F)) := by
  refine LinearMap.ext fun α => ?_
  rw [LinearMap.add_apply, kaehlerToWeil_apply, kaehlerToWeil_apply, kaehlerToWeil_apply,
    ← finsum_add_distrib (kaehlerResidueTerm_support_finite_of_adeleSpace' ω α)
      (kaehlerResidueTerm_support_finite_of_adeleSpace' η α)]
  exact finsum_congr fun v => kaehlerResidueTerm_add_left_s2 ω η _ v

theorem kaehlerToWeil_smul (c : K) (ω : Ω[F⁄K]) :
    kaehlerToWeil (c • ω) = (c • kaehlerToWeil ω : Module.Dual K (adeleSpace K F)) := by
  refine LinearMap.ext fun α => ?_
  rw [LinearMap.smul_apply, kaehlerToWeil_apply, kaehlerToWeil_apply, smul_finsum]
  exact finsum_congr fun v => by rw [kaehlerResidueTerm_smul_left_s2, smul_eq_mul]

theorem weilSmul_kaehlerToWeil (f : F) (ω : Ω[F⁄K]) :
    weilSmul K F f (kaehlerToWeil ω) = kaehlerToWeil (f • ω) := by
  refine LinearMap.ext fun α => ?_
  rw [weilSmul_apply, kaehlerToWeil_apply, kaehlerToWeil_apply, adeleSpaceMul_coe]
  exact finsum_congr fun v => (kaehlerResidueTerm_fsmul_left f ω _ v).symm

noncomputable def kaehlerToWeilLinear : Ω[F⁄K] →ₗ[K] Module.Dual K (adeleSpace K F) where
  toFun := kaehlerToWeil
  map_add' := kaehlerToWeil_add
  map_smul' c ω := by rw [RingHom.id_apply, kaehlerToWeil_smul]

theorem kaehlerToWeil_mem_omegaSpace_zero (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) :
    kaehlerToWeil ω ∈ omegaSpace (K := K) (F := F) (0 : Divisor K F) := by
  rcases eq_or_ne ω 0 with rfl | h0
  · rw [kaehlerToWeil_zero]
    exact Submodule.zero_mem _
  · rw [kaehlerToWeil_eq_weilOfKaehler h0]
    exact omegaSpace_antitone (canonicalDivisorOf_nonneg_of_mem_regularDifferentials h0 hω)
      (weilOfKaehler_mem_omegaSpace_of_residueTheorem hRT h0)

noncomputable def regularToOmega (hRT : ResidueTheorem K F) :
    ↥(regularDifferentials K F) →ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)) :=
  LinearMap.codRestrict (omegaSpace (K := K) (F := F) (0 : Divisor K F))
    (kaehlerToWeilLinear.comp (regularDifferentials K F).subtype)
    (fun ω => kaehlerToWeil_mem_omegaSpace_zero hRT ω.2)

theorem coe_regularToOmega_apply (hRT : ResidueTheorem K F) (ω : ↥(regularDifferentials K F)) :
    ((regularToOmega hRT ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)))
      : Module.Dual K (adeleSpace K F)) = kaehlerToWeil (ω : Ω[F⁄K]) := rfl

end Generic

theorem exists_linearEquiv_regularDifferentials_omegaSpace_zero' {K : Type*} {F : Type*}
    [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K F))
          = weilOfKaehler K F hω := by
  haveI : HasSeparableResidue K F := hasSeparableResidue_of_perfectField
  haveI : Nonempty (Place K F) := nonempty_place_of_constantsAreBase hC
  have hinj : Function.Injective (regularToOmega (K := K) (F := F) hRT) := by
    intro ω η h
    apply Subtype.ext
    by_contra hne
    have hne' : (ω : Ω[F⁄K]) - (η : Ω[F⁄K]) ≠ 0 := sub_ne_zero.mpr hne
    have hval := congrArg (fun x : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)) =>
      (x : Module.Dual K (adeleSpace K F))) h
    simp only [coe_regularToOmega_apply] at hval
    have hzero : kaehlerToWeil ((ω : Ω[F⁄K]) - (η : Ω[F⁄K])) = (0 : Module.Dual K (adeleSpace K F)) := by
      rw [sub_eq_add_neg, kaehlerToWeil_add, ← neg_one_smul K (η : Ω[F⁄K]), kaehlerToWeil_smul,
        hval, neg_one_smul K (kaehlerToWeil (η : Ω[F⁄K])), add_neg_cancel]
    rw [kaehlerToWeil_eq_weilOfKaehler hne'] at hzero
    exact (weilOfKaehler_ne_zero_and_maximal hne').1 hzero
  have hsurj : Function.Surjective (regularToOmega (K := K) (F := F) hRT) := by
    rintro ⟨μ, hμ⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · exact ⟨0, Subtype.ext (by rw [coe_regularToOmega_apply, Submodule.coe_zero, kaehlerToWeil_zero])⟩
    obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
    have hmax := weilOfKaehler_ne_zero_and_maximal (K := K) (F := F) hω₀
    have hlmem : weilOfKaehler K F hω₀ ∈ weilDifferentialModule K F :=
      omegaSpace_le_weilDifferentialModule _ (weilOfKaehler_mem_omegaSpace_of_residueTheorem hRT hω₀)
    have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule _ hμ
    obtain ⟨f, hf, -⟩ := weilDifferentialRankOne_of_isCurveOver (K := K) (F := F) hC hlmem hmax.1 hμmem
    have hf0 : f ≠ 0 := by
      rintro rfl
      apply hμ0
      rw [hf]
      refine LinearMap.ext fun α => ?_
      rw [weilSmul_apply, LinearMap.zero_apply]
      have : adeleSpaceMul K F (0 : F) α = 0 :=
        Subtype.ext (funext fun v => by rw [adeleSpaceMul_coe, mulAdele_apply, zero_mul]; rfl)
      rw [this, map_zero]
    have hfω : f • ω₀ ≠ 0 := smul_ne_zero hf0 hω₀
    have hμ' : μ = kaehlerToWeil (f • ω₀) := by
      rw [hf, ← kaehlerToWeil_eq_weilOfKaehler hω₀, weilSmul_kaehlerToWeil]
    have hreg : f • ω₀ ∈ regularDifferentials K F := by
      refine mem_regularDifferentials_of_canonicalDivisorOf_nonneg hfω ?_
      refine (weilOfKaehler_ne_zero_and_maximal hfω).2 0 ?_
      rw [← kaehlerToWeil_eq_weilOfKaehler hfω, ← hμ']
      exact hμ
    exact ⟨⟨f • ω₀, hreg⟩, Subtype.ext (by rw [coe_regularToOmega_apply, ← hμ'])⟩
  refine ⟨LinearEquiv.ofBijective (regularToOmega hRT) ⟨hinj, hsurj⟩, fun ω hω => ?_⟩
  change ((regularToOmega hRT ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)))
      : Module.Dual K (adeleSpace K F)) = weilOfKaehler K F hω
  rw [coe_regularToOmega_apply, kaehlerToWeil_eq_weilOfKaehler hω]

theorem exists_linearEquiv_regularDifferentials_omegaSpace_zero {K : Type*} {F : Type*}
    [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K F))
          = weilOfKaehler K F hω :=
  exists_linearEquiv_regularDifferentials_omegaSpace_zero' hC hRT

end AlgebraicCurve

end
