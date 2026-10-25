/-
The canonical divisor of a curve over a perfect field.

`AlgebraicCurve.HasCanonicalDivisor K F` says every nonzero differential has a divisor
whose value at a place is the order of the differential there. The construction: at each
place `dπ` spans `Ω` (`Canonical/DCoordGenerates.lean`), so `Df = c • dπ` with `c` in the
valuation ring; two uniformisers are compared by a unit
(`exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver`), which is what makes the coefficient
canonical — that coefficient statement, `exists_mem_D_eq_smul_D_of_isCurveOver`, is homed
with its `Theorems/` wrapper in `Differential/Coefficient.lean`; the orders of the
coefficients of a nontrivial differential have finite support below zero
(`finite_ordDifferential_D_ne_zero`, over `mem_span_D_adjoin` and the unramified
criterion `span_D_eq_top_of_isUnramifiedAt`); and
`hasCanonicalDivisor_of_generator_finiteSupport` turns that into a divisor. The headline
closes the chain for `IsCurveOver K F`.

The headline `AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver` carries the pin's proof
(the `S_` file's copy of the statement is the same statement, so the port keeps one
declaration, at the `Theorems/` wrapper's name), and `dCoordGenerates_of_isCurveOver` (the
`Theorems/` file of the previous module) is applied inside.

After FLT's `P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean` (1,723 ln,
second half), pinned at `aa2d8b3`: <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean>.

Assumes `Canonical/DCoordGenerates.lean`.

spec-pin: Theorems/Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain Polynomial IsLocalRing KaehlerDifferential IntermediateField
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.Place

namespace AlgebraicCurve

section S12WellDefined

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ValSubringKaehlerSpanTop K F :=
  haveI : ∀ v : Place K F,
      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=
    isSeparable_residueField_forall_of_perfectField
  valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable
    (valSubringKaehlerFinite_of_finiteTypeModel
      (valSubringFiniteTypeModel_of_dedekindModel
        (valSubringDedekindModel_of_hasSeparatingTranscendental
          (hasSeparatingTranscendental_of_isCurveOver_of_perfectField (K := K) (F := F)))))

namespace Place

variable (v : Place K F)

theorem ord_uniformizerSubring : v.ord (uniformizerSubring v : F) = 1 :=
  v.ord_coe_irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

theorem dCoord_eq_D_uniformizerSubring :
    v.dCoord = KaehlerDifferential.D K F (uniformizerSubring v : F) := rfl

theorem exists_mem_D_eq_smul_dCoord (hspan : ValSubringKaehlerSpanTop K F)
    {x : F} (hx : x ∈ v.toValuationSubring) :
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • v.dCoord := by
  have hmem : KaehlerDifferential.D K v.toValuationSubring (⟨x, hx⟩ : v.toValuationSubring)
      ∈ Submodule.span v.toValuationSubring
          {KaehlerDifferential.D K v.toValuationSubring (uniformizerSubring v)} := by
    rw [hspan v]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨(c : F), c.2, ?_⟩
  have h := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hc
  rw [LinearMap.map_smul_of_tower, v.kaehlerMap_subring_D_uniformizer, KaehlerDifferential.map_D] at h
  calc KaehlerDifferential.D K F x
      = KaehlerDifferential.D K F (algebraMap v.toValuationSubring F ⟨x, hx⟩) := rfl
    _ = c • v.dCoord := h.symm
    _ = (c : F) • v.dCoord := (algebraMap_smul F c v.dCoord).symm

theorem exists_unit_D_eq_smul_dCoord (hspan : ValSubringKaehlerSpanTop K F)
    [Nontrivial Ω[F⁄K]] [v.DCoordGenerates] {ϖ : F} (hϖ : v.ord ϖ = 1) :
    ∃ w : F, w ≠ 0 ∧ v.ord w = 0 ∧ KaehlerDifferential.D K F ϖ = w • v.dCoord := by
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, v.ord_zero] at hϖ; exact zero_ne_one hϖ
  have hϖmem : ϖ ∈ v.toValuationSubring := v.mem_vs_of_ord_nonneg (by rw [hϖ]; exact zero_le_one)
  obtain ⟨c, hc, hDϖ⟩ := v.exists_mem_D_eq_smul_dCoord hspan hϖmem
  set π₀ : F := (uniformizerSubring v : F) with hπ₀
  have hπ₀ord : v.ord π₀ = 1 := v.ord_uniformizerSubring
  have hπ₀0 : π₀ ≠ 0 := fun h => by rw [h, v.ord_zero] at hπ₀ord; exact zero_ne_one hπ₀ord
  set a : F := π₀ / ϖ with ha
  have ha0 : a ≠ 0 := div_ne_zero hπ₀0 hϖ0
  have haord : v.ord a = 0 := by
    rw [ha, div_eq_mul_inv, v.ord_mul hπ₀0 (inv_ne_zero hϖ0), v.ord_inv, hπ₀ord, hϖ]; ring
  have hamem : a ∈ v.toValuationSubring := v.mem_vs_of_ord_nonneg haord.ge
  obtain ⟨d, hd, hDa⟩ := v.exists_mem_D_eq_smul_dCoord hspan hamem
  have hπ₀eq : π₀ = a * ϖ := by rw [ha, div_mul_cancel₀ _ hϖ0]
  have hD : v.dCoord = (a * c + ϖ * d) • v.dCoord := by
    conv_lhs => rw [v.dCoord_eq_D_uniformizerSubring, ← hπ₀, hπ₀eq, Derivation.leibniz, hDϖ, hDa]
    rw [smul_smul, smul_smul, ← add_smul, mul_comm ϖ d]
  have hone : a * c + ϖ * d = 1 := by
    have h1 : (1 - (a * c + ϖ * d)) • v.dCoord = 0 := by rw [sub_smul, one_smul, ← hD, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h v.dCoord_ne_zero

  have hacmem : a * c ∈ v.toValuationSubring := mul_mem hamem hc
  have hunit : IsUnit (⟨a * c, hacmem⟩ : v.toValuationSubring) := by
    by_contra hnu
    have hmax : (⟨a * c, hacmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hϖmax : (⟨ϖ, hϖmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (v.mem_maximalIdeal_iff_ord_pos hϖ0 hϖmem).mpr (by rw [hϖ]; exact one_pos)
    have h1 : (1 : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      have : (1 : v.toValuationSubring)
          = ⟨a * c, hacmem⟩ + ⟨ϖ, hϖmem⟩ * ⟨d, hd⟩ := Subtype.ext (by
            show (1 : F) = a * c + ϖ * d
            exact hone.symm)
      rw [this]
      exact add_mem hmax (Ideal.mul_mem_right _ _ hϖmax)
    exact (IsLocalRing.maximalIdeal.isMaximal v.toValuationSubring).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  have hacord : v.ord (a * c) = 0 := by
    have := v.ord_coe_unit hunit.unit
    rwa [IsUnit.unit_spec] at this
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : (⟨a * c, hacmem⟩ : v.toValuationSubring) = 0 := Subtype.ext (by simp [h0])
    rw [hz] at hunit
    exact not_isUnit_zero hunit
  have hcord : v.ord c = 0 := by
    rw [v.ord_mul ha0 hc0, haord, zero_add] at hacord
    exact hacord
  exact ⟨c, hc0, hcord, hDϖ⟩

theorem exists_ord_eq_zero_D_eq_smul_D (hspan : ValSubringKaehlerSpanTop K F)
    [Nontrivial Ω[F⁄K]] [v.DCoordGenerates]
    (π π' : F) (hπ : v.ord π = 1) (hπ' : v.ord π' = 1) :
    ∃ u : F, v.ord u = 0 ∧ KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π := by
  obtain ⟨w, hw0, hw, hDπ⟩ := v.exists_unit_D_eq_smul_dCoord hspan hπ
  obtain ⟨w', hw0', hw', hDπ'⟩ := v.exists_unit_D_eq_smul_dCoord hspan hπ'
  refine ⟨w' / w, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hw0' (inv_ne_zero hw0), v.ord_inv, hw', hw]; ring
  · rw [hDπ', hDπ, smul_smul, div_mul_cancel₀ _ hw0]

end Place

theorem exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) (π π' : F) (hπ : v.ord π = 1) (hπ' : v.ord π' = 1) :
    ∃ u : F, v.ord u = 0 ∧ KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π := by
  have hspan := valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField (K := K) (F := F)
  haveI : v.DCoordGenerates := Place.dCoordGenerates_of_valSubringKaehlerSpanTop hspan v
  exact v.exists_ord_eq_zero_D_eq_smul_D hspan π π' hπ hπ'

end S12WellDefined

end AlgebraicCurve

namespace AlgebraicCurve

section S12HCD

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open KaehlerDifferential IntermediateField Polynomial

theorem hasCanonicalDivisor_of_generator_finiteSupport
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hgen : Submodule.span F ({ω₀} : Set Ω[F⁄K]) = ⊤)
    (hfin : {v : Place K F | v.ordDifferential ω₀ ≠ 0}.Finite) :
    HasCanonicalDivisor (K := K) (F := F) := by
  classical
  refine ⟨fun ω hω => ?_⟩
  have hmem : ω ∈ Submodule.span F ({ω₀} : Set Ω[F⁄K]) := by rw [hgen]; exact Submodule.mem_top
  obtain ⟨g, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have hg : g ≠ 0 := by rintro rfl; exact hω (zero_smul _ _)
  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  refine ⟨Dg + Finsupp.onFinset hfin.toFinset (fun v => v.ordDifferential ω₀)
      (fun v hv => hfin.mem_toFinset.mpr hv), fun v => ?_⟩
  rw [Finsupp.add_apply, Finsupp.onFinset_apply, hDg v]
  have hc : v.differentialCoeff ω₀ ≠ 0 := by
    intro h0; apply hω₀; rw [← v.differentialCoeff_smul_dCoord ω₀, h0, zero_smul]
  exact (v.ordDifferential_smul hg hc).symm

namespace Place

open scoped AlgebraicCurve.Place in
private theorem ordDifferential_D_eq_zero_of_span_eq_top (hspan : ValSubringKaehlerSpanTop K F)
    [Nontrivial Ω[F⁄K]] (v : Place K F) [v.DCoordGenerates]
    (s : v.toValuationSubring)
    (hs : Submodule.span v.toValuationSubring
      ({KaehlerDifferential.D K v.toValuationSubring s} : Set Ω[v.toValuationSubring⁄K]) = ⊤) :
    v.ordDifferential (KaehlerDifferential.D K F (s : F)) = 0 := by
  have h1mem : KaehlerDifferential.D K v.toValuationSubring s
      ∈ Submodule.span v.toValuationSubring
        ({KaehlerDifferential.D K v.toValuationSubring (uniformizerSubring v)} : Set Ω[v.toValuationSubring⁄K]) := by
    rw [hspan v]; exact Submodule.mem_top
  have h2mem : KaehlerDifferential.D K v.toValuationSubring (uniformizerSubring v)
      ∈ Submodule.span v.toValuationSubring
        ({KaehlerDifferential.D K v.toValuationSubring s} : Set Ω[v.toValuationSubring⁄K]) := by
    rw [hs]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1mem
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp h2mem
  have h1 : KaehlerDifferential.D K F (s : F) = (c : F) • v.dCoord := by
    have h := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hc
    rw [LinearMap.map_smul_of_tower, v.kaehlerMap_subring_D_uniformizer, KaehlerDifferential.map_D] at h
    calc KaehlerDifferential.D K F (s : F)
        = KaehlerDifferential.D K F (algebraMap v.toValuationSubring F s) := rfl
      _ = c • v.dCoord := h.symm
      _ = (c : F) • v.dCoord := (algebraMap_smul F c v.dCoord).symm
  have h2 : v.dCoord = (c' : F) • KaehlerDifferential.D K F (s : F) := by
    have h := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hc'
    rw [LinearMap.map_smul_of_tower, KaehlerDifferential.map_D, v.kaehlerMap_subring_D_uniformizer] at h
    calc v.dCoord = c' • KaehlerDifferential.D K F (algebraMap v.toValuationSubring F s) := h.symm
      _ = (c' : F) • KaehlerDifferential.D K F (s : F) := (algebraMap_smul F c' _).symm
  have hcc : (c' : F) * c = 1 := by
    have h3 : (1 - (c' : F) * c) • v.dCoord = 0 := by
      rw [sub_smul, one_smul, mul_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h v.dCoord_ne_zero
  have hc0 : (c : F) ≠ 0 := fun h => by rw [h, mul_zero] at hcc; exact zero_ne_one hcc
  have hc'0 : (c' : F) ≠ 0 := fun h => by rw [h, zero_mul] at hcc; exact zero_ne_one hcc
  have hcord : v.ord (c : F) = 0 := by
    have hsum : v.ord (c' : F) + v.ord (c : F) = 0 := by rw [← v.ord_mul hc'0 hc0, hcc, v.ord_one]
    have h4 := v.ord_nonneg_of_mem_vs c.2
    have h5 := v.ord_nonneg_of_mem_vs c'.2
    omega
  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F (s : F)) = c :=
    v.differentialCoeff_unique h1
  show v.ord (v.differentialCoeff _) = 0
  rw [hcoeff]; exact hcord

end Place

theorem mem_span_D_adjoin (t : F) (ω : Ω[↥(Algebra.adjoin K ({t} : Set F))⁄K]) :
    ω ∈ Submodule.span ↥(Algebra.adjoin K ({t} : Set F))
      ({KaehlerDifferential.D K ↥(Algebra.adjoin K ({t} : Set F))
        ⟨t, Algebra.self_mem_adjoin_singleton K t⟩} : Set Ω[↥(Algebra.adjoin K ({t} : Set F))⁄K]) := by
  have htop : ω ∈ Submodule.span ↥(Algebra.adjoin K ({t} : Set F))
      (Set.range (KaehlerDifferential.D K ↥(Algebra.adjoin K ({t} : Set F)))) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  refine Submodule.span_le.mpr ?_ htop
  rintro _ ⟨r, rfl⟩
  have hr : (r : F) ∈ (Polynomial.aeval (R := K) t).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
  obtain ⟨Q, hQ⟩ := hr
  have hr' : r = Polynomial.aeval (⟨t, Algebra.self_mem_adjoin_singleton K t⟩ : Algebra.adjoin K ({t} : Set F)) Q := by
    apply Subtype.ext
    show (r : F) = (Algebra.adjoin K ({t} : Set F)).val (Polynomial.aeval _ Q)
    rw [← Polynomial.aeval_algHom_apply]
    exact hQ.symm
  rw [hr', Derivation.map_aeval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

namespace Place

open scoped AlgebraicCurve.Place in
private theorem span_D_eq_top_of_isUnramifiedAt (v : Place K F) (T : Subalgebra K F)
    (hT : (T : Set F) ⊆ (v.toValuationSubring : Set F))
    {t : F} (hRT : Algebra.adjoin K ({t} : Set F) ≤ T)
    [IsDedekindDomain T] [IsFractionRing T F]
    (hunr : letI : Algebra ↥(Algebra.adjoin K ({t} : Set F)) T := (Subalgebra.inclusion hRT).toRingHom.toAlgebra
      Algebra.IsUnramifiedAt ↥(Algebra.adjoin K ({t} : Set F)) (v.centerIdeal T hT)) :
    Submodule.span v.toValuationSubring
      ({KaehlerDifferential.D K v.toValuationSubring
        ⟨t, hT (hRT (Algebra.self_mem_adjoin_singleton K t))⟩} : Set Ω[v.toValuationSubring⁄K]) = ⊤ := by
  letI iRT : Algebra ↥(Algebra.adjoin K ({t} : Set F)) T := (Subalgebra.inclusion hRT).toRingHom.toAlgebra
  letI iTO : Algebra T v.toValuationSubring := v.modelAlgebra T hT
  letI iRO : Algebra ↥(Algebra.adjoin K ({t} : Set F)) v.toValuationSubring :=
    ((algebraMap T v.toValuationSubring).comp (algebraMap ↥(Algebra.adjoin K ({t} : Set F)) T)).toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin K ({t} : Set F)) T v.toValuationSubring :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K ↥(Algebra.adjoin K ({t} : Set F)) v.toValuationSubring :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  haveI hloc := v.isLocalization_centerIdeal_of_isDedekindDomain T hT
  haveI : Algebra.FormallyUnramified ↥(Algebra.adjoin K ({t} : Set F))
      (Localization.AtPrime (v.centerIdeal T hT)) := hunr
  let e : Localization.AtPrime (v.centerIdeal T hT) ≃ₐ[T] v.toValuationSubring :=
    IsLocalization.algEquiv (v.centerIdeal T hT).primeCompl _ _
  haveI : Algebra.FormallyUnramified ↥(Algebra.adjoin K ({t} : Set F)) v.toValuationSubring :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars ↥(Algebra.adjoin K ({t} : Set F)))
  haveI hsub : Subsingleton Ω[v.toValuationSubring⁄↥(Algebra.adjoin K ({t} : Set F))] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hrange : LinearMap.range
      (KaehlerDifferential.mapBaseChange K ↥(Algebra.adjoin K ({t} : Set F)) v.toValuationSubring) = ⊤ := by
    rw [KaehlerDifferential.range_mapBaseChange]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  have htO : algebraMap ↥(Algebra.adjoin K ({t} : Set F)) v.toValuationSubring
      ⟨t, Algebra.self_mem_adjoin_singleton K t⟩
        = ⟨t, hT (hRT (Algebra.self_mem_adjoin_singleton K t))⟩ := Subtype.ext rfl
  have hle : LinearMap.range
      (KaehlerDifferential.mapBaseChange K ↥(Algebra.adjoin K ({t} : Set F)) v.toValuationSubring)
      ≤ Submodule.span v.toValuationSubring
        ({KaehlerDifferential.D K v.toValuationSubring
          ⟨t, hT (hRT (Algebra.self_mem_adjoin_singleton K t))⟩} : Set Ω[v.toValuationSubring⁄K]) := by
    rintro _ ⟨x, rfl⟩
    refine TensorProduct.inductionOn x ?_ ?_
    · intro b ω
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (mem_span_D_adjoin t ω)
      rw [← hr, LinearMap.map_smul_of_tower, KaehlerDifferential.map_D, htO]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · intro x y hx hy
      rw [map_add]; exact add_mem hx hy
  exact top_le_iff.mp (hrange ▸ hle)

end Place

open scoped AlgebraicCurve.Place in
theorem Place.eq_of_centerIdeal_eq (T : Subalgebra K F) [IsDedekindDomain T] [IsFractionRing T F]
    {v₁ v₂ : Place K F} (h₁ : (T : Set F) ⊆ (v₁.toValuationSubring : Set F))
    (h₂ : (T : Set F) ⊆ (v₂.toValuationSubring : Set F))
    (hP : v₁.centerIdeal T h₁ = v₂.centerIdeal T h₂) : v₁ = v₂ := by
  have hle : v₁.centerLocalizationValuationSubring T h₁ ≤ v₂.toValuationSubring := by
    intro x hx
    change x ∈ (v₁.centerLocalizationSubalgebra T h₁ : Subalgebra T F) at hx
    obtain ⟨a, s, hs, rfl⟩ := hx
    rw [← div_eq_mul_inv]
    exact div_mem_of_not_mem_centerIdeal v₂ T h₂ a (hP ▸ hs)
  have heq := ValuationSubring.eq_of_isDiscreteValuationRing_of_le hle v₂.ne_top'
  rw [v₁.centerLocalizationValuationSubring_eq T h₁] at heq
  cases v₁; cases v₂
  congr

theorem adjoin_le_transcendentalChart (t : F) :
    Algebra.adjoin K ({t} : Set F) ≤ transcendentalChart K t := by
  intro x hx
  show x ∈ integralClosure ↥(Algebra.adjoin K ({t} : Set F)) F
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := ↥(Algebra.adjoin K ({t} : Set F))) (A := F) (x := ⟨x, hx⟩)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem finite_ordDifferential_D_ne_zero (hspan : ValSubringKaehlerSpanTop K F)
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [PerfectField K]
    {t : F} (htr : Transcendental K t) [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    {v : Place K F | v.ordDifferential (KaehlerDifferential.D K F t) ≠ 0}.Finite := by
  classical
  have ht0 : t ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have hRT : Algebra.adjoin K ({t} : Set F) ≤ transcendentalChart K t := adjoin_le_transcendentalChart t
  obtain ⟨hft, hded, hfrac⟩ := isAffineChart_transcendentalChart (K := K) htr
  haveI : IsDedekindDomain ↥(transcendentalChart K t) := hded
  haveI : IsFractionRing ↥(transcendentalChart K t) F := hfrac
  letI iRT : Algebra ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) :=
    (Subalgebra.inclusion hRT).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsPrincipalIdealRing ↥(Algebra.adjoin K ({t} : Set F)) := isPrincipalIdealRing_adjoin htr
  haveI : IsDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) := isDedekindDomain_adjoin htr
  have hinj : Function.Injective (algebraMap ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t)) :=
    Subalgebra.inclusion_injective hRT
  haveI : FaithfulSMul ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : Module.IsTorsionFree ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c x h
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  haveI : Module.Finite ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) :=
    moduleFinite_integralClosure_adjoin (K := K) htr
  haveI : Algebra.EssFiniteType ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) :=
    inferInstance
  haveI : FaithfulSMul ↥(Algebra.adjoin K ({t} : Set F)) (FractionRing ↥(transcendentalChart K t)) :=
    inferInstance
  haveI : Algebra.IsSeparable (FractionRing ↥(Algebra.adjoin K ({t} : Set F)))
      (FractionRing ↥(transcendentalChart K t)) := by
    let e₁ : FractionRing ↥(Algebra.adjoin K ({t} : Set F)) ≃ₐ[↥(Algebra.adjoin K ({t} : Set F))] K⟮t⟯ :=
      FractionRing.algEquiv _ K⟮t⟯
    let e₂ : FractionRing ↥(transcendentalChart K t) ≃ₐ[↥(transcendentalChart K t)] F :=
      FractionRing.algEquiv _ F
    refine Algebra.IsSeparable.of_equiv_equiv e₁.symm.toRingEquiv e₂.symm.toRingEquiv ?_
    ext r
    exact IsFractionRing.algEquiv_commutes e₁.symm e₂.symm r

  have hdiff : differentIdeal ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t) ≠ ⊥ :=
    differentIdeal_ne_bot
  have hfinP : {P : IsDedekindDomain.HeightOneSpectrum ↥(transcendentalChart K t) |
      P.asIdeal ∣ differentIdeal ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t)}.Finite :=
    Ideal.finite_factors hdiff

  obtain ⟨Dt, hDt, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) t ht0
  have hpole : {v : Place K F | v.ord t < 0}.Finite := by
    refine (Dt.support.finite_toSet).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff] at hv ⊢
    rw [hDt v]; omega
  have hsub : ∀ v : Place K F, 0 ≤ v.ord t →
      ((transcendentalChart K t : Subalgebra K F) : Set F) ⊆ (v.toValuationSubring : Set F) := by
    intro v hv
    exact transcendentalChart_subset_valuationSubring_of_mem v (v.mem_vs_of_ord_nonneg hv)

  have key : ∀ (v : Place K F) (hv : 0 ≤ v.ord t),
      ¬ ((v.centerIdeal (transcendentalChart K t) (hsub v hv)) ∣
          differentIdeal ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t)) →
      v.ordDifferential (KaehlerDifferential.D K F t) = 0 := by
    intro v hv hndvd
    have hunr := (not_dvd_differentIdeal_iff (A := ↥(Algebra.adjoin K ({t} : Set F)))
      (B := ↥(transcendentalChart K t))).mp hndvd
    have hs := v.span_D_eq_top_of_isUnramifiedAt (transcendentalChart K t) (hsub v hv) hRT hunr
    exact v.ordDifferential_D_eq_zero_of_span_eq_top hspan
      ⟨t, (hsub v hv) (hRT (Algebra.self_mem_adjoin_singleton K t))⟩ hs

  have hS₂ : {v : Place K F | ∃ hv : 0 ≤ v.ord t, (v.centerIdeal (transcendentalChart K t) (hsub v hv)) ∣
      differentIdeal ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t)}.Finite := by
    haveI := hfinP.to_subtype
    let g : {v : Place K F | ∃ hv : 0 ≤ v.ord t, (v.centerIdeal (transcendentalChart K t) (hsub v hv)) ∣
        differentIdeal ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t)} →
        {P : IsDedekindDomain.HeightOneSpectrum ↥(transcendentalChart K t) |
          P.asIdeal ∣ differentIdeal ↥(Algebra.adjoin K ({t} : Set F)) ↥(transcendentalChart K t)} :=
      fun x => ⟨⟨x.1.centerIdeal (transcendentalChart K t) (hsub x.1 x.2.1), inferInstance,
        x.1.centerIdeal_ne_bot_of_isFractionRing (transcendentalChart K t) (hsub x.1 x.2.1)⟩, x.2.2⟩
    have hg : Function.Injective g := by
      rintro ⟨v₁, hv₁, hd₁⟩ ⟨v₂, hv₂, hd₂⟩ h
      have hP := congrArg (fun P => P.1.asIdeal) h
      exact Subtype.ext (Place.eq_of_centerIdeal_eq (transcendentalChart K t) _ _ hP)
    haveI := Finite.of_injective g hg
    exact Set.toFinite _
  refine (hpole.union hS₂).subset ?_
  intro v hv
  by_cases h0 : 0 ≤ v.ord t
  · right
    by_contra hnot
    exact hv (key v h0 (fun hd => hnot ⟨h0, hd⟩))
  · left
    exact lt_of_not_ge h0

end S12HCD

end AlgebraicCurve

namespace AlgebraicCurve

theorem hasCanonicalDivisor_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) := by
  have hspan := valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField (K := K) (F := F)
  haveI : ∀ v : Place K F, v.DCoordGenerates := fun v =>
    Place.dCoordGenerates_of_valSubringKaehlerSpanTop hspan v
  obtain ⟨t, htr, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfd
  haveI := hsep
  exact hasCanonicalDivisor_of_generator_finiteSupport
    (KaehlerDifferential.D_ne_zero_of_transcendental K t htr)
    (KaehlerDifferential.span_D_eq_top_of_transcendental K t htr)
    (finite_ordDifferential_D_ne_zero hspan htr)

end AlgebraicCurve

end
