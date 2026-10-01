/-
FinitePlaceResidue — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.UnitFinite

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential

namespace ValuationSubring

variable {F : Type*} [Field F]

private theorem ofPrime_congr {R : ValuationSubring F} {P Q : Ideal R}
    [P.IsPrime] [Q.IsPrime] (h : P = Q) : R.ofPrime P = R.ofPrime Q := by
  subst h; congr

theorem eq_top_of_idealOfLE_eq_bot {R S : ValuationSubring F} (h : R ≤ S)
    (hbot : idealOfLE R S h = ⊥) : S = ⊤ :=
  eq_top_of_idealOfLE_eq_bot_s12 h hbot

theorem idealOfLE_ne_bot_of_ne_top {R S : ValuationSubring F} (h : R ≤ S)
    (hS : S ≠ ⊤) : idealOfLE R S h ≠ ⊥ :=
  idealOfLE_ne_bot_of_ne_top_s12 h hS

theorem eq_of_isDiscreteValuationRing_of_le {R S : ValuationSubring F}
    [IsDiscreteValuationRing R] (h : R ≤ S) (hS : S ≠ ⊤) : R = S :=
  eq_of_isDiscreteValuationRing_of_le_s12 h hS

end ValuationSubring

namespace AlgebraicCurve

section DedekindModel

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_dedekindModel
    (hmodel : ValSubringDedekindModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_essFiniteType
    (valSubringEssFiniteType_of_dedekindModel hmodel)

end DedekindModel

open RationalFunctionField

theorem ordDifferentialWellDefined_ratFunc_of_perfectField (K : Type*) [Field K]
    [PerfectField K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'

  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'

  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section UnitFiniteDX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1DifferentialCoeffUnitFinite_dX :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp hp.separable
  · exact absurd rfl hvinf

end UnitFiniteDX

section MOneSimplePoleBounds

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

theorem ord_finitePlace_mOneAtom_mul_differentialCoeff
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord
        (p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀) = -1 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(finitePlace K hp).ord_mul hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀),
    ord_finitePlace_p1PrincipalPartAtom K hp hc hdeg 1,
    hunit (finitePlace K hp) (finitePlace_ne_placeInfty hp)]
  norm_num

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (p1PlaceInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    -1 ≤ (p1PlaceInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω₀) := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(p1PlaceInfty K).ord_mul hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero hω₀)]
  have h1 : 1 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c 1) :=
    one_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg le_rfl
  have hordD : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff ω₀) = -2 := hInfty
  omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀
      ∈ (finitePlace K hp).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (finitePlace K hp).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    rw [← (finitePlace K hp).poleSubmodule_one, Place.mem_poleSubmodule, pow_one]
    refine (finitePlace K hp).mem_of_ord_nonneg
      (mul_ne_zero (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀))) ?_
    rw [(finitePlace K hp).ord_mul (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀)),
      (finitePlace K hp).ord_uniformizer,
      ord_finitePlace_mOneAtom_mul_differentialCoeff K hω₀ hunit hp hc hdeg]
    omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (p1PlaceInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω₀
      ∈ (p1PlaceInfty K).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (p1PlaceInfty K).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    rw [← (p1PlaceInfty K).poleSubmodule_one, Place.mem_poleSubmodule, pow_one]
    refine (p1PlaceInfty K).mem_of_ord_nonneg
      (mul_ne_zero (p1PlaceInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero hω₀))) ?_
    rw [(p1PlaceInfty K).ord_mul (p1PlaceInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero hω₀)),
      (p1PlaceInfty K).ord_uniformizer]
    have h := ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one K hω₀ hInfty hp hc hdeg
    omega

end MOneSimplePoleBounds

section MOneSimplePoleRow

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

def P1PrincipalPartMOneSimplePoleCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff ω₀
        ∈ (finitePlace K hpirr).simplePoleSubmodule)
      (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω₀
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      + Algebra.trace K (p1PlaceInfty K).ResidueField
          ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = 0

end MOneSimplePoleRow

end AlgebraicCurve

end
