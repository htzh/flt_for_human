/-
Separating — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.TraceEngine

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential
open AlgebraicCurve.RationalFunctionField KaehlerDifferential

namespace IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_simple_inv (t : F) : K⟮t⁻¹⟯ = K⟮t⟯ := adjoin_simple_inv_s12 t

theorem algebraMap_comp_equivOfEq {S T : IntermediateField K F} (h : S = T) :
    (algebraMap T F).comp ((IntermediateField.equivOfEq h).toRingEquiv : S →+* T)
      = ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap S F) :=
  algebraMap_comp_equivOfEq_s12 h

theorem finiteDimensional_of_eq {S T : IntermediateField K F} (h : S = T)
    [FiniteDimensional ↥S F] : FiniteDimensional ↥T F :=
  finiteDimensional_of_eq_s12 h

theorem isSeparable_of_eq {S T : IntermediateField K F} (h : S = T)
    [Algebra.IsSeparable ↥S F] : Algebra.IsSeparable ↥T F :=
  isSeparable_of_eq_s12 h

theorem finiteDimensional_adjoin_inv (t : F) [FiniteDimensional K⟮t⟯ F] :
    FiniteDimensional K⟮t⁻¹⟯ F :=
  finiteDimensional_adjoin_inv_s12 t

theorem isSeparable_adjoin_inv (t : F) [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.IsSeparable K⟮t⁻¹⟯ F :=
  isSeparable_adjoin_inv_s12 t

end IntermediateField

namespace AlgebraicCurve

open scoped IntermediateField

section CharZeroSeparable

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isSeparable_of_charZero_of_finiteDimensional [CharZero K]
    (S : IntermediateField K F) [FiniteDimensional ↥S F] :
    Algebra.IsSeparable ↥S F :=
  haveI : CharZero ↥S := IntermediateField.charZero S
  Algebra.IsSeparable.of_integral ↥S F

theorem isSeparable_adjoin_of_charZero_of_finiteDimensional [CharZero K] (t : F)
    [FiniteDimensional K⟮t⟯ F] : Algebra.IsSeparable K⟮t⟯ F :=
  isSeparable_of_charZero_of_finiteDimensional K⟮t⟯

end CharZeroSeparable

section SeparatingTranscendentalCore

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendentalCore : Prop :=
  ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F

variable {K F}

theorem hasSeparatingTranscendental_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    HasSeparatingTranscendental K F := by
  obtain ⟨t, ht, hfin⟩ := h
  haveI : Algebra.IsSeparable K⟮t⟯ F :=
    isSeparable_adjoin_of_charZero_of_finiteDimensional t
  exact ⟨t, ht, hfin, ‹_›,
    IntermediateField.finiteDimensional_adjoin_inv t,
    IntermediateField.isSeparable_adjoin_inv t⟩

theorem valSubringKaehlerFinite_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (hasSeparatingTranscendental_of_core h)

end SeparatingTranscendentalCore

section MonicRatioResidue

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

open RationalFunctionField

theorem ord_placeInfty_X_pow_natDegree_div {p : K[X]} (hp : p ≠ 0) :
    (p1PlaceInfty K).ord
        (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd : (X ^ p.natDegree : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hXd
  rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul hXd' (inv_ne_zero hp'),
    (p1PlaceInfty K).ord_inv, ord_placeInfty_algebraMap' K hXd, ord_placeInfty_algebraMap' K hp,
    natDegree_X_pow]
  ring

theorem X_pow_natDegree_div_mem_placeInfty {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
      ∈ (p1PlaceInfty K).toValuationSubring := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
      (pow_ne_zero _ X_ne_zero)
  exact (p1PlaceInfty K).mem_of_ord_nonneg (div_ne_zero hXd' hp')
    (ord_placeInfty_X_pow_natDegree_div K hp).ge

theorem degree_X_pow_natDegree_sub_lt_of_monic {p : K[X]} (hpmon : p.Monic) :
    ((X : K[X]) ^ p.natDegree - p).degree < p.degree := by
  have hdeg : ((X : K[X]) ^ p.natDegree).degree = p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpmon.ne_zero]
  refine (Polynomial.degree_sub_lt_left hdeg (pow_ne_zero _ X_ne_zero) ?_).trans_le hdeg.le
  rw [Polynomial.leadingCoeff_X_pow, hpmon]

end MonicRatioResidue

end AlgebraicCurve


open scoped IntermediateField Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

open KaehlerDifferential Module IntermediateField

namespace AlgebraicCurve

open RationalFunctionField

section MonicRatioResidueChunk4

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem residue_placeInfty_X_pow_natDegree_div_monic_eq_one {p : K[X]} (hpmon : p.Monic) :
    IsLocalRing.residue _ ⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
      = (1 : (p1PlaceInfty K).ResidueField) := by
  rw [← sub_eq_zero, show (1 : (p1PlaceInfty K).ResidueField) = IsLocalRing.residue _ 1 from
      (map_one _).symm, ← map_sub, IsLocalRing.residue_eq_zero_iff]

  set d := p.natDegree
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpmon.ne_zero

  have hsubmem : algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
      ∈ (p1PlaceInfty K).toValuationSubring := by
    rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
    · simp only [h0, _root_.map_zero, zero_div]; exact zero_mem _
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    refine (p1PlaceInfty K).mem_of_ord_nonneg (div_ne_zero h0' hp') ?_
    rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul h0' (inv_ne_zero hp'),
      (p1PlaceInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega
  have hcoe : (⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
        - 1 : (p1PlaceInfty K).toValuationSubring)
      = ⟨_, hsubmem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) (X ^ d) / algebraMap K[X] (RatFunc K) p - 1
      = algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
    rw [map_sub, sub_div, div_self hp']
  rw [hcoe, Place.mk_mem_maximalIdeal_iff]
  rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
  · exact .inl (by simp [h0])
  · refine .inr ?_
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul h0' (inv_ne_zero hp'),
      (p1PlaceInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega

end MonicRatioResidueChunk4

section NamedCarrier

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1PlaceInftySimplePoleResidueEulerValueX : Prop :=
  ∀ (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarrier

section MonicRatioReduction

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1MonomialAtom_eq_monicRatio_mul {p : K[X]} (hpdeg : 1 ≤ p.natDegree) :
    p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1
            * (p1PlaceInfty K).differentialCoeff (dX K)) := by
  show algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) / algebraMap K[X] (RatFunc K) p ^ 1
        * (p1PlaceInfty K).differentialCoeff (dX K)
    = algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
        * (algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
            * (p1PlaceInfty K).differentialCoeff (dX K))
  have hXd : algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
      = algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) * algebraMap K[X] (RatFunc K) X := by
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hpdeg]
  have hX0 : algebraMap K[X] (RatFunc K) (X : K[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr X_ne_zero
  rw [pow_one, pow_one, map_one, hXd, one_div]
  field_simp

theorem p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty
    (hInfty : (p1PlaceInfty K).ordDifferential (dX K) = -2) :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule :=
  p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K (dX_ne_zero K) hInfty
    irreducible_X 1 (by rw [degree_one, degree_X]; decide)

theorem simplePoleResidueAux_placeInfty_monomial_eq_X
    (hInfty : (p1PlaceInfty K).ordDifferential (dX K) = -2)
    {p : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    (p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩
      = (p1PlaceInfty K).simplePoleResidueAux
          ⟨_, p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty⟩ := by
  set hXmem := p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty

  have hfact := p1MonomialAtom_eq_monicRatio_mul K hpirr.natDegree_pos
  have hRatioMem := X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero
  have hprodmem : (algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
          / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K))
      ∈ (p1PlaceInfty K).simplePoleSubmodule :=
    (p1PlaceInfty K).mul_mem_simplePoleSubmodule_of_mem hRatioMem hXmem
  have heq : (⟨_, himem⟩ : (p1PlaceInfty K).simplePoleSubmodule) = ⟨_, hprodmem⟩ :=
    Subtype.ext hfact
  rw [heq, (p1PlaceInfty K).simplePoleResidueAux_mul_of_mem hRatioMem hXmem,
    residue_placeInfty_X_pow_natDegree_div_monic_eq_one K hpmon, one_mul]

theorem p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X
    (hInfty : (p1PlaceInfty K).ordDifferential (dX K) = -2)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K := by
  intro p hpmon hpirr himem
  rw [simplePoleResidueAux_placeInfty_monomial_eq_X K hInfty hpmon hpirr himem]
  exact hX _

end MonicRatioReduction

section ComposedEngineInftyX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyX
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hX)

end ComposedEngineInftyX

end AlgebraicCurve

end
