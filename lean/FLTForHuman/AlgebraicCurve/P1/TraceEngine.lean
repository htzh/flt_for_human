/-
TraceEngine — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.FinitePlaceResidue

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential

namespace ModularCurve

section Corollaries

variable (K : Type*) [Field K]

scoped instance instHasPrincipalDivisorsRatFuncSelf : AlgebraicCurve.HasPrincipalDivisors K (RatFunc K) :=
  AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors_of_isGalois
    (AlgebraicCurve.ramificationInertiaIdentity_of_finiteDimensional K (RatFunc K) (RatFunc K))

end Corollaries

end ModularCurve

namespace AlgebraicCurve

section TraceRow

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

def P1FinitePlaceCanonicalResidueAtomMGeTwoTrace : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 2 ≤ m →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      Algebra.trace K (finitePlace K hpirr).ResidueField
          (R.res (p1PrincipalPartAtom K p c m
            * (finitePlace K hpirr).differentialCoeff (dX K))) = 0

def P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p),
    c.degree < p.degree → 2 ≤ m → 2 ≤ p.natDegree →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      Algebra.trace K (finitePlace K hpirr).ResidueField
          (R.res (p1PrincipalPartAtom K p c m
            * (finitePlace K hpirr).differentialCoeff (dX K))) = 0

end TraceRow

section Monotonicity

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg
    (h : P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg K) :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K :=
  fun p c m hpmon hpirr hdeg hm hpdeg R => by
    rw [h p c m hpmon hpirr hdeg hm hpdeg R, _root_.map_zero]

end Monotonicity

section DegOneDischargeTrace

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hcdeg : c.degree < p.degree) (hm : 2 ≤ m) (hdeg : p.natDegree = 1)
    (R : (finitePlace K hpirr).CanonicalLocalResidueDataK) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        (R.res (p1PrincipalPartAtom K p c m
          * (finitePlace K hpirr).differentialCoeff (dX K))) = 0 := by
  rw [p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne K hcoord hpmon hpirr hcdeg hm
    hdeg R, _root_.map_zero]

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTrace K := by
  intro p c m hpmon hpirr hcdeg hm R
  have hpos := hpirr.natDegree_pos
  rcases Nat.lt_or_ge p.natDegree 2 with hdeg | hdeg
  · exact p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne K hcoord hpmon hpirr
      hcdeg hm (by omega) R
  · exact hHigh p c m hpmon hpirr hcdeg hm hdeg R

end DegOneDischargeTrace

section AlgClosedTrace

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [IsAlgClosed K] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K :=
  p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg K
    (p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed K)

end AlgClosedTrace

section DedekindFractionModel

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_dedekindFractionModel
    (hfrac : ValSubringDedekindFractionModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_dedekindModel
    (valSubringDedekindModel_of_dedekindFractionModel hfrac)

end DedekindFractionModel

section EulerGeneral

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K] {p : K[X]} [Fact (Irreducible p)]

theorem aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis

  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]

  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]

  rw [Finset.sum_eq_single (p.natDegree - 1)]
  ·
    rw [FLT.EulerDualBasis.trace_root_pow_div_derivative_self hpmon hpd, mul_one]
  ·
    intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [FLT.EulerDualBasis.trace_root_pow_div_derivative_of_lt hpmon hk', mul_zero]
  ·
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerGeneral

section AlgEquivAdjoinRoot

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable {p : K[X]} (hpirr : Irreducible p)

open RationalFunctionField

def finitePlaceResidueFieldAlgEquivAdjoinRoot :
    AdjoinRoot p ≃ₐ[K] (finitePlace K hpirr).ResidueField :=
  residueFieldEquivOfHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hpirr)

theorem finitePlaceResidueFieldAlgEquivAdjoinRoot_mk (q : K[X]) :
    finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr (AdjoinRoot.mk p q)
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) q,
          algebraMap_mem_ofHeightOneSpectrum K _ q⟩ :=
  rfl

end AlgEquivAdjoinRoot

section TraceTransport

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable {p : K[X]} (hpirr : Irreducible p)

open RationalFunctionField

theorem trace_finitePlace_residueField_eq_trace_adjoinRoot
    (y : (finitePlace K hpirr).ResidueField) :
    Algebra.trace K (finitePlace K hpirr).ResidueField y
      = Algebra.trace K (AdjoinRoot p)
          ((finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm y) := by
  conv_lhs => rw [← (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).apply_symm_apply y]
  exact Algebra.trace_eq_of_algEquiv _ _

end TraceTransport

section BridgeRows

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

def P1FinitePlaceSimplePoleResidueAdjoinRootValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    letI : Fact (Irreducible p) := ⟨hpirr⟩
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule),
    (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p)

def P1PlaceInftySimplePoleResidueEulerValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c.degree < p.degree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

end BridgeRows

section FinitePlaceTrace

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

theorem trace_finitePlace_simplePoleResidue_of_adjoinRootValue
    (hbridge : P1FinitePlaceSimplePoleResidueAdjoinRootValue K)
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := hbridge p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt K hpmon hdeg]

end FinitePlaceTrace

section HigherDegReduction

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hfin : P1FinitePlaceSimplePoleResidueAdjoinRootValue K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ := by
  subst heq
  intro p c hpmon hpirr hdeg hfmem himem
  rw [trace_finitePlace_simplePoleResidue_of_adjoinRootValue K hfin hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end HigherDegReduction

section TwoAffineChartsKaehler

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_dedekindFractionModel
    (valSubringDedekindFractionModel_of_twoAffineCharts h)

end TwoAffineChartsKaehler

section SeparatingTranscendentalKaehler

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_twoAffineCharts
    (valSubringTwoAffineCharts_of_hasSeparatingTranscendental h)

end SeparatingTranscendentalKaehler

namespace Place


section SimplePoleAuxMul

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem simplePoleResidueAux_mul_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule)
    (haf : a * f ∈ v.simplePoleSubmodule) :
    v.simplePoleResidueAux ⟨a * f, haf⟩
      = IsLocalRing.residue _ ⟨a, ha⟩ * v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [simplePoleResidueAux_apply, simplePoleResidueAux_apply, ← map_mul]
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (mul_left_comm _ _ _))

theorem mul_mem_simplePoleSubmodule_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    a * f ∈ v.simplePoleSubmodule := by
  rw [mem_simplePoleSubmodule, mul_left_comm]
  exact mul_mem ha hf

end SimplePoleAuxMul

end Place

section DerivativeRegular

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

open RationalFunctionField

theorem denom_notMem_of_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) {f : RatFunc K}
    (hf : f ∈ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring) :
    f.denom ∉ w.asIdeal := by
  intro hd
  have hxval : w.valuation (RatFunc K) f ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hf)
  have hden_ne : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hmul : f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
    ((div_eq_iff hden_ne).mp f.num_div_denom).symm
  have hnum : f.num ∉ w.asIdeal := by
    intro hn
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom f
    exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
  refine absurd h1 (ne_of_lt ?_)
  calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
      = w.valuation (RatFunc K) f
          * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) := by
        rw [← map_mul, hmul]
    _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w f.denom).mpr hd

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open KaehlerDifferential

private theorem differentialCoeff_add' (v : Place K (RatFunc K)) (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_D_algebraMap_polynomial (v : Place K (RatFunc K)) (q : K[X]) :
    v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) q))
      = algebraMap K[X] (RatFunc K) q.derivative * v.differentialCoeff (dX K) := by
  rw [D_algebraMap_polynomial K q, v.differentialCoeff_smul]

theorem differentialCoeff_D_mem_finitePlace [CharZero K] {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr

  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]

  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  ·
    have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge

end DerivativeRegular

section LeibnizCore

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField KaehlerDifferential

theorem uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h

  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, differentialCoeff_add' K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine mul_mem (uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge)

theorem residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]

  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _) (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_

  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr

  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    differentialCoeff_D_mem_finitePlace K hpirr (uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore

section BridgeDischarge

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField KaehlerDifferential

theorem residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit (hpirr.separable.isUnit_of_dvd' dvd_rfl hlt')

theorem simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  rw [Place.simplePoleResidueAux_apply, eq_div_iff (residue_algebraMap_derivative_ne_zero K hpirr)]

  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf

  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge

section ComposedEngineInfty

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge K hω₀ heq
    (p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX K) hinf

end ComposedEngineInfty

section LowDegRegular

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_dX
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hc : c ≠ 0) :
    (p1PlaceInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K))
      = (p.natDegree : ℤ) - c.natDegree - 2 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
  rw [(p1PlaceInfty K).ord_mul hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero (dX_ne_zero K)),
    ord_placeInfty_p1PrincipalPartAtom K hp hc 1, hInfty]
  push_cast; ring

theorem p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree) :
    p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).toValuationSubring := by
  rcases hcdeg with rfl | hcdeg
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (p1PlaceInfty K).differentialCoeff (dX K) ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · rcases eq_or_ne c 0 with rfl | hc
    · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (p1PlaceInfty K).differentialCoeff (dX K) ∈ _
      rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
    have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
    refine (p1PlaceInfty K).mem_of_ord_nonneg
      (mul_ne_zero hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero (dX_ne_zero K))) ?_
    rw [ord_placeInfty_mOneAtom_mul_differentialCoeff_dX K hInfty hp hc]
    omega

end LowDegRegular

section LowDegValue

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem trace_placeInfty_simplePoleResidue_mOne_of_lowDeg
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hpirr : Irreducible p)
    (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree)
    (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1)) := by

  have hreg := p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hcdeg
  have hLHS : (p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩ = 0 :=
    (p1PlaceInfty K).simplePoleResidueAux_eq_zero_of_mem hreg
  rw [hLHS, _root_.map_zero]

  rcases hcdeg with rfl | hcdeg
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < p.natDegree - 1), _root_.neg_zero]

end LowDegValue

section NamedCarriers

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

def P1PlaceInftySimplePoleResidueEulerValueTopDeg : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c ≠ 0 → c.natDegree + 1 = p.natDegree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

def P1PlaceInftySimplePoleResidueEulerValueMonomial : Prop :=
  ∀ (p : K[X]) (_ : p.Monic) (_ : Irreducible p),
    ∀ (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarriers

section EraseLeadLinearity

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartAtom_add_mul_differentialCoeff (p c₁ c₂ : K[X]) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (c₁ + c₂) m * v.differentialCoeff ω
      = p1PrincipalPartAtom K p c₁ m * v.differentialCoeff ω
        + p1PrincipalPartAtom K p c₂ m * v.differentialCoeff ω := by
  show algebraMap K[X] (RatFunc K) (c₁ + c₂) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = algebraMap K[X] (RatFunc K) c₁ / (algebraMap K[X] (RatFunc K) p) ^ m * v.differentialCoeff ω
      + algebraMap K[X] (RatFunc K) c₂ / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
  rw [map_add]; ring

theorem p1PrincipalPartAtom_C_mul_mul_differentialCoeff (p c : K[X]) (a : K) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (C a * c) m * v.differentialCoeff ω
      = a • (p1PrincipalPartAtom K p c m * v.differentialCoeff ω) := by
  show algebraMap K[X] (RatFunc K) (C a * c) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = a • (algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω)
  rw [map_mul, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
    Algebra.smul_def]
  ring

theorem trace_placeInfty_simplePoleResidueAux_mOne_add
    {p c₁ c₂ : K[X]} {ω : Ω[(RatFunc K)⁄K]}
    (h1 : p1PrincipalPartAtom K p c₁ 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule)
    (h2 : p1PrincipalPartAtom K p c₂ 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule)
    (h12 : p1PrincipalPartAtom K p (c₁ + c₂) 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, h12⟩)
      = Algebra.trace K (p1PlaceInfty K).ResidueField
          ((p1PlaceInfty K).simplePoleResidueAux ⟨_, h1⟩)
        + Algebra.trace K (p1PlaceInfty K).ResidueField
            ((p1PlaceInfty K).simplePoleResidueAux ⟨_, h2⟩) := by
  have heq : (⟨_, h12⟩ : (p1PlaceInfty K).simplePoleSubmodule)
      = (⟨_, h1⟩ : (p1PlaceInfty K).simplePoleSubmodule) + ⟨_, h2⟩ :=
    Subtype.ext (p1PrincipalPartAtom_add_mul_differentialCoeff K p c₁ c₂ 1 _ ω)
  rw [heq, map_add, map_add]

theorem trace_placeInfty_simplePoleResidueAux_mOne_C_mul
    {p c : K[X]} {a : K} {ω : Ω[(RatFunc K)⁄K]}
    (hc : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule)
    (hac : p1PrincipalPartAtom K p (C a * c) 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, hac⟩)
      = a * Algebra.trace K (p1PlaceInfty K).ResidueField
          ((p1PlaceInfty K).simplePoleResidueAux ⟨_, hc⟩) := by
  have heq : (⟨_, hac⟩ : (p1PlaceInfty K).simplePoleSubmodule)
      = a • (⟨_, hc⟩ : (p1PlaceInfty K).simplePoleSubmodule) :=
    Subtype.ext (p1PrincipalPartAtom_C_mul_mul_differentialCoeff K p c a 1 _ ω)
  rw [heq, map_smul, map_smul, smul_eq_mul]

theorem p1PlaceInftySimplePoleResidueEulerValue_of_topDeg
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    (htop : P1PlaceInftySimplePoleResidueEulerValueTopDeg K) :
    P1PlaceInftySimplePoleResidueEulerValue K := by
  intro p c hpmon hpirr hcdeg himem
  rcases eq_or_ne c 0 with rfl | hc
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inl rfl) himem
  have hndeg : c.natDegree < p.natDegree := natDegree_lt_natDegree hc hcdeg
  rcases (by omega : c.natDegree + 2 ≤ p.natDegree ∨ c.natDegree + 1 = p.natDegree) with h | h
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inr h) himem
  · exact htop p c hpmon hpirr hc h himem

theorem p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValueTopDeg K := by
  intro p c hpmon hpirr hc hcnd himem

  have hInfty' : (p1PlaceInfty K).ordDifferential (dX K) = -2 := hInfty
  have hXd : (X ^ (p.natDegree - 1) : K[X]).degree < p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpirr.ne_zero]
    exact_mod_cast (by omega : p.natDegree - 1 < p.natDegree)
  have hXmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) hInfty' hpirr (X ^ (p.natDegree - 1)) hXd
  have hCXmem : p1PrincipalPartAtom K p (C c.leadingCoeff * X ^ (p.natDegree - 1)) 1
        * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_C_mul_mul_differentialCoeff K]
    exact (p1PlaceInfty K).simplePoleSubmodule.smul_mem _ hXmem
  have hELdeg : c.eraseLead = 0 ∨ c.eraseLead.natDegree + 2 ≤ p.natDegree := by
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero c with h | h
    · exact .inr (by omega)
    · exact .inl h
  have hELmem : p1PrincipalPartAtom K p c.eraseLead 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule :=
    (p1PlaceInfty K).mem_simplePoleSubmodule_of_mem
      (p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hELdeg)

  have hcnd' : c.natDegree = p.natDegree - 1 := by omega
  have hcdecomp : c = C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead := by
    conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow c, add_comm, hcnd']

  have h12mem : p1PrincipalPartAtom K p
        (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead) 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_add_mul_differentialCoeff K]; exact add_mem hCXmem hELmem
  have heq : (⟨_, himem⟩ : (p1PlaceInfty K).simplePoleSubmodule) = ⟨_, h12mem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
      = algebraMap K[X] (RatFunc K) (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead)
          / (algebraMap K[X] (RatFunc K) p) ^ 1 * (p1PlaceInfty K).differentialCoeff (dX K)
    rw [← hcdecomp]

  have hELcoeff : c.eraseLead.coeff (p.natDegree - 1) = 0 := by
    rcases hELdeg with h | h
    · rw [h, coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hLead : c.leadingCoeff = c.coeff (p.natDegree - 1) := by
    rw [leadingCoeff, hcnd']
  rw [heq, trace_placeInfty_simplePoleResidueAux_mOne_add K hCXmem hELmem,
    trace_placeInfty_simplePoleResidueAux_mOne_C_mul K hXmem,
    hmono p hpmon hpirr hXmem,
    trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr hELdeg hELmem,
    hELcoeff, _root_.neg_zero, add_zero, hLead]
  ring

theorem p1PlaceInftySimplePoleResidueEulerValue_of_monomial
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_topDeg K hInfty
    (p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial K hInfty hmono)

end EraseLeadLinearity

section ComposedEngineInftyMonomial

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge K hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hmono)

end ComposedEngineInftyMonomial


end AlgebraicCurve

end
