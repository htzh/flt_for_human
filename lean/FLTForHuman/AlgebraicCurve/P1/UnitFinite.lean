/-
UnitFinite — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.DivisorAction

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module

namespace AlgebraicCurve

section UnitFinite

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

open RationalFunctionField

def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K → v.ord (v.differentialCoeff ω₀) = 0

variable {K}

theorem p1DifferentialCoeffRegularFinite_of_unitFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : P1DifferentialCoeffUnitFinite K hω₀) :
    P1DifferentialCoeffRegularFinite K hω₀ :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero hω₀) (hunit v hv).ge

end UnitFinite

section KaehlerRatFunc

variable (K : Type*) [Field K]

open KaehlerDifferential

def kaehlerPolynomialBasis : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

scoped instance instFormallyEtalePolynomialRatFunc : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=
  ⟨Module.Free.of_basis (kaehlerRatFuncBasis K),
    (Module.finrank_eq_card_basis (kaehlerRatFuncBasis K)).trans (by simp)⟩

scoped instance instIsCurveOverRatFunc : IsCurveOver K (RatFunc K) :=
  RationalFunctionField.isCurveOver_of_kaehlerRankOne K (kaehlerRankOne_ratFunc K)

end KaehlerRatFunc

namespace Place

attribute [local instance 0] valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  haveI hfin : Fintype ↥((IsLocalRing.maximalIdeal v.toValuationSubring).primesOver
      (integralClosureAt F' v)) :=
    (IsDedekindDomain.coe_primesOverFinset (maximalIdeal_ne_bot v) (integralClosureAt F' v)) ▸
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v)).finite_toSet.fintype
  have hkey := Ideal.sum_ramification_inertia_eq_finrank
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (integralClosureAt F' v)
  rw [← IsFractionRing.finrank_eq v.toValuationSubring F (integralClosureAt F' v) F'] at hkey
  have hconv : (∑ q : ↥((IsLocalRing.maximalIdeal v.toValuationSubring).primesOver
        (integralClosureAt F' v)),
        q.1.ramificationIdx v.toValuationSubring * q.1.inertiaDeg v.toValuationSubring)
      = ∑ P ∈ IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
          (integralClosureAt F' v),
          P.ramificationIdx v.toValuationSubring * P.inertiaDeg v.toValuationSubring :=
    (Finset.sum_subtype
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v))
      (fun P => IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v) (P := P))
      (fun P => P.ramificationIdx v.toValuationSubring * P.inertiaDeg v.toValuationSubring)).symm
  rw [← hkey]
  rw [hconv]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v ((hs w).mp hw)).asIdeal) ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v ((hs w).mp hw)).isPrime,
      fiberCenter_liesOver ((hs w).mp hw)⟩
  ·
    intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((hs w).mp hw) ((hs w').mp hw')
      (HeightOneSpectrum.ext h)
  ·
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      (hs _).mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  ·
    intro w hw
    have hwr := (hs w).mp hw
    haveI : (fiberCenter F' v hwr).asIdeal.LiesOver
        (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hwr
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter hwr,
      inertiaDeg_eq_inertiaDeg_fiberCenter hwr,
      Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal v.toValuationSubring)
        (fiberCenter F' v hwr).asIdeal (maximalIdeal_ne_bot v),
      Ideal.inertiaDeg'_eq_inertiaDeg _ _]

theorem sum_ramificationIndex_mul_deg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff v s hs
  calc ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = ∑ w ∈ s, (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hdeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
          deg_restrict_mul_inertiaDeg (K := K) (F := F) (w := w)
        rw [(hs w).mp hw] at hdeg
        rw [← hdeg]
        push_cast
        ring
    _ = (v.deg : ℤ) * ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
        rw [Finset.mul_sum]
    _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [hsum]; ring

end Place

theorem ramificationInertiaIdentity_of_finiteDimensional
    (K F F' : Type*) [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] :
    RamificationInertiaIdentity K F F' := fun v s hs =>
  Place.sum_ramificationIndex_mul_deg_of_forall_mem_iff v s hs

section PCoordinateIdentity

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem derivative_monic_natDegree_one_eq_one {p : K[X]} (hpmon : p.Monic)
    (hdeg : p.natDegree = 1) : derivative p = 1 := by
  rw [hpmon.eq_X_add_C hdeg, derivative_add, derivative_X, derivative_C, add_zero]

theorem D_algebraMap_polynomial_degOne {p : K[X]} (hpmon : p.Monic) (hdeg : p.natDegree = 1) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) p) = dX K := by
  rw [D_algebraMap_polynomial K p, derivative_monic_natDegree_one_eq_one K hpmon hdeg, map_one,
    one_smul]

theorem eq_C_coeff_zero_of_degree_lt_degOne {p c : K[X]} (hpirr : Irreducible p)
    (hdeg : p.natDegree = 1) (hcdeg : c.degree < p.degree) : c = C (c.coeff 0) := by
  have hpdeg : p.degree = (1 : ℕ) := by
    rw [degree_eq_natDegree hpirr.ne_zero, hdeg]
  rw [hpdeg, Nat.cast_one] at hcdeg
  exact eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hcdeg)

theorem p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : p.natDegree = 1)
    (hcdeg : c.degree < p.degree) (m : ℕ) :
    p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)
      = c.coeff 0 • ((finitePlace K hpirr).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
          * ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹) := by
  have hc : algebraMap K[X] (RatFunc K) c = algebraMap K (RatFunc K) (c.coeff 0) := by
    conv_lhs => rw [eq_C_coeff_zero_of_degree_lt_degOne K hpirr hdeg hcdeg]
    rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
  rw [D_algebraMap_polynomial_degOne K hpmon hdeg, Algebra.smul_def,
    show p1PrincipalPartAtom K p c m
      = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m from rfl, hc]
  ring

end PCoordinateIdentity

section NamedHigherDeg

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

def P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p),
    c.degree < p.degree → 2 ≤ m → 2 ≤ p.natDegree →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      R.res (p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)) = 0

end NamedHigherDeg

section DegOneDischarge

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hcdeg : c.degree < p.degree) (hm : 2 ≤ m) (hdeg : p.natDegree = 1)
    (R : (finitePlace K hpirr).CanonicalLocalResidueDataK) :
    R.res (p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)) = 0 := by
  rw [p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne K hpmon hpirr hdeg hcdeg m, map_smul,
    show m = (m - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm,
    hcoord (finitePlace K hpirr) (algebraMap K[X] (RatFunc K) p) (ord_finitePlace_self K hpirr)
      R (m - 1) (by omega),
    smul_zero]

end DegOneDischarge

section AlgClosed

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [IsAlgClosed K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed :
    P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg K := by
  intro p c m _ hpirr _ _ hdeg
  have h1 : p.natDegree = 1 := by
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hpirr
    rw [degree_eq_natDegree hpirr.ne_zero] at h
    exact_mod_cast h
  omega

end AlgClosed

end AlgebraicCurve

end
