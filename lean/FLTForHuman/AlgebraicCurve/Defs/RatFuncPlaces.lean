/-
The `P¹` place vocabulary: the `ofHeightOneSpectrum` bridge lemmas, the
residue-field/residue-degree computation for `K[X]`, `finitePlace`, and the place
at infinity, after FLT's `Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean` lines
18–236 and the whole of `Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean>).

Dropped (measured, `TOPIC-ac0-vocabulary.md` §2.7): `placeOfPoint` (236–274) and
the whole `Place.Congr` section (274–398). They occur in the cone only inside the
pin's `attribute [-simp]` walls, which the port does not transcribe. The
`RatFuncPlaceInfty` file is the one the blueprint's six-module table omits; it is
ported here in full.
-/
import FLTForHuman.AlgebraicCurve.Defs.Place
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Polynomial.RingDivision

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace Place

/-! ## T1 nodes (wrapper binders) -/

theorem isEquiv_adicValuation_ofHeightOneSpectrum {K F : Type*} [Field K] [Field F]
    [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [Algebra K R] [IsScalarTower K R F]
    (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation :=
  (Place.ofHeightOneSpectrum (K := K) w).isEquiv_adicValuation_of_valuationSubring_eq rfl

/-! ## AC0 helpers with section variables -/

section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

instance : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

instance : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

theorem ord_eq_zero_iff_adicValuation_eq_one {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (v.adicValuation_ne_zero hf)
    rw [h, exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, log_one]

end

theorem ord_ofHeightOneSpectrum_ne_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) {q : R}
    (hq : q ≠ 0) : (Place.ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔
      q ∈ w.asIdeal := by
  have hq' : algebraMap R F q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hq
  rw [ne_eq, (Place.ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hq',
    ← (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).eq_one_iff_eq_one,
    HeightOneSpectrum.valuation_eq_one_iff_notMem, not_not]

section OfHeightOneSpectrum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

theorem ofHeightOneSpectrum_injective :
    Function.Injective (ofHeightOneSpectrum (K := K) (F := F) (R := R)) := by
  intro w w' h
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  refine (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).trans ?_
  rw [h]
  exact (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w').symm

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) :
    HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible hp).isPrime
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero

@[simp]
theorem heightOneSpectrumOfIrreducible_asIdeal {p : K[X]} (hp : Irreducible p) :
    (heightOneSpectrumOfIrreducible K hp).asIdeal = Ideal.span {p} := rfl

theorem exists_irreducible_span (w : HeightOneSpectrum K[X]) :
    ∃ p : K[X], Irreducible p ∧ w.asIdeal = Ideal.span {p} := by
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal w.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hp
  refine ⟨p, ?_, hp⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact w.ne_bot (hp.trans (by simp))
  have hpr := w.isPrime
  rw [hp] at hpr
  exact ((Ideal.span_singleton_prime hp0).mp hpr).irreducible

def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)

theorem finitePlace_def {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp = Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp) := rfl

section ResidueDegree

theorem algebraMap_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring :=
  (Place.mem_iff_adicValuation_le_one _).mpr
    ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mp (w.valuation_le_one q))

def residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    K[X] →+* (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField :=
  (IsLocalRing.residue _).comp
    ((algebraMap K[X] (RatFunc K)).codRestrict
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring.toSubring
      (algebraMap_mem_ofHeightOneSpectrum K w))

theorem residueOfHeightOneSpectrum_apply (w : HeightOneSpectrum K[X]) (q : K[X]) :
    residueOfHeightOneSpectrum K w q = IsLocalRing.residue _
      ⟨algebraMap K[X] (RatFunc K) q, algebraMap_mem_ofHeightOneSpectrum K w q⟩ := rfl

theorem ker_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    RingHom.ker (residueOfHeightOneSpectrum K w) = w.asIdeal := by
  ext q
  rw [RingHom.mem_ker, residueOfHeightOneSpectrum_apply, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one,
    ← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem w q

theorem surjective_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    Function.Surjective (residueOfHeightOneSpectrum K w) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
  have hxval : w.valuation (RatFunc K) x ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hx)

  have hden_ne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr x.denom_ne_zero
  have hmul : x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num :=
    ((div_eq_iff hden_ne).mp x.num_div_denom).symm

  have hden : x.denom ∉ w.asIdeal := by
    intro hd
    have hnum : x.num ∉ w.asIdeal := by
      intro hn
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom x
      exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
    have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
    refine absurd h1 (ne_of_lt ?_)
    calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num)
        = w.valuation (RatFunc K) x
            * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) := by
          rw [← map_mul, hmul]
      _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) :=
          mul_le_of_le_one_left' hxval
      _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w x.denom).mpr hd

  have hmax : w.asIdeal.IsMaximal := IsPrime.to_maximal_ideal w.ne_bot
  obtain ⟨t, ht⟩ : ∃ t : K[X], x.denom * t - 1 ∈ w.asIdeal := by
    obtain ⟨b, c, hc, hbc⟩ := hmax.exists_inv hden
    refine ⟨b, ?_⟩
    rw [show x.denom * b - 1 = -c by linear_combination hbc]
    exact neg_mem hc

  refine ⟨x.num * t, ?_⟩
  rw [residueOfHeightOneSpectrum_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  show (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).adicValuation
    (algebraMap K[X] (RatFunc K) (x.num * t) - x) < 1
  rw [← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  have key : algebraMap K[X] (RatFunc K) (x.num * t) - x
      = x * algebraMap K[X] (RatFunc K) (x.denom * t - 1) := by
    rw [map_sub, map_mul, map_mul, map_one, mul_sub, mul_one, ← mul_assoc, hmul]
  rw [key, map_mul]
  calc w.valuation (RatFunc K) x
        * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1))
      ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1)) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr ht

def residueFieldEquivOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (K[X] ⧸ w.asIdeal) ≃ₐ[K]
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField := by
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_residueOfHeightOneSpectrum K w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_residueOfHeightOneSpectrum K w))) ?_
  intro a
  rw [show (algebraMap K (K[X] ⧸ w.asIdeal)) a
      = Ideal.Quotient.mk w.asIdeal (algebraMap K K[X] a) from rfl]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueOfHeightOneSpectrum_apply]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm)

theorem deg_ofHeightOneSpectrum {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree := by
  rw [Place.deg, ← (residueFieldEquivOfHeightOneSpectrum K w).toLinearEquiv.finrank_eq, hw]
  exact finrank_quotient_span_eq_natDegree

theorem deg_finitePlace {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).deg = p.natDegree :=
  deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp)

end ResidueDegree

end RationalFunctionField

namespace RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem nontrivial_valueGroup_inftyValuation :
    Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

def placeInfty : Place K (RatFunc K) :=
  haveI := nontrivial_valueGroup_inftyValuation K
  { toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
    ne_top' := by
      simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      infer_instance
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (RatFunc.inftyValuation K)).toIsPrincipalIdealRing }

@[simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

end RationalFunctionField

end AlgebraicCurve
