/-
DivPow — the atom-3 tower tail of the ℙ¹ residue core.

Port of the unique tail of
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean`
(pin `anthropics/fermats-last-theorem@aa2d8b3`), the sibling of the master
ℙ¹ file already ported as the `P1/` chain. The shared engine is imported from
`P1/Core`.

**Partial set (P3.2f).** Everything here except the headline is landed. The
headline `RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero`
(pin S_ file lines 2016–2140) is *not* ported: its proof calls
`AlgebraicCurve.completionTraceSum_of_isSeparable` and
`AlgebraicCurve.residueTraceCompletionCommute_v2`, which are absent from the
port and in turn require the whole unported Tate agreement
(`tateCommFinite` / `tateAgreement_v2` / `tateChainRule` /
`tateTraceCompat_of_isSeparable`). See the P3.2f report for the promotion debt.
-/
import FLTForHuman.AlgebraicCurve.P1.Core
import FLTForHuman.AlgebraicCurve.Defs.PlaceCompletion

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open KaehlerDifferential
open scoped IntermediateField
open AlgebraicCurve

namespace AlgebraicCurve

open RationalFunctionField

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace P1Tower

variable (K : Type*) [Field K] (p : K[X])

/-- The `K`-algebra map `K[X] → RatFunc K` sending `X` to `p`. -/
def substPoly : K[X] →ₐ[K] RatFunc K :=
  Polynomial.aeval (algebraMap K[X] (RatFunc K) p)

theorem substPoly_apply (q : K[X]) :
    substPoly K p q = algebraMap K[X] (RatFunc K) (q.comp p) := by
  simp only [substPoly, Polynomial.comp_eq_aeval, ← Polynomial.aeval_algebraMap_apply]

variable {p} in
theorem substPoly_ne_zero (hp : 0 < p.natDegree) {q : K[X]} (hq : q ≠ 0) :
    substPoly K p q ≠ 0 := by
  rw [substPoly_apply, Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
  exact fun h => hq ((Polynomial.comp_eq_zero_iff.mp h).resolve_right (fun hh => by
    have := hh.2; rw [this] at hp; simp at hp))

/-- The induced `K`-algebra endomorphism `RatFunc K → RatFunc K` sending `X` to `p`. -/
def subst (hp : 0 < p.natDegree) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (substPoly K p) (fun q hq => by
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      (substPoly_ne_zero K hp (nonZeroDivisors.ne_zero hq)))

theorem subst_algebraMap (hp : 0 < p.natDegree) (q : K[X]) :
    subst K p hp (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) (q.comp p) := by
  rw [subst, RatFunc.liftAlgHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    map_one, div_one, substPoly_apply]

/-- The type synonym carrying the `RatFunc K`-algebra structure through `subst`. -/
def Kx (_hp : 0 < p.natDegree) : Type _ := RatFunc K

variable (hp : 0 < p.natDegree)

scoped instance : Field (Kx K p hp) := inferInstanceAs (Field (RatFunc K))
scoped instance : Algebra K (Kx K p hp) := inferInstanceAs (Algebra K (RatFunc K))
scoped instance : DecidableEq (Kx K p hp) := Classical.decEq _

def toKx : RatFunc K ≃ₐ[K] Kx K p hp := AlgEquiv.refl

scoped instance algebraKx : Algebra (RatFunc K) (Kx K p hp) :=
  ((toKx K p hp).toAlgHom.comp (subst K p hp)).toRingHom.toAlgebra

theorem algebraMap_Kx_apply (f : RatFunc K) :
    algebraMap (RatFunc K) (Kx K p hp) f = toKx K p hp (subst K p hp f) := rfl

scoped instance : IsScalarTower K (RatFunc K) (Kx K p hp) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    rw [algebraMap_Kx_apply, IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      ← Polynomial.C_eq_algebraMap]
    show algebraMap K (RatFunc K) a = subst K p hp (algebraMap K[X] (RatFunc K) (C a))
    rw [subst_algebraMap, Polynomial.C_comp, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply])

theorem subst_X : subst K p hp (RatFunc.X : RatFunc K) = algebraMap K[X] (RatFunc K) p := by
  rw [← RatFunc.algebraMap_X, subst_algebraMap, Polynomial.X_comp]

theorem aeval_ratFuncX (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X]
  rw [show (algebraMap K[X] (RatFunc K)) X
        = (IsScalarTower.toAlgHom K K[X] (RatFunc K)) X from rfl,
    Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left]
  rfl

private def _root_.AlgebraicCurve.P1Tower.gen : Kx K p hp :=
  toKx K p hp (RatFunc.X : RatFunc K)

def minP : (RatFunc K)[X] := p.map (algebraMap K (RatFunc K)) - C (RatFunc.X : RatFunc K)

theorem toKx_apply (f : RatFunc K) : toKx K p hp f = (f : RatFunc K) := rfl

theorem aeval_gen_map (q : K[X]) :
    aeval (gen K p hp) (q.map (algebraMap K (RatFunc K)))
      = toKx K p hp (algebraMap K[X] (RatFunc K) q) := by
  rw [aeval_map_algebraMap]
  exact aeval_ratFuncX K q

theorem aeval_gen_minP : aeval (gen K p hp) (minP K p) = 0 := by
  rw [minP, map_sub, aeval_gen_map, aeval_C, algebraMap_Kx_apply, subst_X, sub_self]

include hp in
theorem monic_minP (hmon : p.Monic) : (minP K p).Monic := by
  rw [minP]
  refine (hmon.map _).sub_of_left ?_
  rw [degree_C (RatFunc.X_ne_zero), Polynomial.degree_map]
  exact_mod_cast (show (0 : WithBot ℕ) < p.degree from by
    rw [Polynomial.degree_eq_natDegree (by rintro rfl; simp at hp)]; exact_mod_cast hp)

private theorem _root_.AlgebraicCurve.P1Tower.isIntegral_gen (hmon : p.Monic) :
    IsIntegral (RatFunc K) (gen K p hp) :=
  ⟨minP K p, monic_minP K p hp hmon, by
    have h := aeval_gen_minP K p hp
    rwa [aeval_def] at h⟩

include hp in
theorem minP_ne_zero (hmon : p.Monic) : minP K p ≠ 0 := (monic_minP K p hp hmon).ne_zero

theorem toKx_algebraMap_mem_adjoin (q : K[X]) :
    toKx K p hp (algebraMap K[X] (RatFunc K) q)
      ∈ IntermediateField.adjoin (RatFunc K) {gen K p hp} := by
  rw [← aeval_gen_map]
  exact IntermediateField.algebra_adjoin_le_adjoin (RatFunc K) _
    (Polynomial.aeval_mem_adjoin_singleton (RatFunc K) _)

theorem adjoin_gen_eq_top :
    IntermediateField.adjoin (RatFunc K) {gen K p hp} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  induction f using RatFunc.induction_on with
  | f a b hb =>
    have ha := toKx_algebraMap_mem_adjoin K p hp a
    have hb' := toKx_algebraMap_mem_adjoin K p hp b
    exact div_mem ha hb'

theorem finiteDimensional_Kx (hmon : p.Monic) : FiniteDimensional (RatFunc K) (Kx K p hp) := by
  have h := IntermediateField.adjoin.finiteDimensional (isIntegral_gen K p hp hmon)
  rw [adjoin_gen_eq_top] at h
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem isIntegral_Kx (hmon : p.Monic) : Algebra.IsIntegral (RatFunc K) (Kx K p hp) :=
  haveI := finiteDimensional_Kx K p hp hmon
  Algebra.IsIntegral.of_finite (RatFunc K) (Kx K p hp)

theorem derivative_minP :
    derivative (minP K p) = (derivative p).map (algebraMap K (RatFunc K)) := by
  rw [minP, derivative_sub, derivative_C, sub_zero, Polynomial.derivative_map]

theorem transcendental_ratFuncX : Transcendental K (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact (transcendental_algebraMap_iff (IsFractionRing.injective K[X] (RatFunc K))).mpr
    (Polynomial.transcendental_X K)

include hp in
theorem separable_minP (hsep : p.Separable) : (minP K p).Separable := by
  classical
  let L := AlgebraicClosure (RatFunc K)
  rw [Polynomial.Separable, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (RatFunc K) L]
  intro β
  by_contra h
  push_neg at h
  obtain ⟨hP, hP'⟩ := h
  have hd0 : derivative p ≠ 0 := by
    intro h0
    have hu : IsUnit p := by
      have hc : IsCoprime p (derivative p) := hsep
      rw [h0] at hc
      exact isCoprime_zero_right.mp hc
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have h1 : aeval β (derivative p) = 0 := by
    rw [derivative_minP, aeval_map_algebraMap] at hP'
    exact hP'
  have hβ : IsIntegral K β := isAlgebraic_iff_isIntegral.mp ⟨derivative p, hd0, h1⟩
  have h2 : aeval β p = algebraMap (RatFunc K) L RatFunc.X := by
    rw [minP, map_sub, aeval_map_algebraMap, aeval_C, sub_eq_zero] at hP
    exact hP
  have h3 : IsIntegral K (aeval β p) :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin K {β}) hβ.fg_adjoin_singleton _
      (Polynomial.aeval_mem_adjoin_singleton K _)
  rw [h2] at h3
  have h4 : IsIntegral K (RatFunc.X : RatFunc K) :=
    (isIntegral_algebraMap_iff (R := K) (A := RatFunc K) (B := L)).mp h3
  exact transcendental_ratFuncX K h4.isAlgebraic

theorem isSeparable_gen (hmon : p.Monic) (hsep : p.Separable) :
    IsSeparable (RatFunc K) (gen K p hp) :=
  (separable_minP K p hp hsep).of_dvd (minpoly.dvd _ _ (aeval_gen_minP K p hp))

theorem isSeparable_Kx (hmon : p.Monic) (hsep : p.Separable) :
    Algebra.IsSeparable (RatFunc K) (Kx K p hp) := by
  haveI := finiteDimensional_Kx K p hp hmon
  have h : Algebra.IsSeparable (RatFunc K)
      (IntermediateField.adjoin (RatFunc K) {gen K p hp}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc K) (Kx K p hp)).mpr
      (isSeparable_gen K p hp hmon hsep)
  rw [adjoin_gen_eq_top] at h
  exact Algebra.IsSeparable.of_algHom (RatFunc K) _
    (IntermediateField.topEquiv (F := RatFunc K) (E := Kx K p hp)).symm.toAlgHom

end P1Tower

section SubstOrd

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [IsCurveOver K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable (p : K[X]) (hp : 0 < p.natDegree)

namespace P1Tower

scoped instance isCurveOver_Kx : IsCurveOver K (Kx K p hp) := ‹IsCurveOver K (RatFunc K)›
scoped instance nontrivialKaehler_Kx : Nontrivial Ω[(Kx K p hp)⁄K] :=
  ‹Nontrivial Ω[(RatFunc K)⁄K]›
scoped instance dCoordGenerates_Kx (w : Place K (Kx K p hp)) : w.DCoordGenerates :=
  ‹∀ v : Place K (RatFunc K), v.DCoordGenerates› w

variable {p} in
theorem ord_finitePlace_pos_iff_dvd {q : K[X]} (hirr : Irreducible q) {a : K[X]}
    (ha : a ≠ 0) :
    0 < (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) a) ↔ q ∣ a := by
  have hmem := algebraMap_mem_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hirr) a
  have hnn : 0 ≤ (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) a) :=
    (finitePlace K hirr).ord_nonneg_of_mem hmem
  have hiff := Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
    (heightOneSpectrumOfIrreducible K hirr) ha
  rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, ← finitePlace_def] at hiff
  rw [← hiff]
  omega

variable {p} in
theorem ord_finitePlace_eq_zero_iff_not_dvd {q : K[X]} (hirr : Irreducible q) {a : K[X]}
    (ha : a ≠ 0) :
    (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) a) = 0 ↔ ¬ q ∣ a := by
  have hiff := Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
    (heightOneSpectrumOfIrreducible K hirr) ha
  rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, ← finitePlace_def] at hiff
  rw [← hiff, not_not]

theorem not_dvd_comp_of_eval_zero_ne_zero {u : K[X]} (hu : u.eval 0 ≠ 0) (hpu : ¬ IsUnit p) :
    ¬ p ∣ u.comp p := by
  intro hdvd
  have hX : X ∣ u - C (u.eval 0) := by
    rw [Polynomial.X_dvd_iff, coeff_sub, coeff_C_zero, ← Polynomial.coeff_zero_eq_eval_zero,
      sub_self]
  obtain ⟨r, hr⟩ := hX
  have hcomp : u.comp p = p * r.comp p + C (u.eval 0) := by
    have := congrArg (fun q => q.comp p) hr
    simp only [Polynomial.sub_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp]
      at this
    rw [← this]; ring
  have : p ∣ C (u.eval 0) := by
    have h2 : C (u.eval 0) = u.comp p - p * r.comp p := by rw [hcomp]; ring
    rw [h2]
    exact dvd_sub hdvd (dvd_mul_right _ _)
  exact hpu (isUnit_of_dvd_unit this (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hu)))

include hp in
theorem not_isUnit_p : ¬ IsUnit p := fun h => by
  have := Polynomial.natDegree_eq_zero_of_isUnit h; omega

theorem ord_finitePlace_subst_algebraMap (hirr : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (finitePlace K hirr).ord (subst K p hp (algebraMap K[X] (RatFunc K) q))
      = (Polynomial.rootMultiplicity 0 q : ℤ)
        * (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨u, hqu, hXu⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0
  set k := Polynomial.rootMultiplicity 0 q
  have hu0 : u ≠ 0 := by rintro rfl; simp at hqu; exact hq hqu
  have hueval : u.eval 0 ≠ 0 := by
    intro h
    exact hXu (by simpa using (Polynomial.dvd_iff_isRoot).mpr h)
  have hcomp : q.comp p = p ^ k * u.comp p := by
    conv_lhs => rw [hqu]
    simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp, map_zero, sub_zero]
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hup0 : u.comp p ≠ 0 := fun h => by
    have := not_dvd_comp_of_eval_zero_ne_zero K p hueval (not_isUnit_p K p hp)
    rw [h] at this; exact this (dvd_zero _)
  rw [subst_algebraMap, hcomp, map_mul, map_pow,
    (finitePlace K hirr).ord_mul (pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hp0))
      ((map_ne_zero_iff _ hinj).mpr hup0),
    ← zpow_natCast, (finitePlace K hirr).ord_zpow,
    (ord_finitePlace_eq_zero_iff_not_dvd K hirr hup0).mpr
      (not_dvd_comp_of_eval_zero_ne_zero K p hueval (not_isUnit_p K p hp)), add_zero]

theorem ord_finitePlace_subst (hirr : Irreducible p) (f : RatFunc K) :
    (finitePlace K hirr).ord (subst K p hp f)
      = (placeOfPoint K 0).ord f
        * (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hsn : subst K p hp (algebraMap K[X] (RatFunc K) f.num) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.num ▸ substPoly_ne_zero K hp hnum
  have hsd : subst K p hp (algebraMap K[X] (RatFunc K) f.denom) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.denom ▸ substPoly_ne_zero K hp hden
  conv_lhs => rw [← RatFunc.num_div_denom f, map_div₀]
  conv_rhs => rw [← RatFunc.num_div_denom f]
  rw [div_eq_mul_inv, div_eq_mul_inv, (finitePlace K hirr).ord_mul hsn (inv_ne_zero hsd),
    Place.ord_inv,
    ord_finitePlace_subst_algebraMap K p hp hirr hnum,
    ord_finitePlace_subst_algebraMap K p hp hirr hden,
    (placeOfPoint K 0).ord_mul ((map_ne_zero_iff _ hinj).mpr hnum)
      (inv_ne_zero ((map_ne_zero_iff _ hinj).mpr hden)), Place.ord_inv,
    ord_placeOfPoint_algebraMap 0 hnum, ord_placeOfPoint_algebraMap 0 hden]
  ring

theorem restrict_finitePlace (hirr : Irreducible p)
    [Algebra.IsIntegral (RatFunc K) (Kx K p hp)] :
    Place.restrict (RatFunc K) (show Place K (Kx K p hp) from finitePlace K hirr)
      = placeOfPoint K 0 := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [Place.mem_restrict_iff]
  show subst K p hp f ∈ (finitePlace K hirr).toValuationSubring ↔ _
  rcases eq_or_ne f 0 with rfl | hf
  · simp [map_zero, zero_mem]
  have hsf : subst K p hp f ≠ 0 := (map_ne_zero_iff _ (subst K p hp).toRingHom.injective).mpr hf
  have hpos : 0 < (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) := by
    rw [ord_finitePlace_pos_iff_dvd K hirr hirr.ne_zero]
  rw [Place.mem_iff_ord_nonneg _ hsf, Place.mem_iff_ord_nonneg _ hf,
    ord_finitePlace_subst K p hp hirr]
  constructor
  · intro h; by_contra hneg; push_neg at hneg
    have : (placeOfPoint K 0).ord f * (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p)
        < 0 :=
      mul_neg_of_neg_of_pos hneg hpos
    omega
  · intro h; exact mul_nonneg h hpos.le

scoped instance instFiniteResiduePlaceKx [DecidableEq (RatFunc K)] (w : Place K (Kx K p hp)) :
    w.FiniteResidue :=
  RationalFunctionField.instFiniteResidue (K := K) w

variable {p} in
theorem eq_finitePlace_of_ord_pos [DecidableEq (RatFunc K)] (hirr : Irreducible p)
    {w' : Place K (RatFunc K)} (h : 0 < w'.ord (algebraMap K[X] (RatFunc K) p)) :
    w' = finitePlace K hirr := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty w' with ⟨q, rfl⟩ | rfl
  · have hmem : p ∈ q.asIdeal :=
      (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) q hirr.ne_zero).mp
        h.ne'
    obtain ⟨r, hrirr, hr⟩ := exists_irreducible_span K q
    have hassoc : Associated r p := by
      rw [hr, Ideal.mem_span_singleton] at hmem
      exact hrirr.associated_of_dvd hirr hmem
    have hq : q = heightOneSpectrumOfIrreducible K hirr := by
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      rw [heightOneSpectrumOfIrreducible_asIdeal, hr, Ideal.span_singleton_eq_span_singleton]
      exact hassoc
    rw [hq, finitePlace_def]
  · exfalso
    rw [ord_placeInfty ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
        hirr.ne_zero), RatFunc.intDegree_polynomial] at h
    have : (0 : ℤ) ≤ (p.natDegree : ℤ) := Int.natCast_nonneg _
    omega

theorem finitePlace_mem_fiber (hirr : Irreducible p)
    [Algebra.IsIntegral (RatFunc K) (Kx K p hp)] :
    (show Place K (Kx K p hp) from finitePlace K hirr)
      ∈ (placeOfPoint K 0).fiber (Kx K p hp) :=
  Place.mem_fiber.mpr (restrict_finitePlace K p hp hirr)

theorem fiber_placeOfPoint_zero (hirr : Irreducible p) [DecidableEq (RatFunc K)]
    [Algebra.IsIntegral (RatFunc K) (Kx K p hp)] :
    (placeOfPoint K 0).fiber (Kx K p hp)
      = {(show Place K (Kx K p hp) from finitePlace K hirr)} := by
  ext w'
  rw [Finset.mem_singleton, Place.mem_fiber]
  constructor
  · intro hw'
    have hX : (placeOfPoint K 0).ord (RatFunc.X : RatFunc K) = 1 := by
      classical
      rw [← RatFunc.algebraMap_X, ord_placeOfPoint_algebraMap 0 Polynomial.X_ne_zero]
      have h := (Polynomial.rootMultiplicity_X_sub_C : Polynomial.rootMultiplicity (0 : K) (X - C 0) = _)
      rw [map_zero, sub_zero, if_pos rfl] at h
      exact_mod_cast h
    have hord : w'.ord (algebraMap (RatFunc K) (Kx K p hp) RatFunc.X)
        = (Place.ramificationIndex (F := RatFunc K) w' : ℤ) * 1 := by
      rw [Place.ord_restrict, hw', hX]
    have hpos : 0 < w'.ord (algebraMap (RatFunc K) (Kx K p hp) RatFunc.X) := by
      rw [hord, mul_one]; exact_mod_cast Place.ramificationIndex_pos (F := RatFunc K) w'
    rw [algebraMap_Kx_apply, subst_X] at hpos
    exact eq_finitePlace_of_ord_pos K hirr hpos
  · rintro rfl
    exact restrict_finitePlace K p hp hirr

theorem ord_placeInfty_subst_algebraMap [DecidableEq (RatFunc K)] {q : K[X]} (hq : q ≠ 0) :
    (placeInfty K).ord (subst K p hp (algebraMap K[X] (RatFunc K) q))
      = (p.natDegree : ℤ) * (placeInfty K).ord (algebraMap K[X] (RatFunc K) q) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hqp : q.comp p ≠ 0 := fun h => by
    have := substPoly_ne_zero K hp hq; rw [substPoly_apply, h, map_zero] at this; exact this rfl
  rw [subst_algebraMap, ord_placeInfty ((map_ne_zero_iff _ hinj).mpr hqp),
    ord_placeInfty ((map_ne_zero_iff _ hinj).mpr hq), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, Polynomial.natDegree_comp]
  push_cast
  ring

theorem ord_placeInfty_subst [DecidableEq (RatFunc K)] (f : RatFunc K) :
    (placeInfty K).ord (subst K p hp f) = (p.natDegree : ℤ) * (placeInfty K).ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hsn : subst K p hp (algebraMap K[X] (RatFunc K) f.num) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.num ▸ substPoly_ne_zero K hp hnum
  have hsd : subst K p hp (algebraMap K[X] (RatFunc K) f.denom) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.denom ▸ substPoly_ne_zero K hp hden
  conv_lhs => rw [← RatFunc.num_div_denom f, map_div₀]
  conv_rhs => rw [← RatFunc.num_div_denom f]
  rw [div_eq_mul_inv, div_eq_mul_inv, (placeInfty K).ord_mul hsn (inv_ne_zero hsd), Place.ord_inv,
    ord_placeInfty_subst_algebraMap K p hp hnum, ord_placeInfty_subst_algebraMap K p hp hden,
    (placeInfty K).ord_mul ((map_ne_zero_iff _ hinj).mpr hnum)
      (inv_ne_zero ((map_ne_zero_iff _ hinj).mpr hden)), Place.ord_inv]
  ring

end P1Tower

end SubstOrd

section OrdPrivateHelpers

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

private theorem _root_.AlgebraicCurve.Place.ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  ·
    have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega

end Place

end OrdPrivateHelpers

section P1TowerPart3

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [IsCurveOver K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable (p : K[X]) (hp : 0 < p.natDegree)

namespace P1Tower

theorem ord_sum_of_injOn {F : Type*} [Field F] [Algebra K F] (v : Place K F) {ι : Type*}
    (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0)
    (hinj : Set.InjOn (fun i => v.ord (f i)) s) (hs : s.Nonempty) :
    (∑ i ∈ s, f i) ≠ 0 ∧ v.ord (∑ i ∈ s, f i) = s.inf' hs (fun i => v.ord (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (Finset.not_nonempty_empty)
  | @insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · refine ⟨?_, ?_⟩
      · simpa using hf a (Finset.mem_insert_self a ∅)
      · simp
    have hf' : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hinj' : Set.InjOn (fun i => v.ord (f i)) s := hinj.mono (Finset.subset_insert a s)
    obtain ⟨hne, hord⟩ := ih hf' hinj' hsne
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    obtain ⟨j, hj, hjmin⟩ := Finset.exists_mem_eq_inf' hsne (fun i => v.ord (f i))
    have hdiff : v.ord (f a) ≠ v.ord (∑ i ∈ s, f i) := by
      rw [hord, hjmin]
      intro heq
      have := hinj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hj) heq
      exact ha (this ▸ hj)
    rw [Finset.sum_insert ha, Finset.inf'_insert]
    refine ⟨?_, ?_⟩
    · intro h0
      have : ∑ i ∈ s, f i = -f a := eq_neg_of_add_eq_zero_right h0
      rw [this, v.ord_neg'] at hdiff
      exact hdiff rfl
    · rw [v.ord_add_eq_min hfa hne hdiff, hord]

theorem linearIndependent_pow_gen [DecidableEq (RatFunc K)] :
    LinearIndependent (RatFunc K) (fun i : Fin p.natDegree => gen K p hp ^ (i : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : ∑ i : Fin p.natDegree, subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ) = 0 := by
    have : ∀ i : Fin p.natDegree, g i • gen K p hp ^ (i : ℕ)
        = toKx K p hp (subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ)) := fun i => by
      rw [Algebra.smul_def, algebraMap_Kx_apply]; rfl
    simp_rw [this] at hg
    rw [← map_sum] at hg
    exact (map_eq_zero_iff _ (toKx K p hp).injective).mp hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  let S : Finset (Fin p.natDegree) := Finset.univ.filter (fun i => g i ≠ 0)
  have hS : S.Nonempty := ⟨i0, by simp [S, hi0]⟩
  have hterm : ∀ i ∈ S, subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ) ≠ 0 := by
    intro i hi
    have hgi : g i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact mul_ne_zero ((_root_.map_ne_zero (subst K p hp)).mpr hgi)
      (pow_ne_zero _ RatFunc.X_ne_zero)
  have hordt : ∀ i ∈ S, (placeInfty K).ord (subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ))
      = (p.natDegree : ℤ) * (placeInfty K).ord (g i) - (i : ℕ) := by
    intro i hi
    have hgi : g i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [(placeInfty K).ord_mul ((_root_.map_ne_zero (subst K p hp)).mpr hgi)
      (pow_ne_zero _ RatFunc.X_ne_zero), ← zpow_natCast, (placeInfty K).ord_zpow,
      ord_placeInfty_subst, ord_placeInfty RatFunc.X_ne_zero, RatFunc.intDegree_X]
    ring
  have hinj : Set.InjOn
      (fun i => (placeInfty K).ord (subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ))) S := by
    intro i hi j hj heq
    simp only at heq
    rw [hordt i hi, hordt j hj] at heq
    have hd : ((p.natDegree : ℤ)) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by
      refine ⟨(placeInfty K).ord (g i) - (placeInfty K).ord (g j), ?_⟩
      linear_combination (-1 : ℤ) * heq
    have hlt : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs < ((p.natDegree : ℤ)).natAbs := by
      have hi' := i.isLt; have hj' := j.isLt
      omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hlt
    exact Fin.ext (by omega)
  have key := (ord_sum_of_injOn K (placeInfty K) S _ hterm hinj hS).1
  apply key
  rw [← hsum]
  refine Finset.sum_filter_of_ne (fun i _ hne => ?_)
  intro hgi
  apply hne
  rw [hgi, map_zero, zero_mul]

theorem natDegree_le_finrank [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    p.natDegree ≤ Module.finrank (RatFunc K) (Kx K p hp) := by
  haveI := finiteDimensional_Kx K p hp hmon
  simpa using (linearIndependent_pow_gen K p hp).fintype_card_le_finrank

theorem minpoly_gen [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    minpoly (RatFunc K) (gen K p hp) = minP K p := by
  haveI := finiteDimensional_Kx K p hp hmon
  have hint := isIntegral_gen K p hp hmon
  have hdvd : minpoly (RatFunc K) (gen K p hp) ∣ minP K p :=
    minpoly.dvd _ _ (aeval_gen_minP K p hp)
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (monic_minP K p hp hmon) hdvd ?_
  have h1 : (minP K p).natDegree = p.natDegree := by
    rw [minP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [natDegree_C, hp]
  have h2 : Module.finrank (RatFunc K) (Kx K p hp)
      = (minpoly (RatFunc K) (gen K p hp)).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, adjoin_gen_eq_top]
    exact (IntermediateField.topEquiv (F := RatFunc K) (E := Kx K p hp)).toLinearEquiv.finrank_eq.symm
  rw [h1, ← h2]
  exact natDegree_le_finrank K p hp hmon

noncomputable def pbGen [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    PowerBasis (RatFunc K) (Kx K p hp) :=
  (IntermediateField.adjoin.powerBasis (isIntegral_gen K p hp hmon)).map
    ((IntermediateField.equivOfEq (adjoin_gen_eq_top K p hp)).trans IntermediateField.topEquiv)

theorem pbGen_gen [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    (pbGen K p hp hmon).gen = gen K p hp := by
  simp [pbGen, IntermediateField.adjoin.powerBasis_gen]

theorem pbGen_dim [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    (pbGen K p hp hmon).dim = p.natDegree := by
  rw [pbGen, PowerBasis.map_dim, IntermediateField.adjoin.powerBasis_dim, minpoly_gen K p hp hmon,
    minP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [natDegree_C, hp]

theorem aeval_gen_derivative_minpoly [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    aeval (gen K p hp) (derivative (minpoly (RatFunc K) (gen K p hp)))
      = toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p)) := by
  rw [minpoly_gen K p hp hmon, derivative_minP, aeval_gen_map]

theorem toKx_algebraMap_eq_sum {c : K[X]} (hc : c.natDegree < p.natDegree) :
    toKx K p hp (algebraMap K[X] (RatFunc K) c)
      = ∑ k ∈ Finset.range p.natDegree, algebraMap K (RatFunc K) (c.coeff k) • gen K p hp ^ k := by
  rw [← aeval_gen_map, Polynomial.aeval_eq_sum_range' (by rwa [Polynomial.natDegree_map])]
  simp only [Polynomial.coeff_map]

theorem trace_mul_inv_derivative [DecidableEq (RatFunc K)] (hmon : p.Monic) (hsep : p.Separable)
    {c : K[X]} (hc : c.natDegree < p.natDegree) :
    haveI := finiteDimensional_Kx K p hp hmon
    Algebra.trace (RatFunc K) (Kx K p hp)
      (toKx K p hp (algebraMap K[X] (RatFunc K) c)
        * (toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p)))⁻¹)
      = algebraMap K (RatFunc K) (c.coeff (p.natDegree - 1)) := by
  haveI := finiteDimensional_Kx K p hp hmon
  haveI := isSeparable_Kx K p hp hmon hsep
  have hgen := pbGen_gen K p hp hmon
  have hdim := pbGen_dim K p hp hmon
  have hder : toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p))
      = aeval (pbGen K p hp hmon).gen
          (derivative (minpoly (RatFunc K) (pbGen K p hp hmon).gen)) := by
    rw [hgen, aeval_gen_derivative_minpoly K p hp hmon]
  rw [toKx_algebraMap_eq_sum K p hp hc, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, LinearMap.map_smul, ← div_eq_mul_inv, hder, ← hgen]
  have hd : 0 < (pbGen K p hp hmon).dim := by rw [hdim]; exact hp
  rw [← hdim, Finset.sum_eq_single ((pbGen K p hp hmon).dim - 1)]
  · rw [FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self _ hd, smul_eq_mul, mul_one]
  · intro k hk hne
    rw [Finset.mem_range] at hk
    have hk' : k < (pbGen K p hp hmon).dim - 1 := by omega
    rw [FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt _ hk', smul_zero]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

theorem D_ratFuncX_ne_zero :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) ≠ 0 := by
  intro h0
  have hpoly : ∀ q : K[X],
      KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q) = 0 := by
    intro q
    rw [← aeval_ratFuncX K q, Derivation.map_aeval, h0, smul_zero]
  have hall : ∀ f : RatFunc K, KaehlerDifferential.D K (RatFunc K) f = 0 := by
    intro f
    rw [← RatFunc.num_div_denom f, Derivation.leibniz_div, hpoly, hpoly, smul_zero, smul_zero,
      sub_zero, smul_zero]
  have htop := KaehlerDifferential.span_range_derivation (R := K) (S := RatFunc K)
  have hbot : Submodule.span (RatFunc K)
      (Set.range (KaehlerDifferential.D K (RatFunc K))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨f, rfl⟩
    exact hall f
  rw [hbot] at htop
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  exact hx (Submodule.mem_bot (R := RatFunc K) |>.mp (htop.symm ▸ Submodule.mem_top (x := x)))

end P1Tower

end P1TowerPart3

section LocalResidueCompletionC4

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]

-- Re-landed verbatim from the pin's
-- `Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean:185`
-- (`kwHgfV352_localResidueCompletion`); recorded as promotion debt in the P3.2f
-- report because the pin declaration is public and this copy is `private`.
private def kwHgfV352_localResidueCompletion (v : Place K E) (xh : v.adicCompletion) :
    v.ResidueField :=
  v.localResidue (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose

theorem kwHgfV352_localResidueCompletion_spec (v : Place K E) (xh : v.adicCompletion)
    {x : E} (hx : algebraMap E v.adicCompletion x - xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = v.localResidue x := by
  unfold kwHgfV352_localResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x)
      = (algebraMap E v.adicCompletion x₀ - xh) - (algebraMap E v.adicCompletion x - xh) := by
    rw [map_sub]; ring
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hx
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 := v.localResidue_of_mem hov
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem kwHgfV352_localResidueCompletion_algebraMap (v : Place K E) (x : E) :
    kwHgfV352_localResidueCompletion v (algebraMap E v.adicCompletion x) = v.localResidue x :=
  kwHgfV352_localResidueCompletion_spec v _
    (by rw [sub_self]; exact zero_mem _)

end LocalResidueCompletionC4

end AlgebraicCurve


