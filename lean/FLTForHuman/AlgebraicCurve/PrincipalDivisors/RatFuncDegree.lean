/-
The `P¹` places and degree: the classification of the places of `K(t)`, the
finiteness of the pole/zero support, and the `P¹` base case of
`HasPrincipalDivisors`, after FLT's ten `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_*.lean`
files
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean>).

The eleven nodes are public at the `Theorems/Thm_AlgebraicCurve_RationalFunctionField_*`
wrappers' binders. Ten are proved here; `deg_ofHeightOneSpectrum` was already
written by AC0 in `Defs/RatFuncPlaces.lean` (it is the same declaration the pin
re-exports under `P2M.Dup`), so it is not written twice (`TOPIC-t8-ratfunc-degree.md`
§2.3).

The pin ships each of the first three nodes with a private bridge block (`'`-copies
of AC0's `Place.adicValuation_valuationSubring`, `mem_iff_adicValuation_le_one`,
`isEquiv_adicValuation_of_valuationSubring_eq`,
`ord_eq_zero_iff_adicValuation_eq_one`,
`isEquiv_adicValuation_ofHeightOneSpectrum` and
`RationalFunctionField.{nontrivial_valueGroup_inftyValuation, placeInfty}`);
≈214 content lines never written, because AC0 already wrote the public originals.
The port writes only the genuinely T8-local private helpers: the dichotomy
`eq_ofHeightOneSpectrum_or_eq_placeInfty`, `placeInfty_ne_ofHeightOneSpectrum`,
`finite_setOf_valuation_ne_one`, the `WFg` helper
`exists_sub_algebraMap_intDegree_neg`, and the three `WFj` helpers
(`ne_finitePlace_of_forall_ne`, `single_add_single_apply_eq_ord`,
`degree_single_add_single`).

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.RatFuncPlaces
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

-- The `RatFunc.inftyValuation` API needs `DecidableEq (RatFunc K)` in v4.34; the
-- `classical`-provided instance is installed as a local instance in the proofs.
-- The pin's `haveI` walls are kept literal (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

/-! ## The `P¹` dichotomy and the three classification nodes -/

/-- Every place of `K(t)` is either a finite place `ofHeightOneSpectrum w` or the
place at infinity. This is Ostrowski (`RatFunc.valuation_isEquiv_infty_or_adic`)
read through the public AC0 bridge lemmas; the pin repeats it privately in each of
the first three `S_` files, the port writes it once. -/
private theorem eq_ofHeightOneSpectrum_or_eq_placeInfty {K : Type*} [Field K]
    [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) :
    (∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
        v = Place.ofHeightOneSpectrum w) ∨
      v = placeInfty K := by
  haveI := v.adicValuation_isRankOneDiscrete
  haveI := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · refine Or.inr (Place.ext ?_)
    rw [placeInfty_toValuationSubring]
    exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

/-- The place at infinity is not a finite place. -/
private theorem placeInfty_ne_ofHeightOneSpectrum {K : Type*} [Field K]
    [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

theorem subsingleton_setOf_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] :
    {v : Place K (RatFunc K) | ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w}.Subsingleton := by
  classical
  intro v hv v' hv'
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, h⟩ | h
  · exact absurd h (hv w)
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v' with ⟨w, h'⟩ | h'
  · exact absurd h' (hv' w)
  rw [h, h']

theorem exists_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] :
    ∃ v : Place K (RatFunc K),
      ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
        v ≠ Place.ofHeightOneSpectrum w := by
  classical
  exact ⟨placeInfty K, fun w => placeInfty_ne_ofHeightOneSpectrum w⟩

theorem toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K]
    [DecidableEq (RatFunc K)] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) :
    v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  haveI := v.adicValuation_isRankOneDiscrete
  haveI := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)

/-- Finiteness of the set of finite places at which `f` has nonzero valuation: the
primes dividing the numerator or the denominator. T8-local and `private`. -/
private theorem finite_setOf_valuation_ne_one {K : Type*} [Field K] {f : RatFunc K}
    (hf : f ≠ 0) :
    {w : IsDedekindDomain.HeightOneSpectrum (Polynomial K) |
      w.valuation (RatFunc K) f ≠ 1}.Finite := by
  have hnum : (Ideal.span {f.num} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using RatFunc.num_ne_zero hf
  have hden : (Ideal.span {f.denom} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using f.denom_ne_zero
  refine Set.Finite.subset ((Ideal.finite_factors hnum).union (Ideal.finite_factors hden))
    fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Ideal.dvd_span_singleton] at hcon
  refine hw ?_
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.1
  have h2 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.2
  rw [show f = algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom from
    f.num_div_denom.symm, map_div₀, h1, h2]
  exact div_one 1

theorem finite_setOf_ord_ne_zero {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.image (Place.ofHeightOneSpectrum (K := K))
        (finite_setOf_valuation_ne_one hf))
      (Set.Subsingleton.finite subsingleton_setOf_forall_ne_ofHeightOneSpectrum))
    fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
  by_cases hcase : ∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hcase
    refine Or.inl ⟨w, fun hone => hv ?_, rfl⟩
    exact ((Place.ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hf).mpr
      ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := RatFunc K)
        w).eq_one_iff_eq_one.mp hone)
  · exact Or.inr fun w h => hcase ⟨w, h⟩

/-! ## The `ord` leaves at the finite places and at infinity -/

theorem ord_ofHeightOneSpectrum_eq_neg_log {K : Type*} [Field K]
    (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0)
    (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f =
      -WithZero.log (w.valuation (RatFunc K) f) := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  exact (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval hf

theorem ord_ofHeightOneSpectrum_of_span {K : Type*} [Field K]
    (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0)
    (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [ord_ofHeightOneSpectrum_eq_neg_log w hp hw (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]

theorem ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K]
    (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) {f : RatFunc K} (hf : f ≠ 0) :
    v.ord f = -f.intDegree := by
  classical
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [v.ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K)
      (toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum v hv).symm hπ hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

/-! ## The residue-field computation at infinity (`deg = 1`) -/

/-- The pin's `WFg` helper: a rational function of `∞`-valuation `≤ 1` differs from
a constant by something of negative `intDegree`. T8-local and `private`. -/
private theorem exists_sub_algebraMap_intDegree_neg {K : Type*} [Field K]
    [DecidableEq (RatFunc K)] {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩
  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt_left hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

theorem deg_eq_one_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K]
    (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) : v.deg = 1 := by
  classical
  have hvS : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring :=
    toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum v hv
  have hequiv : (RatFunc.inftyValuation K).IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hvS.symm
  have hbij : Function.Bijective (Algebra.ofId K v.ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K v.ResidueField).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      have hx' : RatFunc.inftyValuation K x ≤ 1 := by
        rw [hvS] at hx
        exact (Valuation.mem_valuationSubring_iff _ _).mp hx
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg hx'
      refine ⟨c, ?_⟩
      show IsLocalRing.residue _ (algebraMap K v.toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      show v.adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← hequiv.lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-! ## The `P¹` base case of `HasPrincipalDivisors` -/

/-- The pin's `WFj` helper: a finite place is not a place with no finite part. -/
private theorem ne_finitePlace_of_forall_ne {K : Type*} [Field K] {v : Place K (RatFunc K)}
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) {p : Polynomial K} (hp : Irreducible p) :
    v ≠ finitePlace K hp :=
  hv _

/-- The pin's `WFj` helper: the explicit divisor `(finitePlace p) - (deg p)·∞`
evaluates to `ord (p)` at every place. T8-local and `private`. -/
private theorem single_add_single_apply_eq_ord {K : Type*} [Field K]
    {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      vinf ≠ Place.ofHeightOneSpectrum w) {p : Polynomial K} (hp : Irreducible p)
    (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap (Polynomial K) (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  by_cases hfin : ∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hfin
    rw [Finsupp.single_eq_of_ne (hvinf w).symm, add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    · rw [Finsupp.single_eq_of_ne hcase]
      symm
      by_contra hne
      refine hcase ?_
      have hmem : p ∈ w.asIdeal :=
        (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp0).mp hne
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp]
      rfl
  · have hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
        v ≠ Place.ofHeightOneSpectrum w := fun w h => hfin ⟨w, h⟩
    have hveq : v = vinf := subsingleton_setOf_forall_ne_ofHeightOneSpectrum hv hvinf
    rw [Finsupp.single_eq_of_ne (show v ≠ finitePlace K hp from hv _), zero_add, hveq,
      Finsupp.single_eq_same,
      ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum vinf hvinf
        (RatFunc.algebraMap_ne_zero hp0),
      RatFunc.intDegree_polynomial]

/-- The pin's `WFj` helper: the explicit `P¹` divisor of a prime polynomial has
degree zero. T8-local and `private`. -/
private theorem degree_single_add_single {K : Type*} [Field K]
    {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      vinf ≠ Place.ofHeightOneSpectrum w) {p : Polynomial K} (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single,
    show (finitePlace K hp).deg = p.natDegree from
      deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp),
    deg_eq_one_of_forall_ne_ofHeightOneSpectrum vinf hvinf]
  push_cast
  ring

theorem degree_eq_zero_of_forall_eq_ord_algebraMap {K : Type*} [Field K] (q : Polynomial K) :
    ∀ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) →
        Divisor.degree D = 0 := by
  classical
  obtain ⟨vinf, hvinf⟩ := exists_forall_ne_ofHeightOneSpectrum (K := K)
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro D hD
    have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · intro x hx D hD
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hx
    have hC : (algebraMap K[X] (RatFunc K)) (Polynomial.C r) = algebraMap K (RatFunc K) r := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have hzero : D = 0 := by
      ext v
      rw [hD v, hC, v.ord_algebraMap]
      simp
    rw [hzero, map_zero]
  · intro a p ha hp ih D hD
    have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
    have ha' : algebraMap K[X] (RatFunc K) a ≠ 0 := RatFunc.algebraMap_ne_zero ha
    set Dp : Divisor K (RatFunc K) :=
      Finsupp.single (finitePlace K hp.irreducible) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ)) with hDp_def
    have hDp : ∀ v : Place K (RatFunc K), Dp v = v.ord (algebraMap K[X] (RatFunc K) p) :=
      fun v => single_add_single_apply_eq_ord hvinf hp.irreducible v
    have hDa : ∀ v : Place K (RatFunc K),
        (D - Dp) v = v.ord (algebraMap K[X] (RatFunc K) a) := by
      intro v
      rw [Finsupp.sub_apply, hD v, hDp v, map_mul, v.ord_mul hp' ha']
      ring
    have hdeg_p : Divisor.degree Dp = 0 :=
      degree_single_add_single hvinf hp.irreducible
    have hdeg_a : Divisor.degree (D - Dp) = 0 := ih (D - Dp) hDa
    have hsplit : D = Dp + (D - Dp) := by abel
    rw [hsplit, map_add, hdeg_p, zero_add]
    exact hdeg_a

theorem degree_eq_zero_of_forall_eq_ord {K : Type*} [Field K] {f : RatFunc K}
    (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) :
    Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · have hden : f.denom ≠ 0 := f.denom_ne_zero
    have hdenF : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden

    set Dden : Divisor K (RatFunc K) :=
      Finsupp.ofSupportFinite
        (fun v : Place K (RatFunc K) => v.ord (algebraMap K[X] (RatFunc K) f.denom))
        (finite_setOf_ord_ne_zero hdenF) with hDden_def
    have hDden : ∀ v : Place K (RatFunc K),
        Dden v = v.ord (algebraMap K[X] (RatFunc K) f.denom) := fun v => rfl
    have hsplit : ∀ v : Place K (RatFunc K),
        (D + Dden) v = v.ord (algebraMap K[X] (RatFunc K) f.num) := by
      intro v
      rw [Finsupp.add_apply, hD v, hDden v]
      have hmul : f * algebraMap K[X] (RatFunc K) f.denom
          = algebraMap K[X] (RatFunc K) f.num :=
        ((div_eq_iff hdenF).mp f.num_div_denom).symm
      have h2 := v.ord_mul hf hdenF
      rw [hmul] at h2
      exact h2.symm
    have h1 := degree_eq_zero_of_forall_eq_ord_algebraMap
      f.num (D + Dden) hsplit
    have h2 := degree_eq_zero_of_forall_eq_ord_algebraMap
      f.denom Dden hDden
    rw [map_add, h2, add_zero] at h1
    exact h1

end RationalFunctionField

end AlgebraicCurve
