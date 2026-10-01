/-
UnitNormalForm — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.Differential

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing KaehlerDifferential
open scoped Polynomial
open scoped AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve

open RationalFunctionField

variable (K : Type*) [Field K]

/-- Pin row #212. -/
abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

/-- Pin row #213. -/
theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

/-- Pin row #214. -/
theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

/-- Pin row #215. -/
theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

/-- Pin row #216. -/
theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero

  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

/-- Pin row #217. -/
theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

/-- Pin row #218. -/
theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  ·
    exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

variable {K}

/-- Pin row #219. -/
theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_

  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by simp [h])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

section NumDenom

variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

/-- Pin row #220. -/
private theorem uniformizer_ne_zero' : (v).uniformizer ≠ 0 :=
  (v).uniformizer_ne_zero

/-- Pin row #221. -/
theorem ord_algebraMap_denom_uniformizer_eq_zero {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.denom) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  by_contra hne

  have hpd : p ∣ π.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ π.num := fun hpn =>
    hp.not_isUnit (π.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) π.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hπne)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) π.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)) (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hordπ
  omega

/-- Pin row #222. -/
theorem ord_algebraMap_num_uniformizer_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.num) = 1 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_uniformizer_eq_zero hp hwp] at hordπ
  omega

/-- Pin row #223. -/
theorem not_dvd_num'denom_sub_numdenom' {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ¬ p ∣ ((v).uniformizer.num.derivative * (v).uniformizer.denom
            - (v).uniformizer.num * (v).uniformizer.denom.derivative) := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hpn' : ¬ p ∣ π.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hπne)
      (ord_algebraMap_num_uniformizer_eq_one hp hwp)
  have hpd : ¬ p ∣ π.denom := fun hpd => by
    have := ord_algebraMap_denom_uniformizer_eq_zero (w := w) hp hwp
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mpr hpd this
  have hpn : p ∣ π.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hπne)).mp ?_
    rw [ord_algebraMap_num_uniformizer_eq_one hp hwp]; exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ π.num * π.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ π.num.derivative * π.denom := by
    have := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at this
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

end NumDenom

section PerPlace

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

/-- Pin row #224. -/
theorem ord_differentialCoeff_dX_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).ord ((v).differentialCoeff (dX K)) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  set ξ : K[X] := π.num.derivative * π.denom - π.num * π.denom.derivative with hξ
  have hd0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero

  have hcoord : (v).dCoord
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2) • dX K := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K π, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
    rfl

  have hξ0 : ξ ≠ 0 := by
    intro h; rw [hξ] at h
    exact not_dvd_num'denom_sub_numdenom' hp hwp hsep (h ▸ dvd_zero p)
  have hcoeff0 : algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2 ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (pow_ne_zero 2 hd0)

  have hcoeff : (v).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2)⁻¹ := by
    refine (v).differentialCoeff_unique ?_
    rw [hcoord, smul_smul, inv_mul_cancel₀ hcoeff0, one_smul]

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K) ξ) = 0 := by
    by_contra h
    refine not_dvd_num'denom_sub_numdenom' hp hwp hsep ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  rw [hcoeff, (v).ord_inv, div_eq_mul_inv,
    (v).ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (inv_ne_zero (pow_ne_zero 2 hd0)),
    hordξ, (v).ord_inv, ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_uniformizer_eq_zero hp hwp]
  ring

/-- Pin row #225. -/
theorem differentialCoeff_dX_mem_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).differentialCoeff (dX K) ∈ (v).toValuationSubring :=
  (v).mem_of_ord_nonneg ((v).differentialCoeff_ne_zero (dX_ne_zero K))
    (ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp hsep).ge

end PerPlace

section Discharge

variable (K)
variable [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [HasPrincipalDivisors K (RatFunc K)] in

/-- Pin row #226. -/
theorem p1DifferentialCoeffRegularFinite_dX :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact differentialCoeff_dX_mem_ofHeightOneSpectrum hp hwp hp.separable
  · exact absurd rfl hvinf

end Discharge

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

omit [DecidableEq (RatFunc K)] in

/-- Pin row #227. -/
theorem ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne
    (w : HeightOneSpectrum K[X]) {p : K[X]} (hp : Irreducible p)
    (hne : w ≠ heightOneSpectrumOfIrreducible K hp) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 0 := by
  by_contra hord
  refine hne (HeightOneSpectrum.ext ?_)
  have hmem : p ∈ w.asIdeal :=
    (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp.ne_zero).mp hord

  exact ((PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le
    (w.isPrime.isMaximal w.ne_bot).ne_top
    ((Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hmem)).symm

/-- Pin row #228. -/
theorem ord_algebraMap_irreducible_eq_zero_of_ne
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ p1PlaceInfty K) :
    v.ord (algebraMap K[X] (RatFunc K) p) = 0 := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · refine ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne K w hp ?_
    rintro rfl; exact hvp rfl
  · exact absurd rfl hvinf

/-- Pin row #229. -/
theorem inv_algebraMap_pow_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ p1PlaceInfty K) (m : ℕ) :
    ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹ ∈ v.toValuationSubring := by
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
  refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero m hp0)) ?_
  rw [v.ord_inv, ← zpow_natCast, v.ord_zpow,
    ord_algebraMap_irreducible_eq_zero_of_ne K hp hvp hvinf, mul_zero, _root_.neg_zero]

/-- Pin row #230. -/
theorem p1PrincipalPartAtom_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ p1PlaceInfty K) :
    p1PrincipalPartAtom K p c m ∈ v.toValuationSubring := by
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv]
  exact mul_mem (algebraMap_polynomial_mem_of_ne_placeInfty' K hvinf c)
    (inv_algebraMap_pow_mem_of_ne_finitePlace K hp hvp hvinf m)

/-- Pin row #231. -/
theorem ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : p ≠ 0) {c : K[X]} (hc : c ≠ 0) (m : ℕ) :
    (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m)
      = (m : ℤ) * p.natDegree - c.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (p1PlaceInfty K).ord_inv, ← zpow_natCast, (p1PlaceInfty K).ord_zpow,
    ord_placeInfty_algebraMap' K hc, ord_placeInfty_algebraMap' K hp]
  ring

/-- Pin row #232. -/
theorem one_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    1 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]

  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 1 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

end AlgebraicCurve

end
