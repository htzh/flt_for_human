/-
DivisorAction — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.DXCoeff

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve

open RationalFunctionField

namespace Place

/-- Local copy of the pin `private Place.ord_add_eq_left` (pin line 829); the
chunk-1 copy is `private` in this same module and not reachable by name. -/
private theorem ord_add_eq_left' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]

end Place

section WronskianBound

variable {K : Type*} [Field K]

theorem natDegree_numDenomWronskian_lt {n d : K[X]} (hn : n ≠ 0) (hd : d ≠ 0)
    (hW : n.derivative * d - n * d.derivative ≠ 0) :
    (n.derivative * d - n * d.derivative).natDegree < n.natDegree + d.natDegree := by
  have hdeg : (n.derivative * d - n * d.derivative).degree < (n * d).degree := by
    rw [Polynomial.degree_mul]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_right (Polynomial.degree_ne_bot.mpr hd)]
      exact Polynomial.degree_derivative_lt hn
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_left (Polynomial.degree_ne_bot.mpr hn)]
      exact Polynomial.degree_derivative_lt hd
  have h2 := Polynomial.natDegree_lt_natDegree hW hdeg
  rwa [Polynomial.natDegree_mul hn hd] at h2

end WronskianBound

section DXCoeff

variable (K : Type*) [Field K]

def ratFuncDXCoeff (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
    / (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem ratFuncDXCoeff_def (f : RatFunc K) :
    ratFuncDXCoeff K f
      = algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / (algebraMap K[X] (RatFunc K) f.denom) ^ 2 := rfl

theorem D_eq_ratFuncDXCoeff_smul_dX (f : RatFunc K) :
    KaehlerDifferential.D K (RatFunc K) f = ratFuncDXCoeff K f • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [ratFuncDXCoeff_def, div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K f,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd), one_smul]

theorem wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero {f : RatFunc K}
    (h : ratFuncDXCoeff K f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h0
  exact h (by rw [ratFuncDXCoeff_def, h0, _root_.map_zero, zero_div])

end DXCoeff

section FinitePlaces

variable {K : Type*} [Field K]
variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne

  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hord
  omega

theorem ord_algebraMap_num_eq_one_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.num) = 1 := by
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := hord
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord] at h
  omega

theorem not_dvd_wronskian_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) := by
  have hpn' : ¬ p ∣ f.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hf)
      (ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord)
  have hpd : ¬ p ∣ f.denom := fun hpd => by
    have h0 := ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mpr hpd h0
  have hpn : p ∣ f.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hf)).mp ?_
    rw [ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord]
    exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ f.num * f.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ f.num.derivative * f.denom := by
    have h1 := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at h1
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

theorem ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (v).ord (ratFuncDXCoeff K f) = 0 := by
  have hW : ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) :=
    not_dvd_wronskian_of_ord_eq_one hp hwp hsep hf hord
  have hξ0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := fun h =>
    hW (h ▸ dvd_zero p)
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hξ0' : algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hξ0

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)) = 0 := by
    by_contra h
    refine hW ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  refine ⟨div_ne_zero hξ0' (pow_ne_zero 2 hd0), ?_⟩
  rw [ratFuncDXCoeff_def, div_eq_mul_inv,
    (v).ord_mul hξ0' (inv_ne_zero (pow_ne_zero 2 hd0)), (v).ord_inv, hordξ,
    ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord]
  ring

end FinitePlaces

section PlaceInftySide

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

theorem ord_placeInfty_ratFuncDXCoeff_ge {g : RatFunc K} (hg : g ≠ 0)
    (hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0) :
    (p1PlaceInfty K).ord g + 1 ≤ (p1PlaceInfty K).ord (ratFuncDXCoeff K g) := by
  have hn0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hd0 : g.denom ≠ 0 := g.denom_ne_zero
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0

  have hdeg : (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree
      < g.num.natDegree + g.denom.natDegree :=
    natDegree_numDenomWronskian_lt hn0 hd0 hW

  have hcoeff : (p1PlaceInfty K).ord (ratFuncDXCoeff K g)
      = 2 * (g.denom.natDegree : ℤ)
        - (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree := by
    rw [ratFuncDXCoeff_def, ord_placeInfty (div_ne_zero hW' (pow_ne_zero 2 hd')),
      RatFunc.intDegree_div hW' (pow_ne_zero 2 hd'), RatFunc.intDegree_polynomial,
      ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
    push_cast
    ring

  have hgord : (p1PlaceInfty K).ord g = (g.denom.natDegree : ℤ) - g.num.natDegree := by
    rw [ord_placeInfty hg, RatFunc.intDegree]
    ring
  rw [hcoeff, hgord]
  omega

theorem exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero {g : RatFunc K}
    (hg : g ≠ 0) (hord : (p1PlaceInfty K).ord g = 0) :
    ∃ e : RatFunc K, (e = 0 ∨ 2 ≤ (p1PlaceInfty K).ord e) ∧
      KaehlerDifferential.D K (RatFunc K) g = e • dX K := by

  have hmem : RatFunc.inftyValuation K g ≤ 1 := by
    have h1 : g ∈ (p1PlaceInfty K).toValuationSubring :=
      (p1PlaceInfty K).mem_of_ord_nonneg hg hord.symm.le
    rwa [p1PlaceInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at h1

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K hmem

  have hDg : KaehlerDifferential.D K (RatFunc K) g
      = KaehlerDifferential.D K (RatFunc K) (g - algebraMap K (RatFunc K) c) := by
    rw [map_sub, Derivation.map_algebraMap (KaehlerDifferential.D K (RatFunc K)) c, sub_zero]
  rcases hc with hc0 | hcneg
  ·
    exact ⟨0, Or.inl rfl, by rw [hDg, hc0, _root_.map_zero, zero_smul]⟩
  ·
    have hg₁0 : g - algebraMap K (RatFunc K) c ≠ 0 := by
      intro h0
      rw [h0] at hcneg
      simp at hcneg
    refine ⟨ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c), ?_,
      by rw [hDg, D_eq_ratFuncDXCoeff_smul_dX]⟩
    rcases eq_or_ne (ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c)) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hW := wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K h0
      have hge := ord_placeInfty_ratFuncDXCoeff_ge hg₁0 hW
      have hord₁ : 1 ≤ (p1PlaceInfty K).ord (g - algebraMap K (RatFunc K) c) := by
        rw [ord_placeInfty hg₁0]
        omega
      omega

theorem exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one {h : RatFunc K}
    (hh : h ≠ 0) (hord : (p1PlaceInfty K).ord h = -1) :
    ∃ b : RatFunc K, b ≠ 0 ∧ (p1PlaceInfty K).ord b = 0 ∧
      KaehlerDifferential.D K (RatFunc K) h = b • dX K := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXinv : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX

  have hg0 : h * (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := mul_ne_zero hh hXinv
  have hordg : (p1PlaceInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹) = 0 := by
    rw [(p1PlaceInfty K).ord_mul hh hXinv, (p1PlaceInfty K).ord_inv, ord_placeInfty_X, hord]
    ring
  obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg0 hordg

  have hh_eq : h = h * (RatFunc.X : RatFunc K)⁻¹ * RatFunc.X := by
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  have hDh : KaehlerDifferential.D K (RatFunc K) h
      = (h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e) • dX K := by
    conv_lhs => rw [hh_eq]
    rw [Derivation.leibniz, hDe, smul_smul,
      show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) = dX K from rfl,
      ← add_smul]
  rcases he with rfl | he2
  ·
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * 0, ?_, ?_, hDh⟩
    · rw [mul_zero, add_zero]
      exact hg0
    · rw [mul_zero, add_zero]
      exact hordg
  ·
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, (p1PlaceInfty K).ord_zero] at he2
      omega
    have hXe0 : (RatFunc.X : RatFunc K) * e ≠ 0 := mul_ne_zero hX he0
    have hlt : (p1PlaceInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹)
        < (p1PlaceInfty K).ord ((RatFunc.X : RatFunc K) * e) := by
      rw [hordg, (p1PlaceInfty K).ord_mul hX he0, ord_placeInfty_X]
      omega
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e, ?_, ?_, hDh⟩
    ·
      intro hsum
      have hXe_eq : (RatFunc.X : RatFunc K) * e = -(h * (RatFunc.X : RatFunc K)⁻¹) := by
        linear_combination hsum
      rw [hXe_eq, (p1PlaceInfty K).ord_neg] at hlt
      exact lt_irrefl _ hlt
    · rw [(p1PlaceInfty K).ord_add_eq_left' hg0 hXe0 hlt]
      exact hordg

theorem exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one {f : RatFunc K}
    (hf : f ≠ 0) (hord : (p1PlaceInfty K).ord f = 1) :
    ∃ e : RatFunc K, e ≠ 0 ∧ (p1PlaceInfty K).ord e = 2 ∧
      KaehlerDifferential.D K (RatFunc K) f = e • dX K := by

  have hf' : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hord' : (p1PlaceInfty K).ord f⁻¹ = -1 := by
    rw [(p1PlaceInfty K).ord_inv, hord]
  obtain ⟨b, hb0, hbord, hDb⟩ := exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one hf' hord'
  refine ⟨-(f ^ 2 * b), neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hf) hb0), ?_, ?_⟩
  · rw [(p1PlaceInfty K).ord_neg, (p1PlaceInfty K).ord_mul (pow_ne_zero 2 hf) hb0, hbord,
      add_zero, ← zpow_natCast, (p1PlaceInfty K).ord_zpow, hord]
    norm_num
  ·
    conv_lhs => rw [← inv_inv f]
    rw [(KaehlerDifferential.D K (RatFunc K)).leibniz_inv f⁻¹, hDb, inv_inv, smul_smul,
      neg_mul]

end PlaceInftySide

section Glue

variable {K : Type*} [Field K]

theorem exists_ord_zero_smul_of_smul_dX_eq {v : Place K (RatFunc K)} {π π' c c' : RatFunc K}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hord : v.ord c' = v.ord c)
    (hD : KaehlerDifferential.D K (RatFunc K) π = c • dX K)
    (hD' : KaehlerDifferential.D K (RatFunc K) π' = c' • dX K) :
    ∃ u : RatFunc K, v.ord u = 0 ∧
      KaehlerDifferential.D K (RatFunc K) π' = u • KaehlerDifferential.D K (RatFunc K) π := by
  refine ⟨c' / c, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hc' (inv_ne_zero hc), v.ord_inv, hord]
    ring
  · rw [hD, hD', smul_smul, div_mul_cancel₀ _ hc]

end Glue

theorem ordDifferentialWellDefined_ratFunc (K : Type*) [Field K] [CharZero K] :
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
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section ConsumerGates

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ConsumerGates

section NonVacuity

variable (K : Type*) [Field K]

end NonVacuity

section PrincipalPartAtoms

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

theorem two_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    2 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]
  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 2 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

omit [DecidableEq (RatFunc K)] in

theorem not_dvd_of_degree_lt {p c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) : ¬ p ∣ c :=
  fun hdvd => not_lt.mpr (Polynomial.degree_le_of_dvd hdvd hc) hdeg

omit [DecidableEq (RatFunc K)] in

theorem ord_finitePlace_of_degree_lt {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) c) = 0 :=
  not_ne_iff.mp fun h =>
    not_dvd_of_degree_lt K hc hdeg ((ord_finitePlace_ne_zero_iff K hp hc).mp h)

omit [DecidableEq (RatFunc K)] in

theorem ord_finitePlace_p1PrincipalPartAtom {p : K[X]} (hp : Irreducible p)
    {c : K[X]} (hc : c ≠ 0) (hdeg : c.degree < p.degree) (m : ℕ) :
    (finitePlace K hp).ord (p1PrincipalPartAtom K p c m) = -(m : ℤ) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (finitePlace K hp).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (finitePlace K hp).ord_inv, ← zpow_natCast, (finitePlace K hp).ord_zpow,
    ord_finitePlace_of_degree_lt K hp hc hdeg, ord_finitePlace_self K hp]
  ring

end PrincipalPartAtoms

end AlgebraicCurve

end
