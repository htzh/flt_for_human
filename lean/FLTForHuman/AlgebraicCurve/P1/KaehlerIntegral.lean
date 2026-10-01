/-
KaehlerIntegral — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.PerfectPrelude

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential
open AlgebraicCurve.RationalFunctionField KaehlerDifferential
open scoped IntermediateField
open scoped IntermediateField Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
open KaehlerDifferential Module IntermediateField
open AlgebraicCurve

section
section

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Uniqueness

section Profile

variable (K : Type*) [Field K]

theorem exists_smul_dX_eq (ω : Ω[(RatFunc K)⁄K]) : ∃ c : RatFunc K, c • dX K = ω := by
  have hmem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hmem

section ProfileValues

variable [CharZero K] [DecidableEq (RatFunc K)]

theorem ordDifferential_dX_of_ne_placeInfty {v : Place K (RatFunc K)}
    (hv : v ≠ p1PlaceInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX K v hv

theorem ordDifferential_dX_placeInfty :
    (p1PlaceInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K (ordDifferentialWellDefined_ratFunc K)

theorem exists_divisor_smul_dX {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (p1PlaceInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (p1PlaceInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty K hne, Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end ProfileValues

section Instance

variable [CharZero K]

scoped instance instHasCanonicalDivisorRatFunc :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end Instance

section ExactDivisor

variable [CharZero K] [DecidableEq (RatFunc K)]

end ExactDivisor

end Profile

section RatDiamond

end RatDiamond

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


end ModularCurve

section AxiomAudit

end AxiomAudit

end
end

end

section
section

set_option linter.unusedSectionVars false

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField



section KaehlerToolbox

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place
variable (v : Place K F)
end Place
end KaehlerToolbox
section DXCoeffIntegrality
variable {K : Type*} [Field K]
theorem ratFuncDXCoeff_eq_of_D_eq_smul_dX {f e : RatFunc K}
    (h : KaehlerDifferential.D K (RatFunc K) f = e • dX K) : ratFuncDXCoeff K f = e := by
  have key : (ratFuncDXCoeff K f - e) • dX K = 0 := by
    rw [sub_smul, ← D_eq_ratFuncDXCoeff_smul_dX K f, h, sub_self]
  rcases smul_eq_zero.mp key with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (dX_ne_zero K)

theorem ratFuncDXCoeff_zero : ratFuncDXCoeff K (0 : RatFunc K) = 0 :=
  ratFuncDXCoeff_eq_of_D_eq_smul_dX (by rw [_root_.map_zero, zero_smul])

section FinitePlaces

variable {w : HeightOneSpectrum K[X]}

local notation "vw" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_eq_zero_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : 0 ≤ (vw).ord f) :
    (vw).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne
  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (vw).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (vw).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (vw).ord_mul hnum0 (inv_ne_zero hden0),
    (vw).ord_inv, hordn] at hord
  omega

theorem ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {g : RatFunc K}
    (hg : g ≠ 0) (hord : 0 ≤ (vw).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 0 ≤ (vw).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
    wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have hWord : 0 ≤ (vw).ord (algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative)) :=
    (vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)
  have hden : (vw).ord (algebraMap K[X] (RatFunc K) g.denom) = 0 :=
    ord_algebraMap_denom_eq_zero_of_ord_nonneg hp hwp hg hord
  have key : (vw).ord (ratFuncDXCoeff K g)
      = (vw).ord (algebraMap K[X] (RatFunc K)
          (g.num.derivative * g.denom - g.num * g.denom.derivative))
        - 2 * (vw).ord (algebraMap K[X] (RatFunc K) g.denom) := by
    rw [ratFuncDXCoeff_def, div_eq_mul_inv,
      (vw).ord_mul hW' (inv_ne_zero (pow_ne_zero 2 hd')), (vw).ord_inv, ← zpow_natCast,
      (vw).ord_zpow]
    push_cast
    ring
  rw [key, hden]
  omega

end FinitePlaces

section PlaceInftySide

variable [DecidableEq (RatFunc K)]

theorem ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
    {f : RatFunc K} (hf : f ≠ 0) (hord : (p1PlaceInfty K).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (p1PlaceInfty K).ord (ratFuncDXCoeff K f) = 2 := by
  obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hf hord
  rw [ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe]
  exact ⟨he0, heord⟩

theorem ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg
    {g : RatFunc K} (hg : g ≠ 0) (hord : 0 ≤ (p1PlaceInfty K).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 2 ≤ (p1PlaceInfty K).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  rcases eq_or_lt_of_le hord with heq | hlt
  ·
    obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg heq.symm
    have hee := ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe
    rcases he with rfl | h2
    · exact absurd hee hne
    · rw [hee]; exact h2
  ·
    have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
      wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
    have h := ord_placeInfty_ratFuncDXCoeff_ge hg hW
    omega

end PlaceInftySide

end DXCoeffIntegrality

section LemmaA

variable {K : Type*} [Field K] [CharZero K]

theorem ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  ·
    refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((p1PlaceInfty K).uniformizer_ne_zero) ((p1PlaceInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        hp.separable (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (p1PlaceInfty K).uniformizer)
          ((p1PlaceInfty K).uniformizer_ne_zero) ((p1PlaceInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem differentialCoeff_D_eq_ratFuncDXCoeff_div (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem differentialCoeff_D_mem_of_mem (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ := ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le v hg
  rw [differentialCoeff_D_eq_ratFuncDXCoeff_div v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaA

section ExactDifferentialEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place

variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj [CharZero K]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn

  have hres : R.res (v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    omega

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]

theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {π' : F} (hπ' : v.ord π' = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1 := by
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'
  have hπv0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero

  set w : F := π' * (v.uniformizer)⁻¹ with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero hπ'0 (inv_ne_zero hπv0)
  have hword : v.ord w = 0 := by
    rw [hw_def, v.ord_mul hπ'0 (inv_ne_zero hπv0), v.ord_inv, hπ', v.ord_uniformizer]
    ring
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinvmem : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword]
    omega

  have hπ'_eq : π' = v.uniformizer * w := by
    rw [hw_def, mul_comm π' (v.uniformizer)⁻¹, ← mul_assoc, mul_inv_cancel₀ hπv0, one_mul]

  have hD : KaehlerDifferential.D K F π'
      = v.uniformizer • KaehlerDifferential.D K F w
        + w • KaehlerDifferential.D K F v.uniformizer := by
    conv_lhs => rw [hπ'_eq]
    exact Derivation.leibniz _ _ _

  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F π')
      = v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) + w := by
    rw [hD, v.differentialCoeff_add'', v.differentialCoeff_smul, v.differentialCoeff_smul,
      show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
      v.differentialCoeff_dCoord, mul_one]

  have hsplit : v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹ + (v.uniformizer)⁻¹ := by
    rw [hcoeff, hπ'_eq, mul_inv]
    field_simp
  rw [hsplit, map_add, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
    R.res_of_mem _ (mul_mem (hint w hwmem) hwinvmem), zero_add]

end Place

end ExactDifferentialEngine

section RatFuncClauses

variable {K : Type*} [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc
    (v : Place K (RatFunc K)) (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : RatFunc K) (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj v hsurj
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R π' hn

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc
    (v : Place K (RatFunc K)) {π' : RatFunc K} (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π') * (π')⁻¹) = 1 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R hπ'

end RatFuncClauses

theorem canonicalLocalResidueKSimplePoleCoordIndep_ratFunc (K : Type*) [Field K] [CharZero K]
    [HasCanonicalLocalResidueKStar K (RatFunc K)] :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R => canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc v hπ' R

section PlaceInftyConsumers

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty
    (π' : RatFunc K) (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res ((p1PlaceInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc (p1PlaceInfty K)
    (surjective_algebraMap_residueField_placeInfty K) π' R hn

theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty K
    (RatFunc.X : RatFunc K)⁻¹ R (Nat.le_add_left 1 n)

theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (p1PlaceInfty K)
          * (p1PlaceInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply, canonicalLocalResidueDataK_res_X_pow_mul_D_X K R n, _root_.map_zero]

end PlaceInftyConsumers

section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem surjective_algebraMap_residueField_of_deg_eq_one {F : Type*} [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem surjective_algebraMap_residueField_ratFunc_of_isAlgClosed [IsAlgClosed K]
    (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine surjective_algebraMap_residueField_of_deg_eq_one K _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

variable [IsAlgClosed K]

theorem canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' _ R _ hn =>
    canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc v
      (surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v) π' R hn

end AlgClosedDischarge

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end

end

end

end
