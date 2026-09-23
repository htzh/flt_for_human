/-
The `Place` vocabulary of the generic curve layer, after FLT's
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` lines 22–179 and 456–485
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean>).

A `Place K F` is FLT's shape: a `ValuationSubring F` with three side conditions
(the constants lie in it, it is not all of `F`, and it is a principal ideal
ring). The bridge to mathlib's valuation API is built inside the structure:
`heightOneSpectrum` is `IsDiscreteValuationRing.maximalIdeal`, `adicValuation`
is that spectrum's valuation, and `ord f = -(WithZero.log (v.adicValuation f))`.

T1's ord interface lives here too, beside the object it concerns; see
`TOPIC-t1-ord-interface.md` §1.
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Bezout

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

structure Place where

  toValuationSubring : ValuationSubring F

  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring

  ne_top' : toValuationSubring ≠ ⊤

  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring

theorem _root_.ValuationSubring.not_isField_of_ne_top {A : ValuationSubring F} (hA : A ≠ ⊤) :
    ¬IsField A := by
  intro hf
  apply hA
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  by_cases hx : x ∈ A
  · exact hx
  ·

    exfalso
    have hx0 : x ≠ 0 := fun h => hx (h ▸ A.zero_mem)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hxi0 : (⟨x⁻¹, hxi⟩ : A) ≠ 0 := by
      simp only [ne_eq, Subtype.ext_iff]
      exact inv_ne_zero hx0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hxi0
    have hb' : x⁻¹ * (b : F) = 1 := by
      have h := congrArg (Subtype.val) hb
      simpa using h
    have hbx : (b : F) = x := by
      field_simp at hb'
      exact hb'
    exact hx (hbx ▸ b.2)

namespace Place

variable {K F}

theorem toValuationSubring_injective :
    Function.Injective (toValuationSubring (K := K) (F := F)) := by
  rintro ⟨a, _, _, _⟩ ⟨b, _, _, _⟩ (rfl : a = b)
  rfl

@[ext]
theorem ext {v w : Place K F} (h : v.toValuationSubring = w.toValuationSubring) : v = w :=
  toValuationSubring_injective h

variable (v : Place K F)

instance : IsPrincipalIdealRing v.toValuationSubring := v.isPrincipalIdealRing'

instance : IsDiscreteValuationRing v.toValuationSubring where
  not_a_field' := by
    rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact ValuationSubring.not_isField_of_ne_top F v.ne_top'

instance : Algebra K v.toValuationSubring :=
  ((algebraMap K F).codRestrict v.toValuationSubring.toSubring v.algebraMap_mem').toAlgebra

@[simp]
theorem coe_algebraMap (a : K) :
    (algebraMap K v.toValuationSubring a : F) = algebraMap K F a := rfl

instance : IsScalarTower K v.toValuationSubring F :=
  IsScalarTower.of_algebraMap_eq fun a => (v.coe_algebraMap a).symm

abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

def deg : ℕ := Module.finrank K v.ResidueField

class FiniteResidue : Prop where
  finite : Module.Finite K v.ResidueField

def heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=
  IsDiscreteValuationRing.maximalIdeal _

@[simp]
theorem heightOneSpectrum_asIdeal :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring := rfl

def adicValuation : Valuation F ℤᵐ⁰ := v.heightOneSpectrum.valuation F

theorem adicValuation_ne_zero {f : F} (hf : f ≠ 0) : v.adicValuation f ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hf

theorem adicValuation_coe (a : v.toValuationSubring) :
    v.adicValuation (a : F) = v.heightOneSpectrum.intValuation a := by
  simpa [adicValuation] using v.heightOneSpectrum.valuation_of_algebraMap (K := F) a

theorem adicValuation_coe_eq_one_iff (a : v.toValuationSubring) :
    v.adicValuation (a : F) = 1 ↔ IsUnit a := by
  rw [v.adicValuation_coe, HeightOneSpectrum.intValuation_eq_one_iff, heightOneSpectrum_asIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem adicValuation_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.adicValuation (π : F) = exp (-1 : ℤ) := by
  rw [v.adicValuation_coe]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero
    (by rw [heightOneSpectrum_asIdeal, hπ.maximalIdeal_eq])

def ord (f : F) : ℤ := -(WithZero.log (v.adicValuation f))

@[simp]
theorem ord_zero : v.ord (0 : F) = 0 := by simp [ord]

@[simp]
theorem ord_one : v.ord (1 : F) = 0 := by simp [ord]

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f * g) = v.ord f + v.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul (v.adicValuation_ne_zero hf) (v.adicValuation_ne_zero hg)]
  ring

theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · simp only [ord, map_inv₀, WithZero.log_inv, neg_neg]

theorem ord_coe_unit (u : v.toValuationSubringˣ) :
    v.ord ((u : v.toValuationSubring) : F) = 0 := by
  simp [ord, (v.adicValuation_coe_eq_one_iff _).mpr u.isUnit]

theorem ord_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.ord (π : F) = 1 := by
  simp [ord, v.adicValuation_coe_irreducible hπ]

theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  simp only [ord, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem ord_unit_smul_zpow (u : v.toValuationSubringˣ) {π : v.toValuationSubring}
    (hπ : Irreducible π) (n : ℤ) :
    v.ord (((u : v.toValuationSubring) : F) * ((π : F) ^ n)) = n := by
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hu : ((u : v.toValuationSubring) : F) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  rw [v.ord_mul hu (zpow_ne_zero n hπF), v.ord_coe_unit u, zero_add,
    v.ord_zpow _ _, v.ord_coe_irreducible hπ, mul_one]

theorem exists_unit_mul_zpow {f : F} (hf : f ≠ 0) {π : v.toValuationSubring}
    (hπ : Irreducible π) :
    ∃ u : v.toValuationSubringˣ,
      f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord f)) := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := F) hπ hf
  rw [Units.smul_def, Algebra.smul_def] at hu
  have hcoe : algebraMap v.toValuationSubring F (u : v.toValuationSubring)
      = ((u : v.toValuationSubring) : F) := rfl
  have hcoe' : algebraMap v.toValuationSubring F π = (π : F) := rfl
  rw [hcoe, hcoe'] at hu
  have hn : v.ord f = n := by rw [hu]; exact v.ord_unit_smul_zpow u hπ n
  exact ⟨u, by rw [hn, hu]⟩

end Place

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in

theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]

  infer_instance

open IsDedekindDomain.HeightOneSpectrum in

def ofHeightOneSpectrum [Algebra K R] [IsScalarTower K R F] (w : HeightOneSpectrum R) :
    Place K F where
  toValuationSubring := (w.valuation F).valuationSubring
  algebraMap_mem' := fun a => by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact w.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring w

@[simp]
theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

/-! ## T1: the ord/valuation interface

The statements below are the `Theorems/Thm_AlgebraicCurve_*.lean` wrappers
verbatim (the checker is textual), with the wrappers' explicit binders. They live
beside the object they concern rather than in a separate `OrdInterface` module
(`TOPIC-t1-ord-interface.md` §1). -/

namespace Place

private theorem isUnit_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {c : K} (hc : c ≠ 0) :
    IsUnit (algebraMap K v.toValuationSubring c) :=
  (isUnit_iff_ne_zero.mpr hc).map _

private theorem adicValuation_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  rw [← v.coe_algebraMap]
  exact (v.adicValuation_coe_eq_one_iff _).mpr (v.isUnit_algebraMap hc)

theorem ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · simp only [ord, v.adicValuation_algebraMap hc, log_one, neg_zero]

theorem ord_smul_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [smul_zero]
  · have halg : algebraMap K F c ≠ 0 :=
      fun h => hc ((algebraMap K F).injective (by rw [h, map_zero]))
    rw [Algebra.smul_def, v.ord_mul halg hx0, v.ord_algebraMap c, zero_add]

theorem adicValuation_valuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) : v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

theorem mem_iff_adicValuation_le_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} : f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

theorem isEquiv_adicValuation_of_valuationSubring_eq {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation F Γ} (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring.symm)

theorem mem_maximalIdeal_iff_adicValuation_lt_one {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    lt_iff_le_and_ne]
  have hle : v.adicValuation (a : F) ≤ 1 := v.mem_iff_adicValuation_le_one.mp a.2
  tauto

private theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

theorem ord_eq_neg_log_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (w : Valuation F (WithZero (Multiplicative ℤ)))
    (hw : w.valuationSubring = v.toValuationSubring) {π : F}
    (hπ : w π = WithZero.exp (-1 : ℤ)) {f : F} (hf : f ≠ 0) : v.ord f = -WithZero.log (w f) := by
  have hequiv : w.IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hw
  have hexp_lt : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl]
    exact exp_lt_exp.mpr (by omega)
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hadic_π₀ : v.adicValuation (π₀ : F) = exp (-1 : ℤ) := v.adicValuation_coe_irreducible hπ₀

  have hwπ₀ : w (π₀ : F) = exp (-1 : ℤ) := by
    refine le_antisymm (le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mpr ?_)) ?_
    · rw [hadic_π₀]
      exact hexp_lt
    · rw [← hπ]
      refine (hequiv π π₀).mpr ?_
      rw [hadic_π₀]
      refine le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mp ?_)
      rw [hπ]
      exact hexp_lt
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  have hwu : w ((u : v.toValuationSubring) : F) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr ((v.adicValuation_coe_eq_one_iff _).mpr u.isUnit)
  set n := v.ord f with hn
  rw [hu, map_mul, map_zpow₀, hwu, hwπ₀, one_mul, log_zpow, log_exp, smul_eq_mul]
  ring

theorem adicValuation_isRankOneDiscrete {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

theorem adicValuation_isTrivialOn {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

private def placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    Subalgebra K F :=
  { v.toValuationSubring.toSubring.toSubsemiring with algebraMap_mem' := v.algebraMap_mem' }

private theorem mem_placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {y : F} :
    y ∈ placeSubalgebra v ↔ y ∈ v.toValuationSubring := Iff.rfl

private theorem valuationSubring_integers {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) :
    (v.toValuationSubring.valuation).Integers v.toValuationSubring :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun a => v.toValuationSubring.valuation_le_one a
    exists_of_le_one := fun {r} hr =>
      ⟨⟨r, v.toValuationSubring.mem_of_valuation_le_one r hr⟩, rfl⟩ }

theorem mem_toValuationSubring_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by
  have hle : Algebra.adjoin K {j} ≤ placeSubalgebra v :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_placeSubalgebra v).mpr hj))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(v.toValuationSubring) :=
    { toFun := fun a => ⟨(a : F), (mem_placeSubalgebra v).mp (hle a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hOx : IsIntegral (↥v.toValuationSubring) x :=
    IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
  exact v.toValuationSubring.mem_of_valuation_le_one x
    ((valuationSubring_integers v).isIntegral_iff_v_le_one.mp hOx)

theorem ord_eq_zero_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) (hx' : IsIntegral (Algebra.adjoin K {j}) x⁻¹) :
    v.ord x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact v.ord_zero
  · have hxa : x ∈ v.toValuationSubring :=
      v.mem_toValuationSubring_of_isIntegral_adjoin hj hx
    have hxi : x⁻¹ ∈ v.toValuationSubring :=
      v.mem_toValuationSubring_of_isIntegral_adjoin hj hx'
    have hunit : IsUnit (⟨x, hxa⟩ : v.toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hxi⟩, ?_⟩
      ext
      simp [mul_inv_cancel₀ hx0]
    have h1 : v.adicValuation x = 1 :=
      (v.adicValuation_coe_eq_one_iff ⟨x, hxa⟩).mpr hunit
    simp [ord, h1]

end Place

end AlgebraicCurve
