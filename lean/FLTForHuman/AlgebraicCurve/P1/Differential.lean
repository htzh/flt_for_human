/-
Differential — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.EnginePrelude

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable {K : Type*} [Field K]

/-- Pin row #156. -/
scoped instance instHasPrincipalDivisors : HasPrincipalDivisors K (RatFunc K) where
  exists_divisor _ hf := ⟨principalDivisor hf, fun _ => rfl, degree_principalDivisor hf⟩

end RationalFunctionField

section RationalFunctionFieldDifferential

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

omit [DecidableEq (RatFunc K)] in
/-- Pin row #157. -/
theorem D_ratFuncX_eq_neg_X_sq_smul_D_inv :
    KaehlerDifferential.D K (RatFunc K) RatFunc.X
      = (-(RatFunc.X : RatFunc K) ^ 2) •
          KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ :=
  (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
    (mul_inv_cancel₀ RatFunc.X_ne_zero)

/-- Pin row #158. -/
theorem ord_placeInfty_X_inv : (p1PlaceInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(p1PlaceInfty K).ord_inv, ord_placeInfty_X, neg_neg]

/-- Pin row #159. -/
theorem ord_placeInfty_X_pow (n : ℕ) :
    (p1PlaceInfty K).ord ((RatFunc.X : RatFunc K) ^ n) = -(n : ℤ) := by
  rw [show ((RatFunc.X : RatFunc K) ^ n) = (RatFunc.X : RatFunc K) ^ (n : ℤ) from
    (zpow_natCast _ n).symm, (p1PlaceInfty K).ord_zpow, ord_placeInfty_X]
  ring

end RationalFunctionFieldDifferential

section RationalFunctionFieldNonVanishing

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- Pin row #160. -/
theorem D_ratFuncX_inv_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := by
  obtain ⟨u, -, hueq⟩ :=
    hwd (p1PlaceInfty K) (RatFunc.X : RatFunc K)⁻¹ (p1PlaceInfty K).uniformizer
      (ord_placeInfty_X_inv K) (p1PlaceInfty K).ord_uniformizer
  intro h0
  refine (p1PlaceInfty K).dCoord_ne_zero ?_
  show KaehlerDifferential.D K (RatFunc K) (p1PlaceInfty K).uniformizer = 0
  rw [hueq, h0, smul_zero]

/-- Pin row #161. -/
theorem differentialCoeff_placeInfty_D_X_eq :
    (p1PlaceInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = (-(RatFunc.X : RatFunc K) ^ 2) *
          (p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv, (p1PlaceInfty K).differentialCoeff_smul]

/-- Pin row #162. -/
theorem ord_differentialCoeff_placeInfty_D_X_inv_eq_zero
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (p1PlaceInfty K).ord
        ((p1PlaceInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)) = 0 := by
  obtain ⟨u, hu0, hueq⟩ :=
    hwd (p1PlaceInfty K) (p1PlaceInfty K).uniformizer (RatFunc.X : RatFunc K)⁻¹
      (p1PlaceInfty K).ord_uniformizer (ord_placeInfty_X_inv K)
  rw [(p1PlaceInfty K).differentialCoeff_unique
    (show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹
        = u • (p1PlaceInfty K).dCoord from hueq), hu0]

/-- Pin row #163. -/
theorem ordDifferential_placeInfty_D_ratFuncX
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (p1PlaceInfty K).ordDifferential
        (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)) = -2 := by
  rw [Place.ordDifferential, differentialCoeff_placeInfty_D_X_eq K, neg_mul,
    (p1PlaceInfty K).ord_neg,
    (p1PlaceInfty K).ord_mul (pow_ne_zero 2 RatFunc.X_ne_zero)
      ((p1PlaceInfty K).differentialCoeff_ne_zero (D_ratFuncX_inv_ne_zero K hwd)),
    ord_placeInfty_X_pow K 2, ord_differentialCoeff_placeInfty_D_X_inv_eq_zero K hwd]
  norm_num

end RationalFunctionFieldNonVanishing

namespace Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

/-- Pin row #164. -/
theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness

end Place

end AlgebraicCurve

end

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve

namespace Place

section ResidueEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem isSeparable_residueField_of_charZero_of_finiteResidue
    [CharZero K] [v.FiniteResidue] :
    Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) := by
  haveI : Module.Finite K (IsLocalRing.ResidueField v.toValuationSubring) := Place.FiniteResidue.finite
  haveI : Algebra.IsAlgebraic K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Algebra.IsAlgebraic.of_finite K _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

private theorem subsingleton_polynomialKaehler_of_charZero_of_finite
    [CharZero K] [v.FiniteResidue]
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]] :
    letI := v.polynomialAlgebra
    Subsingleton Ω[v.toValuationSubring⁄K[X]] := by
  haveI := v.isSeparable_residueField_of_charZero_of_finiteResidue
  exact v.subsingleton_polynomialKaehler_of_isSeparable_of_finite

end ResidueEngine

end Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringPolynomialFormallyUnramified K F := by
  intro v
  haveI := hfin v
  exact v.subsingleton_polynomialKaehler_of_charZero_of_finite

theorem valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringKaehlerSpanTop K F :=
  valSubringKaehlerSpanTop_of_polynomialFormallyUnramified
    (valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_charZero hfin)

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve

namespace MilneAvAg9bRd15UnitNormalFormLaurentSeed

private theorem ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {g : F} (hg : g ∈ v.toValuationSubring)
    (h0 : IsLocalRing.residue _ (⟨g, hg⟩ : v.toValuationSubring) = 0) :
    g = 0 ∨ 1 ≤ v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Or.inl rfl
  right
  have hnn : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne (v.ord g) 0 with hz | hnz
  · exfalso
    have hmemi : g⁻¹ ∈ v.toValuationSubring := by
      refine v.mem_of_ord_nonneg (inv_ne_zero hg0) ?_
      rw [v.ord_inv, hz, _root_.neg_zero]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hmemi⟩, Subtype.ext (mul_inv_cancel₀ hg0),
      Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩
  · omega

private theorem ag9b15u_exists_unit_normal_form_of_surj
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {w : F} (hw0 : w ≠ 0) (hw : v.ord w = 0) :
    ∃ (c : K) (s : F), c ≠ 0 ∧ (s = 0 ∨ 1 ≤ v.ord s) ∧
      w = algebraMap K F c * (1 + s) := by
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hw.ge
  have hwinv : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hw, _root_.neg_zero]
  have hres0 : IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring) ≠ 0 := by
    intro h0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 ⟨⟨⟨w, hwmem⟩, ⟨w⁻¹, hwinv⟩, Subtype.ext (mul_inv_cancel₀ hw0),
      Subtype.ext (inv_mul_cancel₀ hw0)⟩, rfl⟩
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hc
    exact hres0 hc.symm
  have ha0 : algebraMap K F c ≠ 0 :=
    fun h => hc0 ((algebraMap K F).injective (h.trans (_root_.map_zero _).symm))
  refine ⟨c, w * (algebraMap K F c)⁻¹ - 1, hc0, ?_, ?_⟩
  · have hainv : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]
      exact v.algebraMap_mem' c⁻¹
    have hsmem : w * (algebraMap K F c)⁻¹ - 1 ∈ v.toValuationSubring :=
      sub_mem (mul_mem hwmem hainv) (one_mem _)
    refine ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero v hsmem ?_
    have hfact : (⟨w * (algebraMap K F c)⁻¹ - 1, hsmem⟩ : v.toValuationSubring)
        = ⟨w, hwmem⟩ * ⟨(algebraMap K F c)⁻¹, hainv⟩ - 1 :=
      Subtype.ext (by push_cast; ring)
    have hainv_res : IsLocalRing.residue _
        ((⟨(algebraMap K F c)⁻¹, hainv⟩ : v.toValuationSubring))
        = (IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring))⁻¹ := by
      have h1 : (⟨(algebraMap K F c)⁻¹, hainv⟩ : v.toValuationSubring)
          = algebraMap K v.toValuationSubring c⁻¹ :=
        Subtype.ext (by rw [v.coe_algebraMap, map_inv₀])
      rw [h1, ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        map_inv₀, hc, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hfact, map_sub, map_mul, map_one, hainv_res, mul_inv_cancel₀ hres0, sub_self]
  · have hrw : (1 : F) + (w * (algebraMap K F c)⁻¹ - 1) = w * (algebraMap K F c)⁻¹ := by
      ring
    rw [hrw, mul_comm w (algebraMap K F c)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ ha0, one_mul]

private theorem ag9b15u_exists_K_truncation_of_mem_poleSubmodule
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (n : ℕ) {f : F} (hf : f ∈ v.poleSubmodule n) :
    ∃ c : ℕ → K,
      f - ∑ j ∈ Finset.range n, algebraMap K F (c j) * (v.uniformizer ^ (j + 1))⁻¹
        ∈ v.toValuationSubring := by
  induction n generalizing f with
  | zero =>
    refine ⟨0, ?_⟩
    rw [Finset.range_zero, Finset.sum_empty, sub_zero]
    rwa [← SetLike.mem_coe, v.coe_poleSubmodule_zero] at hf
  | succ n ih =>
    obtain ⟨ctop, hctop⟩ := hsurj (v.laurentTailCoeff (n + 1) ⟨f, hf⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring ctop)
        = v.laurentTailCoeff (n + 1) ⟨f, hf⟩ := by
      rw [← hctop, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : f - algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹
        ∈ v.poleSubmodule n := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hf hclift
      rwa [v.coe_algebraMap] at h
    obtain ⟨c', hc'⟩ := ih hrem
    refine ⟨fun j => if j = n then ctop else c' j, ?_⟩
    have hstep : ∑ j ∈ Finset.range (n + 1),
        algebraMap K F (if j = n then ctop else c' j) * (v.uniformizer ^ (j + 1))⁻¹
        = (∑ j ∈ Finset.range n, algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹)
          + algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹ := by
      rw [Finset.sum_range_succ, ite_eq_left rfl]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ite_eq_right (Finset.mem_range.mp hj).ne]
    rw [hstep, show f - ((∑ j ∈ Finset.range n,
          algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹)
          + algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹)
        = f - algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹
          - ∑ j ∈ Finset.range n,
              algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹ from by ring]
    exact hc'

private theorem ag9b15u_differentialCoeff_D_unit_mul_uniformizer
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (w : F) :
    v.differentialCoeff (KaehlerDifferential.D K F (w * v.uniformizer))
      = w + v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) := by
  refine v.differentialCoeff_unique ?_
  calc KaehlerDifferential.D K F (w * v.uniformizer)
      = w • KaehlerDifferential.D K F v.uniformizer
        + v.uniformizer • KaehlerDifferential.D K F w := by
        rw [Derivation.leibniz]
    _ = w • v.dCoord + v.uniformizer •
          (v.differentialCoeff (KaehlerDifferential.D K F w) • v.dCoord) := by
        rw [show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
          v.differentialCoeff_smul_dCoord]
    _ = (w + v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w))
          • v.dCoord := by
        rw [smul_smul, add_smul]

end MilneAvAg9bRd15UnitNormalFormLaurentSeed

end ModularCurve

end
