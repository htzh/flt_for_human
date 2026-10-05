/-
The explicit-Vélu map equation in odd order: the H3 capstone of the Vélu port.

This module contains the two headline theorems

* `WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed`
  (the general, characteristic-agnostic statement), and
* `WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet`
  (the plain statement, derived as a corollary),

together with the map-column-only engine that their proofs consume and that
`Velu/OddOrder.lean` does not yet provide.

Statements are transcribed from the pinned FLT `aa2d8b3` `Theorems/` wrappers
(the statement authority):

* `Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
* `Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean`

and proof bodies from the canonical pin solution file

* `P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`

only adapted to mathlib `v4.34.0`. The plain headline is a genuine corollary of
the general one (it simply ignores its `(h2 : (2 : L) ≠ 0)` hypothesis); its
proof body is not transcribed.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.OddOrder
import FLTForHuman.WeierstrassCurve.FunctionFieldFinite
import FLTForHuman.AlgebraicCurve.P1.DXCoeff
import FLTForHuman.AlgebraicCurve.P1.UnitFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- The pin's `haveI` instance walls and its unused `h2` binder in the plain
-- headline are transcribed literally.
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

/-! ### The dictionary-flavoured block

`wqDiscPoly`, the separability of `weierstrassQuadratic`, the splitting-field /
`P¹`-degree lemmas and the Galois/`HasPrincipalDivisors` bridge are *dictionary*
material, not Vélu. SET-1's `WeierstrassCurve/Place/Dictionary.lean` (via
`WeierstrassCurve/FunctionFieldQuadratic.lean`) is already the home of the
`weierstrassQuadratic` vocabulary, but it is frozen, so — per the work order's
design note — this block lives in this module in one delimited section rather
than editing `Place/Dictionary.lean`.

`adjoin_yCoord_eq_top`/`finiteDimensional_ratFunc_functionField`
(`WeierstrassCurve/FunctionFieldFinite.lean`) and
`hasPrincipalDivisors_of_isGalois`/`ramificationInertiaIdentity_of_finiteDimensional`
(`AlgebraicCurve/P1/{DXCoeff,UnitFinite}.lean`) are imported, not redeclared.
-/

namespace Polynomial

variable {K : Type*} [Field K]

/-- Pin `Polynomial.separable_X_sq_add_C_mul_X_sub_C` (map `S_` line 7620). -/
theorem separable_X_sq_add_C_mul_X_sub_C {b c : K}
    (h : b ^ 2 + 4 * c ≠ 0) :
    (X ^ 2 + (C b * X - C c) : K[X]).Separable := by
  rw [Polynomial.separable_def']
  refine ⟨C (-(4 * (b ^ 2 + 4 * c)⁻¹)),
    C ((b ^ 2 + 4 * c)⁻¹) * (C 2 * X + C b), ?_⟩
  have hd : derivative (X ^ 2 + (C b * X - C c) : K[X]) = C 2 * X + C b := by
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow,
      derivative_C, derivative_X, mul_one, zero_mul, sub_zero]
    ring_nf
  rw [hd]
  have hkey : C (-(4 * (b ^ 2 + 4 * c)⁻¹)) * (X ^ 2 + (C b * X - C c))
        + C ((b ^ 2 + 4 * c)⁻¹) * (C 2 * X + C b) * (C 2 * X + C b)
      = C ((b ^ 2 + 4 * c)⁻¹ * (b ^ 2 + 4 * c)) := by
    simp only [_root_.map_neg, map_mul, map_add, map_pow, map_ofNat]
    ring
  rw [hkey, inv_mul_cancel₀ h, map_one]

end Polynomial

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] (W : Affine F)

/-- Pin `WeierstrassCurve.Affine.weierstrassQuadratic_natDegree_le` (map `S_` line 5783). -/
theorem weierstrassQuadratic_natDegree_le :
    (weierstrassQuadratic W).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_degree_le]
  refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
  · exact (Polynomial.degree_X_pow 2).le
  · exact le_of_lt weierstrassQuadratic_sub_degree_lt

/-- Pin `WeierstrassCurve.Affine.splits_weierstrassQuadratic_map` (map `S_` line 5850). -/
theorem splits_weierstrassQuadratic_map :
    ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).Splits := by
  have hroot : ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).IsRoot (yCoord W) := by
    show ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).eval (yCoord W) = 0
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact aeval_yCoord_weierstrassQuadratic
  have hkey : (X - C (yCoord W))
        * (((weierstrassQuadratic W).map (algebraMap (RatFunc F) W.FunctionField))
          /ₘ (X - C (yCoord W)))
      = (weierstrassQuadratic W).map (algebraMap (RatFunc F) W.FunctionField) :=
    mul_divByMonic_eq_iff_isRoot.mpr hroot
  rw [← hkey, splits_X_sub_C_mul_iff]
  refine Polynomial.Splits.of_natDegree_le_one ?_
  rw [natDegree_divByMonic _ (monic_X_sub_C (yCoord W))]
  have h1 : ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).natDegree ≤ 2 :=
    le_trans Polynomial.natDegree_map_le (weierstrassQuadratic_natDegree_le W)
  have h2 : (X - C (yCoord W)).natDegree = 1 := Polynomial.natDegree_X_sub_C _
  omega

/-- Pin `WeierstrassCurve.Affine.isSplittingField_weierstrassQuadratic` (map `S_` line 5873). -/
theorem isSplittingField_weierstrassQuadratic :
    Polynomial.IsSplittingField (RatFunc F) W.FunctionField (weierstrassQuadratic W) := by
  constructor
  · exact splits_weierstrassQuadratic_map W
  ·
    rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← adjoin_yCoord_eq_top (W := W),
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        isIntegral_yCoord.isAlgebraic]
    refine Algebra.adjoin_mono ?_
    rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
    exact ⟨weierstrassQuadratic_monic.ne_zero, aeval_yCoord_weierstrassQuadratic⟩

variable (W : Affine F)

/-- Pin `WeierstrassCurve.Affine.wqDiscPoly` (map `S_` line 7648). -/
def wqDiscPoly : F[X] :=
  (C W.a₁ * X + C W.a₃) ^ 2 + C 4 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

variable {W}

/-- Pin `WeierstrassCurve.Affine.weierstrassQuadratic_separable` (map `S_` line 7653). -/
theorem weierstrassQuadratic_separable (h : wqDiscPoly W ≠ 0) :
    (weierstrassQuadratic W).Separable := by
  have hinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    IsFractionRing.injective F[X] (RatFunc F)
  have hC4 : (4 : RatFunc F) = algebraMap F[X] (RatFunc F) (C 4) := by
    rw [map_ofNat, map_ofNat]
  have h2 : (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) ^ 2
        + 4 * (algebraMap F[X] (RatFunc F) (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))
      ≠ 0 := by
    rw [hC4, ← map_mul, ← map_pow, ← map_add]
    exact fun hcon => h (hinj (hcon.trans (_root_.map_zero _).symm))
  rw [show weierstrassQuadratic W
      = X ^ 2 + (C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) * X
        - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))) from
    rfl]
  exact separable_X_sq_add_C_mul_X_sub_C h2

/-- Pin `WeierstrassCurve.Affine.isGalois_functionField_of_wqDiscPoly_ne_zero`
(map `S_` line 7670). -/
theorem isGalois_functionField_of_wqDiscPoly_ne_zero (h : wqDiscPoly W ≠ 0) :
    IsGalois (RatFunc F) W.FunctionField :=
  haveI : (weierstrassQuadratic W).IsSplittingField (RatFunc F) W.FunctionField :=
    isSplittingField_weierstrassQuadratic W
  IsGalois.of_separable_splitting_field (weierstrassQuadratic_separable h)

/-- Pin `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_wqDiscPoly_ne_zero`
(map `S_` line 7676). -/
theorem hasPrincipalDivisors_functionField_of_wqDiscPoly_ne_zero (h : wqDiscPoly W ≠ 0) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  haveI : IsGalois (RatFunc F) W.FunctionField := isGalois_functionField_of_wqDiscPoly_ne_zero h
  haveI : FiniteDimensional (RatFunc F) W.FunctionField :=
    finiteDimensional_ratFunc_functionField W
  AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors_of_isGalois
    (AlgebraicCurve.ramificationInertiaIdentity_of_finiteDimensional F (RatFunc F) W.FunctionField)

/-- Pin `WeierstrassCurve.Affine.natDegree_wqLinear_sq_le` (map `S_` line 7681, pin-private). -/
private theorem natDegree_wqLinear_sq_le :
    ((C W.a₁ * X + C W.a₃ : F[X]) ^ 2).natDegree ≤ 2 := by
  refine le_trans natDegree_pow_le ?_
  have : (C W.a₁ * X + C W.a₃ : F[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) ?_
    simp only [natDegree_C, max_le_iff]
    exact ⟨le_trans (natDegree_C_mul_le _ _) (by simp), by omega⟩
  omega

/-- Pin `WeierstrassCurve.Affine.natDegree_wqCubic` (map `S_` line 7690, pin-private). -/
private theorem natDegree_wqCubic :
    (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).natDegree = 3 := by
  rw [show (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X])
      = C 1 * X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ from by rw [map_one, one_mul]]
  exact natDegree_cubic one_ne_zero

/-- Pin `WeierstrassCurve.Affine.wqDiscPoly_ne_zero` (map `S_` line 7696). -/
theorem wqDiscPoly_ne_zero (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    wqDiscPoly W ≠ 0 := by
  by_cases h2 : (2 : F) = 0
  ·
    have hC4 : (C (4 : F) : F[X]) = 0 := by
      rw [show (4 : F) = 2 * 2 from by norm_num, h2, mul_zero, _root_.map_zero]
    have heq : wqDiscPoly W = (C W.a₁ * X + C W.a₃) ^ 2 := by
      simp only [wqDiscPoly, hC4, zero_mul, add_zero]
    rw [heq]
    refine pow_ne_zero 2 ?_
    have ha : W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := h.resolve_left (· h2)
    intro hcon
    rcases ha with ha | ha
    · have h1 := congrArg (·.coeff 1) hcon
      simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C,
        if_neg one_ne_zero, add_zero, coeff_zero] at h1
      exact ha h1
    · have h0 := congrArg (·.coeff 0) hcon
      simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add,
        coeff_C_zero, coeff_zero] at h0
      exact ha h0
  ·
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 from by norm_num]; exact mul_ne_zero h2 h2
    intro hcon
    have hdeg : (wqDiscPoly W).natDegree = 3 := by
      rw [show wqDiscPoly W = C (4 : F) * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
            + (C W.a₁ * X + C W.a₃) ^ 2 from by simp only [wqDiscPoly]; ring,
        natDegree_add_eq_left_of_natDegree_lt
          (by rw [natDegree_C_mul h4, natDegree_wqCubic];
              exact lt_of_le_of_lt natDegree_wqLinear_sq_le (by omega)),
        natDegree_C_mul h4, natDegree_wqCubic]
    rw [hcon, natDegree_zero] at hdeg
    omega

end WeierstrassCurve.Affine

/-! ### The Galois action on places and valuation subrings

The direct `F ≃ₐ[K] F` pointwise action on `ValuationSubring F` and its induced
action on residue fields. The port already has the same action routed through
`AlgebraicCurve.SemilinearAut.ofAlgAut` (`SemilinearAut.smulValuationSubringEquiv`,
`SemilinearAut.smulResidueRingEquiv`, `AlgebraicCurve.Place.ord_smul`,
`AlgebraicCurve.Place.deg_smul`); the direct-`AlgEquiv` forms below are the pin's
statement copies and are placed here, with the rest of the dictionary material,
rather than edited into the frozen `Place` modules. -/

namespace AlgebraicCurve.Place

open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (σ : F ≃ₐ[K] F)

/-- Pin `AlgebraicCurve.Place.smulRingEquiv` (map `S_` line 358). -/
def smulRingEquiv (A : ValuationSubring F) : A ≃+* (σ • A : ValuationSubring F) where
  toFun x := ⟨σ x, by
    simpa [AlgEquiv.smul_def] using
      ValuationSubring.smul_mem_pointwise_smul σ (x : F) A x.2⟩
  invFun y := ⟨σ.symm y, by
    have := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := σ)
      (S := A) (x := (y : F))).mp y.2
    simpa [AlgEquiv.smul_def, AlgEquiv.aut_inv] using this⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

/-- Pin `AlgebraicCurve.Place.coe_smulRingEquiv_apply` (map `S_` line 374). -/
theorem coe_smulRingEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulRingEquiv σ A x : (σ • A : ValuationSubring F)) : F) = σ x := rfl

private theorem _root_.ValuationSubring.pointwise_smul_top :
    σ • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

variable (v : Place K F)

/-- Pin `AlgebraicCurve.Place.smul_toValuationSubring` (map `S_` line 400). -/
theorem smul_toValuationSubring : (σ • v).toValuationSubring = σ • v.toValuationSubring := rfl

/-- Pin `AlgebraicCurve.Place.smulResidueAlgEquiv` (map `S_` line 432). -/
def smulResidueAlgEquiv : v.ResidueField ≃ₐ[K] (σ • v).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv
      ((smul_toValuationSubring σ v).symm ▸ smulRingEquiv σ v.toValuationSubring)) <| fun a => by
    have h3 : (smulRingEquiv σ v.toValuationSubring) (algebraMap K v.toValuationSubring a)
        = algebraMap K (σ • v).toValuationSubring a := by
      ext
      rw [coe_smulRingEquiv_apply, coe_algebraMap, σ.commutes]
      rfl
    show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3

end AlgebraicCurve.Place

/-! ### The map-column engine: the odd-order carrier and its discharge

`VeluThmOneOddAt` is the proposition the map `S_` file discharges at the odd
order `p = 2 * n + 1`; the three `kw_no6_hroute_*` theorems are its proof. They
consume only `Velu/OddOrder.lean` plus the `HasPrincipalDivisors` supplier
`kw_veluHPDSupplier` built from the dictionary block above. -/

namespace WeierstrassCurve

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

section Carrier

variable {F : Type*} [Field F] [DecidableEq F]

/-- Pin `WeierstrassCurve.VeluThmOneOddAt` (map `S_` line 3154). -/
def VeluThmOneOddAt (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) : Prop :=
  ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
    (∀ P ∈ W.oddOrderSummingSet Q n, r ≠ P.1) →
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) r)
      (W.veluY (W.oddOrderSummingSet Q n) r s)

end Carrier

section HPD

variable {F : Type*} [Field F]

private theorem two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero
    (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h2, h1, h3⟩ := h
  apply hΔ
  have hb2 : W.b₂ = 0 := by
    rw [WeierstrassCurve.b₂, h1]; linear_combination (2 * W.a₂) * h2
  have hb4 : W.b₄ = 0 := by
    rw [WeierstrassCurve.b₄, h1]; linear_combination W.a₄ * h2
  have hb6 : W.b₆ = 0 := by
    rw [WeierstrassCurve.b₆, h3]; linear_combination (2 * W.a₆) * h2
  rw [WeierstrassCurve.Δ, hb2, hb4, hb6]; ring

/-- Pin `WeierstrassCurve.kw_veluHPDSupplier` (map `S_` line 8507). -/
theorem kw_veluHPDSupplier :
    ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      AlgebraicCurve.HasPrincipalDivisors F W.toAffine.FunctionField :=
  fun W hΔ => WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_wqDiscPoly_ne_zero
    (WeierstrassCurve.Affine.wqDiscPoly_ne_zero
      (two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero W hΔ))

end HPD

section CharAgnosticOdd

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

variable (F) in

/-- Pin `WeierstrassCurve.kw_no6_hroute_veluDeficitIsConstantAt_odd`
(map `S_` line 11935). -/
theorem kw_no6_hroute_veluDeficitIsConstantAt_odd
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_dedekind
    kw_veluHPDSupplier kw_hDDTerm
    (kw_veluDeficitFunOrdNonnegAt_odd F kw_hDDTerm hp3 hpodd)

variable (F) in

/-- Pin `WeierstrassCurve.kw_no6_hroute_veluDeficitConstancyAt_odd`
(map `S_` line 11944). -/
theorem kw_no6_hroute_veluDeficitConstancyAt_odd
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitConstancyAt F p := by
  haveI : Infinite F := kw_infinite_of_isAlgClosed
  refine veluDeficitConstancyAt_of_isConstant_of_constantZero F
    (kw_no6_hroute_veluDeficitIsConstantAt_odd F hp3 hpodd)
    (kw_veluDeficitConstantIsZeroAt_odd hp3 hpodd ?_)
  exact kw_veluDeficitCrossQuadProdDegLtAt_odd hp3 hpodd
    (kw_veluDeficitCrossQuadCubeBetaDegLtAt_odd hp3 hpodd
      (kw_veluDeficitCrossQuadBetaOnlyDegLtAt_odd
        (veluDeficitCrossQuadBetaSDecompDegLtAt_of_betaSq_of_alphaBeta
          (kw_veluDeficitCrossQuadBetaSqDecompDegLtAt_odd hp3 hpodd)
          (kw_veluDeficitCrossQuadAlphaBetaDecompDegLtAt_odd hp3 hpodd))))

variable {W : WeierstrassCurve F} {Q : W.toAffine.Point} {p : ℕ}

/-- Pin `WeierstrassCurve.kw_no6_hroute_veluThmOneOddAt_odd`
(map `S_` line 11960). -/
theorem kw_no6_hroute_veluThmOneOddAt_odd
    (hΔ : W.Δ ≠ 0) (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p) :
    VeluThmOneOddAt W Q ((p - 1) / 2) := by
  have hQ0 : Q ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hord; omega
  obtain ⟨x₀, y₀, h₀, rfl, -⟩ := exists_some_of_ne_zero hQ0
  intro r s hrs hav
  exact (W.veluQuotient_equation_iff_veluDeficit_eq_zero _ r s).mpr
    (kw_no6_hroute_veluDeficitConstancyAt_odd F hp3 hpodd
      W hΔ x₀ y₀ h₀ hord hrs hav)

end CharAgnosticOdd

/-! ### The two headlines

Statements are the pin `Theorems/` wrappers' verbatim. The plain statement is the
general one with an extra `(h2 : (2 : L) ≠ 0)`; its proof is the general theorem
applied directly — the hypothesis is simply unused. -/

/-- The general map equation, characteristic-agnostic. -/
theorem velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : W.oddOrderSummingSet Q 0 = ∅ := by simp [WeierstrassCurve.oddOrderSummingSet]
    rw [h0, WeierstrassCurve.veluQuotient_empty, WeierstrassCurve.veluX_empty,
      WeierstrassCurve.veluY_empty]
    exact hxy
  · have hp3 : 3 ≤ 2 * n + 1 := by omega
    have hpodd : Odd (2 * n + 1) := ⟨n, rfl⟩
    have hn_eq : ((2 * n + 1) - 1) / 2 = n := by omega
    have key := WeierstrassCurve.kw_no6_hroute_veluThmOneOddAt_odd
      (W := W) (Q := Q) W.Δ'.ne_zero hp3 hpodd hQ
    rw [hn_eq] at key
    exact key hxy hx

/-- The plain map equation: the general statement with `(2 : L) ≠ 0` assumed.
Proved as a corollary of the general theorem (no transcribed proof body). -/
theorem velu_map_equation_of_oddOrderSummingSet
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) :=
  velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed W n Q hQ hxy hx

end WeierstrassCurve

end
