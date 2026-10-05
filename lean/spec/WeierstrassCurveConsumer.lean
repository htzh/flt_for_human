/-
  Cross-module wire test for the Weierstrass principal-divisor capstone and the
  Vélu port (H0 bridge + SET-1 dictionary and vocabulary).

  A `spec/` probe, not a library module. Four executed zones: the function-field
  prerequisites (`adjoin_yCoord_eq_top`, `finiteDimensional_ratFunc_functionField`),
  the headline `hasPrincipalDivisors_functionField`, applied both at a variable
  curve over `ℚ` (discharging `[CharZero ℚ]`) and at a concrete curve, the H0
  bridge (`yGen`, `polyToFunctionField_eq_aeval`,
  `equation_map_polyToFunctionField_yGen`, `transcendental_polyToFunctionField_X`),
  composed with the generation theorem, and the SET-1 place dictionary plus Vélu
  vocabulary (`veluGx`/`veluGy`/`veluQuotient`/`oddOrderSummingSet`, `IsFinitePlace`,
  `isDedekindDomain_of_Δ_ne_zero`, `placeOfEquation`) at concrete curves.
-/
import FLTForHuman.WeierstrassCurve.PrincipalDivisors
import FLTForHuman.WeierstrassCurve.Velu.Formula
import FLTForHuman.WeierstrassCurve.Velu.Engine
import FLTForHuman.WeierstrassCurve.Velu.Discharge
import FLTForHuman.WeierstrassCurve.Velu.OddOrder
import FLTForHuman.WeierstrassCurve.Velu.MapEquation
import FLTForHuman.WeierstrassCurve.Velu.RestrictAlong
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGate
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import FLTForHuman.WeierstrassCurve.Isogeny.NatCard
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve.Affine

namespace WeierstrassCurveConsumer

-- Zone 1: the function-field prerequisites. `yCoord` generates the function
-- field over `RatFunc F`, and it is a finite extension.
#check @WeierstrassCurve.Affine.adjoin_yCoord_eq_top
#check @WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField

example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    IntermediateField.adjoin (RatFunc F) {WeierstrassCurve.Affine.yCoord W} = ⊤ :=
  WeierstrassCurve.Affine.adjoin_yCoord_eq_top

example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    FiniteDimensional (RatFunc F) W.FunctionField :=
  WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField W

-- Zone 2: the headline, at a variable curve over `ℚ` ...
#check @WeierstrassCurve.Affine.hasPrincipalDivisors_functionField

example (W : WeierstrassCurve.Affine ℚ) :
    AlgebraicCurve.HasPrincipalDivisors ℚ W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField W

-- ... and at a concrete curve `y² = x³ + 1`.
example : AlgebraicCurve.HasPrincipalDivisors ℚ
    (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _

-- Zone 3: the Vélu port's H0 generic-point bridge. `polyToFunctionField` is the
-- `aeval` of `X`, `X` is transcendental, the generic point lies on the
-- base-changed curve, and the pin's `yGen` is our `yCoord`.
example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) (p : F[X]) :
    polyToFunctionField W p = Polynomial.aeval (polyToFunctionField W X) p :=
  polyToFunctionField_eq_aeval p

example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    Transcendental F (polyToFunctionField W X) :=
  transcendental_polyToFunctionField_X

example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (polyToFunctionField W X) (yGen W) :=
  equation_map_polyToFunctionField_yGen

-- The bridge composes with the generation theorem across modules: the pin's
-- generic point `yGen` generates `W.FunctionField` over `RatFunc F`.
example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    IntermediateField.adjoin (RatFunc F) {yGen W} = ⊤ := by
  rw [show yGen W = yCoord W from rfl]
  exact adjoin_yCoord_eq_top

-- Zone 4 (SET-1): the Weierstrass place dictionary and the Vélu vocabulary at a
-- concrete curve `y² = x³ + 1` (`a₁ = a₂ = a₃ = a₄ = 0`, `a₆ = 1`).
example : (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).veluGx 1 2 = 3 := by
  norm_num [WeierstrassCurve.veluGx]

example : (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).veluGy 1 2 = -4 := by
  norm_num [WeierstrassCurve.veluGy]

example : (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).veluQuotient ∅
    = WeierstrassCurve.mk (0 : ℚ) 0 0 0 1 :=
  WeierstrassCurve.veluQuotient_empty _

example : (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).oddOrderSummingSet
    (0 : (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.Point) 0 = ∅ := by
  simp [WeierstrassCurve.oddOrderSummingSet]

-- `IsFinitePlace` unfolds to the coordinate-ring integrality predicate.
example (v : AlgebraicCurve.Place ℚ
    (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.FunctionField) :
    WeierstrassCurve.Affine.IsFinitePlace v ↔
      ∀ r : (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.CoordinateRing,
        algebraMap (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.CoordinateRing
          (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.FunctionField r
          ∈ v.toValuationSubring :=
  Iff.rfl

-- The dictionary's Dedekind input at the concrete curve; `Δ = -432 ≠ 0`.
example : IsDedekindDomain
    (WeierstrassCurve.mk (0 : AlgebraicClosure ℚ) 0 0 0 1).toAffine.CoordinateRing := by
  refine WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero ?_
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

-- A point on `y² = x³ + 1` over `AlgebraicClosure ℚ`.
example : ∃ y : AlgebraicClosure ℚ,
    (WeierstrassCurve.mk (0 : AlgebraicClosure ℚ) 0 0 0 1).toAffine.Equation 0 y :=
  WeierstrassCurve.Affine.exists_equation _ 0

-- `placeOfEquation` produces a finite place (with the Dedekind instance supplied
-- by the caller, as `placeOfEquation` itself takes it as a section variable).
example (W : WeierstrassCurve.Affine (AlgebraicClosure ℚ)) [IsDedekindDomain W.CoordinateRing]
    {x y : AlgebraicClosure ℚ} (h : W.Equation x y) :
    WeierstrassCurve.Affine.IsFinitePlace (WeierstrassCurve.Affine.placeOfEquation h) :=
  WeierstrassCurve.Affine.isFinitePlace_placeOfEquation h

-- Zone 5 (SET-2): the cleared-polynomial degree engine (E) and the generic point /
-- translation layer (F). `adjoin_addFun_eq_top` says the translated generic point
-- generates the function field; the degree bounds are the engine's workhorses.
example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) (hΔ : W.Δ ≠ 0) {a b : F}
    (hA : W.Equation a b) :
    IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) = ⊤ :=
  WeierstrassCurve.Affine.adjoin_addFun_eq_top hΔ hA

example (F : Type*) [Field F] [DecidableEq F] (W : WeierstrassCurve F) {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitSingletonSumClearedPoly S).natDegree < 4 * S.card :=
  W.veluDeficitSingletonSumClearedPoly_natDegree_lt hS

example (F : Type*) [Field F] [DecidableEq F] (W : WeierstrassCurve F) {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S).natDegree < 4 * S.card :=
  W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly_natDegree_lt hS

-- Zone 6 (SET-3): the deficit-fun `ord`/`evalAt` discharge (G) and the
-- odd-order summing-set combinatorics (H). The two
-- `evalAt_veluX/Y_liftSummingSet_placeOfEquation` statements are what the
-- capstone consumes; the carriers and the `_odd` family are applied below.
example (F : Type*) [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
    [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, r ≠ A.1) :
    (WeierstrassCurve.Affine.placeOfEquation hrs).evalAt
        ((W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
          (polyToFunctionField W X))
      = W.veluX S r :=
  WeierstrassCurve.Affine.evalAt_veluX_liftSummingSet_placeOfEquation hrs hS

example (F : Type*) [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
    [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, r ≠ A.1) :
    (WeierstrassCurve.Affine.placeOfEquation hrs).evalAt
        ((W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
          (polyToFunctionField W X) (yGen W))
      = W.veluY S r s :=
  WeierstrassCurve.Affine.evalAt_veluY_liftSummingSet_placeOfEquation hrs hS

example (F : Type*) [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
    [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, r ≠ A.1) :
    (WeierstrassCurve.Affine.placeOfEquation hrs).evalAt
        (W.veluDeficitFun S) = W.veluDeficit S r s :=
  WeierstrassCurve.Affine.evalAt_veluDeficitFun_placeOfEquation hrs hS

example (F : Type*) [Field F] [DecidableEq F] (p : ℕ) :
    WeierstrassCurve.VeluDeficitFunOrdNonnegOffKernelAt F p :=
  WeierstrassCurve.veluDeficitFunOrdNonnegOffKernelAt F p

example (F : Type*) [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    {Q : W.toAffine.Point} {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    (W.oddOrderSummingSet Q n).card = n :=
  WeierstrassCurve.kw_card_oddOrderSummingSet_odd hp3 hpodd hord hn

-- Zone 7 (H3): the explicit-Vélu map-equation headlines and the map-column
-- engine that supplies their `HasPrincipalDivisors` input. The general headline
-- is characteristic-agnostic; the plain headline is its corollary, applied here
-- through the same general theorem.
#check @WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed
#check @WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
#check @WeierstrassCurve.VeluThmOneOddAt
#check @WeierstrassCurve.kw_no6_hroute_veluThmOneOddAt_odd
#check @WeierstrassCurve.kw_veluHPDSupplier
#check @WeierstrassCurve.Affine.wqDiscPoly
#check @WeierstrassCurve.Affine.wqDiscPoly_ne_zero
#check @WeierstrassCurve.Affine.isSplittingField_weierstrassQuadratic
#check @WeierstrassCurve.Affine.weierstrassQuadratic_separable
#check @AlgebraicCurve.Place.smulRingEquiv
#check @AlgebraicCurve.Place.smulResidueAlgEquiv

-- The general statement, restated at the consumer's binders.
example {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) :=
  WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed W n Q hQ hxy hx

-- The plain statement is the general one with `(2 : L) ≠ 0` supplied; the extra
-- hypothesis is unused, so the corollary goes through the general theorem.
example {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) :=
  WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
    h2 W n Q hQ hxy hx

-- The engine's dictionary route at a concrete curve `y² = x³ + 1`: `wqDiscPoly`
-- is nonzero, so the function field is Galois/principal-divisor, and the
-- `VeluThmOneOddAt` carrier is available across the module boundary.
example : WeierstrassCurve.Affine.wqDiscPoly
    (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine ≠ 0 :=
  WeierstrassCurve.Affine.wqDiscPoly_ne_zero (Or.inl (by norm_num))

example : AlgebraicCurve.HasPrincipalDivisors ℚ
    (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.FunctionField :=
  WeierstrassCurve.kw_veluHPDSupplier _ (by
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

example {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve F}
    {Q : W.toAffine.Point} {p : ℕ} (hΔ : W.Δ ≠ 0) (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) :
    WeierstrassCurve.VeluThmOneOddAt W Q ((p - 1) / 2) :=
  WeierstrassCurve.kw_no6_hroute_veluThmOneOddAt_odd hΔ hp3 hpodd hord

-- The H4 `restrictAlong` engine (cluster I) is available across the module
-- boundary. The two headline theorems are blocked on unported upstream (see the
-- header of `Velu/RestrictAlong.lean`), so this zone exercises the engine
-- surface that *is* available: the generic Vélu functions, the cleared level
-- polynomial, the point map, the coordinate-ring/function-field homomorphisms
-- and the seam at the odd-order summing set.
#check @WeierstrassCurve.kwVeluXGenFun
#check @WeierstrassCurve.kwVeluYGenFun
#check @WeierstrassCurve.veluXDenomPoly
#check @WeierstrassCurve.veluXDenomPoly_monic
#check @WeierstrassCurve.natDegree_veluXDenomPoly
#check @WeierstrassCurve.veluXClearedPoly
#check @WeierstrassCurve.veluXClearedPoly_monic
#check @WeierstrassCurve.eval_veluXClearedPoly
#check @WeierstrassCurve.Affine.veluXFun
#check @WeierstrassCurve.Affine.veluYFun
#check @WeierstrassCurve.kw_velu_map_nonsingular
#check @WeierstrassCurve.kwVeluPointMap
#check @WeierstrassCurve.kwVeluPointMap_zero
#check @WeierstrassCurve.kwVeluPointMap_some_of_mem
#check @WeierstrassCurve.kwVeluPointMap_some_of_ne
#check @WeierstrassCurve.kw_aeval_kwVeluXGenFun_injective
#check @WeierstrassCurve.kw_kwVeluXGenFun_mul_denom_sq_eq_cleared
#check @WeierstrassCurve.kw_eval_veluXClearedPoly_ne_zero_of_mem
#check @WeierstrassCurve.kw_oddOrderSummingSetCoordHom_odd
#check @WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd
#check @WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd_finiteAlong
#check @WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd_isIntegral
#check @WeierstrassCurve.kw_restrictAlong_infinitePlace_oddOrderSummingSet_odd
#check @WeierstrassCurve.kw_restrictAlong_placeOfEquation_of_ne_oddOrderSummingSet_odd
#check @WeierstrassCurve.s2c_exists_fst_eq_of_mem_zmultiples
#check @WeierstrassCurve.s2c_mem_zmultiples_of_fst_eq
#check @WeierstrassCurve.zsmul_eq_emod_zsmul_of_nsmul_eq_zero

-- The engine's finiteness/integrality seam across the module boundary.
example {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve F}
    [W.toAffine.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    {Q : W.toAffine.Point} {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) :
    AlgebraicCurve.FiniteAlong F
      (WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd
        (W := W) hp3 hpodd hord) :=
  WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd_finiteAlong
    (W := W) hp3 hpodd hord

example {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve F}
    [W.toAffine.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    {Q : W.toAffine.Point} {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) :
    (WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd
      (W := W) hp3 hpodd hord).toRingHom.IsIntegral :=
  WeierstrassCurve.kw_oddOrderSummingSetFunctionFieldHom_odd_isIntegral
    (W := W) hp3 hpodd hord

-- Zone: the H5a weierstrass place gate and conditional-currency isogeny
-- dictionary (the vocabulary the H4 `restrictAlong` headline takes as binders).
#check @WeierstrassCurve.Affine.GenusOnePlaceGate
#check @WeierstrassCurve.Affine.pointEquivPlace
#check @WeierstrassCurve.Affine.placeOfPoint
#check @WeierstrassCurve.Affine.deg_placeOfPoint
#check @WeierstrassCurve.Affine.pointDivisor
#check @WeierstrassCurve.Affine.pointClass
#check @WeierstrassCurve.Affine.AbelTheorem
#check @WeierstrassCurve.Affine.genusOnePic0Equiv
#check @WeierstrassCurve.Affine.pointClass_add
#check @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
#check @WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum
#check @WeierstrassCurve.Affine.algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
#check @WeierstrassCurve.Affine.GenusOnePlaceGate.ext_of_isCentred
#check @AlgebraicCurve.Pic0.pushforwardAlongHom
#check @WeierstrassCurve.Affine.pointMapOfPushforward
#check @WeierstrassCurve.Affine.IsogenyEndDatum
#check @WeierstrassCurve.Affine.isogenyEndSubring
#check @WeierstrassCurve.Affine.IsogenyHomDatum

-- The seam: the point map attached to an integral function-field
-- homomorphism is the unique additive map making `restrictAlong` commute.
example {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V W : WeierstrassCurve.Affine F} [V.IsElliptic] [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V] [WeierstrassCurve.Affine.AbelTheorem V]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W] [WeierstrassCurve.Affine.AbelTheorem W]
    (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong F ι) (hN : AlgebraicCurve.NormFormulaAlong F ι hfin)
    (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (WeierstrassCurve.Affine.placeOfPoint P).restrictAlong ι hι
      = WeierstrassCurve.Affine.placeOfPoint (g P)) (P : W.Point) :
    WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN P = g P :=
  WeierstrassCurve.Affine.pointMapOfPushforward_eq_of_seam ι hι hfin hN g hg0 hg P

-- `Pic0` and the rational points agree: `genusOnePic0Equiv` inverts `pointClass`.
example {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [WeierstrassCurve.Affine.GenusOnePlaceGate W] [WeierstrassCurve.Affine.AbelTheorem W]
    (P : W.Point) :
    (WeierstrassCurve.Affine.genusOnePic0Equiv W).symm P
      = WeierstrassCurve.Affine.pointClass P :=
  WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply P

-- Zone: the H4 `restrictAlong` headline. Both headlines (general and the plain
-- `[CharZero F]` corollary) are executed under the pin's gate binders; the
-- module's section re-spelling means no `InfinitePlace` class appears among them.
#check @WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
#check @WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
#check @WeierstrassCurve.s2c_key
#check @WeierstrassCurve.s2c_zero
#check @WeierstrassCurve.kw_restrictAlong_placeOfPoint_kwVeluPointMap_odd
#check @WeierstrassCurve.Affine.IsogenyEndDatum.isIntegral_algHomId
#check @WeierstrassCurve.Affine.IsogenyEndDatum.finiteAlong_algHomId
#check @WeierstrassCurve.Affine.IsogenyEndDatum.restrictAlong_algHomId

example {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
    (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1 := by
  obtain ⟨ι, hι, hfin, hfr, -, -, -⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
      (W := W) (Q := Q) (n := n) hord hΔ'
  exact ⟨ι, hι, hfin, hfr⟩

example {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
    (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1 := by
  obtain ⟨ι, hι, hfin, hfr, -, -, -⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
      (W := W) (Q := Q) (n := n) hord hΔ'
  exact ⟨ι, hι, hfin, hfr⟩

#print axioms WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
#print axioms WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq

end WeierstrassCurveConsumer

end
