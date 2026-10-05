/-
  Cross-module wire test for the Weierstrass principal-divisor capstone and the
  Vélu port (H0 bridge + SET-1 dictionary and vocabulary + SET-2 discriminant and
  SET-3 quotient-`j`).

  A `spec/` probe, not a library module. Executed zones: the function-field
  prerequisites (`adjoin_yCoord_eq_top`, `finiteDimensional_ratFunc_functionField`),
  the headline `hasPrincipalDivisors_functionField`, applied both at a variable
  curve over `ℚ` (discharging `[CharZero ℚ]`) and at a concrete curve, the H0
  bridge (`yGen`, `polyToFunctionField_eq_aeval`,
  `equation_map_polyToFunctionField_yGen`, `transcendental_polyToFunctionField_X`),
  composed with the generation theorem, the SET-1 place dictionary plus Vélu
  vocabulary (`veluGx`/`veluGy`/`veluQuotient`/`oddOrderSummingSet`, `IsFinitePlace`,
  `isDedekindDomain_of_Δ_ne_zero`, `placeOfEquation`) at concrete curves, the SET-1
  order-two quotient and its point map, the SET-2 odd-order discriminant identity
  with its `ψ`-counting and cyclic-kernel enumeration, and the SET-3 quotient `j`
  (`vcInvFun_add` as a `→+`, `cyclicQuotientJ` on a `zmultiples` subgroup, and its
  base-change/Galois invariance).
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
import FLTForHuman.WeierstrassCurve.Velu.OrderTwo
import FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap
import FLTForHuman.WeierstrassCurve.Velu.Equivariance
import FLTForHuman.WeierstrassCurve.Velu.Discriminant
import FLTForHuman.WeierstrassCurve.Velu.CyclicCount
import FLTForHuman.WeierstrassCurve.Velu.VariableChangePoint
import FLTForHuman.WeierstrassCurve.Velu.CyclicQuotientJ
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic

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

-- Zone (V1 SET-1): the order-two quotient column (`Velu/OrderTwo.lean` and
-- `Velu/OrderTwoMap.lean`). The 2-torsion curve `y² = x³ - x` over `ℚ` with the
-- kernel point `(0, 0)` (`veluGy 0 0 = 0`), so `veluQuotient2 0 0` is the
-- order-two quotient of the kernel `{0, (0, 0)}`.
abbrev W2 : WeierstrassCurve ℚ := WeierstrassCurve.mk 0 0 0 (-1) 0

private lemma W2_equation : W2.toAffine.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [W2]

private lemma W2_veluGy : W2.veluGy 0 0 = 0 := by
  norm_num [W2, WeierstrassCurve.veluGy]

private lemma W2_two_ne_zero : (2 : ℚ) ≠ 0 := by norm_num

-- `veluGx 0 0 = -1` (`Velu/Defs.lean`) so `velu2QuadDisc 0 = b₂² - 32·b₄ = 64`,
-- and the `OrderTwo.lean` node pins the quotient discriminant to `-1 · 64²`.
private lemma W2_veluQuotient2_Δ_ne_zero : (W2.veluQuotient2 0 0).Δ ≠ 0 := by
  rw [WeierstrassCurve.veluQuotient2_Delta_eq W2_equation W2_veluGy]
  norm_num [W2, WeierstrassCurve.veluGx, WeierstrassCurve.velu2QuadDisc,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

private lemma W2_isElliptic : W2.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by
    rw [WeierstrassCurve.Delta_eq_veluGx_sq_mul_velu2QuadDisc W2_equation W2_veluGy]
    norm_num [W2, WeierstrassCurve.veluGx, WeierstrassCurve.velu2QuadDisc,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄])⟩

example : (W2.veluQuotient2 0 0).a₄ = 4 := by
  rw [WeierstrassCurve.veluQuotient2_a₄]
  norm_num [W2, WeierstrassCurve.veluGx]

example : (W2.veluQuotient2 0 0).b₂ = W2.b₂ := W2.veluQuotient2_b₂ 0 0

example : W2.veluGx 0 0 * W2.velu2QuadDisc 0 ^ 2 = -4096 := by
  norm_num [W2, WeierstrassCurve.veluGx, WeierstrassCurve.velu2QuadDisc,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

-- Cross-module composition with `Velu/Defs.lean`: the empty Vélu set fixes the
-- curve (`veluQuotient_empty`), so the order-two quotient of the fixed curve is
-- the order-two quotient of `W2`.
example : (W2.veluQuotient ∅).veluQuotient2 0 0 = W2.veluQuotient2 0 0 :=
  congrArg (fun W : WeierstrassCurve ℚ => W.veluQuotient2 0 0)
    (WeierstrassCurve.veluQuotient_empty W2)

-- The `OrderTwo.lean` discriminant factorization at the kernel point ...
example : W2.Δ = W2.veluGx 0 0 ^ 2 * W2.velu2QuadDisc 0 :=
  WeierstrassCurve.Delta_eq_veluGx_sq_mul_velu2QuadDisc W2_equation W2_veluGy

example : (W2.veluQuotient2 0 0).Δ = -4096 := by
  rw [WeierstrassCurve.veluQuotient2_Delta_eq W2_equation W2_veluGy]
  norm_num [W2, WeierstrassCurve.veluGx, WeierstrassCurve.velu2QuadDisc,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

example : (W2.veluQuotient2 0 0).IsElliptic := by
  haveI : W2.IsElliptic := W2_isElliptic
  exact WeierstrassCurve.isElliptic_veluQuotient2_of_isElliptic W2_equation W2_veluGy

-- The `OrderTwoMap.lean` headline at the concrete curve, used as a genuine `→+`:
-- additivity is exercised with `map_add`, and the coercion is `veluPointMap2`.
example : ∃ φ : W2.toAffine.Point →+ (W2.veluQuotient2 0 0).toAffine.Point,
    (∀ P Q, φ (P + Q) = φ P + φ Q) ∧
      ⇑φ = WeierstrassCurve.veluPointMap2 W2_two_ne_zero W2_equation W2_veluGy
        W2_veluQuotient2_Δ_ne_zero := by
  haveI : W2.IsElliptic := W2_isElliptic
  obtain ⟨φ, hφ⟩ := WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2 W2
    W2_two_ne_zero W2_equation W2_veluGy W2_veluQuotient2_Δ_ne_zero
  exact ⟨φ, fun P Q => map_add φ P Q, hφ⟩

example : WeierstrassCurve.veluPointMap2 (W := W2) (x₀ := 0) (y₀ := 0)
    W2_two_ne_zero W2_equation W2_veluGy W2_veluQuotient2_Δ_ne_zero
    (0 : W2.toAffine.Point) = 0 :=
  WeierstrassCurve.veluPointMap2_zero (W := W2) (x₀ := 0) (y₀ := 0) _ _ _ _

#print axioms WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2
#print axioms WeierstrassCurve.veluQuotient2_Delta_eq

-- Zone (V1 SET-2): the odd-order discriminant column (`Velu/Equivariance.lean`,
-- `Velu/Discriminant.lean`, `Velu/CyclicCount.lean`).

-- (a) `Velu/Equivariance.lean`, the variable-change/base-change definition layer
-- (the pin's `Def_..._VeluVariableChange` whole plus the `map_velu*` block of
-- `Def_..._VeluEquivariance`). The curve is `y² = x³ + 1`; the variable-change
-- identity is evaluated at `(x, y) = (1, 1)`, where `Velu/Defs.lean`'s
-- `veluU 1 1 = (veluGy 1 1)² = (-2)² = 4`.
abbrev W3 : WeierstrassCurve ℚ := WeierstrassCurve.mk 0 0 0 0 1

example (C : WeierstrassCurve.VariableChange ℚ) :
    (C • W3).veluU (vcXInv C 1) (vcYInv C 1 1)
      = ((C.u⁻¹ : ℚˣ) : ℚ) ^ 6 * 4 := by
  rw [WeierstrassCurve.variableChange_veluU C W3 1 1]
  norm_num [W3, WeierstrassCurve.veluU, WeierstrassCurve.veluGy]

-- and the base-change commutation of the same layer: with the identity ring hom
-- the Vélu quotient does not move.
example (S : Finset (ℚ × ℚ)) :
    (W3.map (RingHom.id ℚ)).veluQuotient
        (S.map ⟨Prod.map (RingHom.id ℚ) (RingHom.id ℚ),
          Function.injective_id.prodMap Function.injective_id⟩)
      = W3.veluQuotient S := by
  rw [WeierstrassCurve.map_veluQuotient (W := W3) (f := RingHom.id ℚ) S
    Function.injective_id]
  simp

-- (b) `Velu/Discriminant.lean`: the identity
-- `Δ(W.veluQuotient S) · (∏_{P∈S} u_P)^4 = Δ(W)^(2n+1)` at an order-three point.
-- `W3.Δ = -432` and `n = 1`.
private lemma W3_Δ : W3.Δ = -432 := by
  norm_num [W3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma W3_isElliptic : W3.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [W3_Δ]; norm_num)⟩

-- the empty summing set: `veluQuotient ∅ = W`, so `Δ` is unchanged — the numeric
-- anchor for the set's `Velu/Defs.lean` vocabulary.
example : (W3.veluQuotient ∅).Δ = -432 := by
  rw [WeierstrassCurve.veluQuotient_empty, W3_Δ]

-- composition of this set's `isOddVeluSet_oddOrderSummingSet` with the
-- `Velu/Defs.lean` `veluU_eq_Ψ₂Sq_eval`: on an odd Vélu set the `veluU` product
-- is the product of the `Ψ₂Sq` evaluations at the x-coordinates.
example {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    {Q : W.toAffine.Point} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    ∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2
      = ∏ P ∈ W.oddOrderSummingSet Q n, W.Ψ₂Sq.eval P.1 :=
  Finset.prod_congr rfl fun P hP =>
    W.veluU_eq_Ψ₂Sq_eval
      ((W.isOddVeluSet_oddOrderSummingSet hp hp2 hord hn).equation P hP)

-- the identity, and the nonvanishing corollary it powers.
example (Q : W3.toAffine.Point) (hQ : addOrderOf Q = 3) :
    (W3.veluQuotient (W3.oddOrderSummingSet Q 1)).Δ *
        (∏ P ∈ W3.oddOrderSummingSet Q 1, W3.veluU P.1 P.2) ^ 4 = W3.Δ ^ 3 := by
  haveI : W3.IsElliptic := W3_isElliptic
  exact WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow W3 Q hQ

example (Q : W3.toAffine.Point) (hQ : addOrderOf Q = 3) :
    (W3.veluQuotient (W3.oddOrderSummingSet Q 1)).Δ ≠ 0 := by
  haveI : W3.IsElliptic := W3_isElliptic
  exact WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
    W3 1 Q (by rw [hQ])

-- (c) `Velu/CyclicCount.lean`: the ψ-counting pair and the cyclic-kernel
-- enumeration. Concrete ψ values first, then the two headlines, then the
-- enumeration composed with (b)'s nonvanishing node.
#eval ModularCurve.dedekindPsi 6
#eval ModularCurve.dedekindPsi 12

example (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n}
      = ModularCurve.dedekindPsi n :=
  ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi n

example (n : ℕ) [NeZero n] {A : Type*} [AddCommGroup A]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n}
      = ModularCurve.dedekindPsi n :=
  AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy n e

example {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 4 ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = 3) ∧
        (Function.Injective fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (3 / 2))).Δ ≠ 0 := by
  obtain ⟨ι, hfin, hcard, Q, hQ, hinj, -⟩ :=
    WeierstrassCurve.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
      (K := K) (ℓ := 3) (by norm_num) (by norm_num) W
  refine ⟨ι, hfin, hcard, Q, hQ, hinj, fun i => ?_⟩
  exact WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
    W (3 / 2) (Q i) (by rw [hQ i])

#print axioms WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
#print axioms WeierstrassCurve.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero

#print axioms WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
#print axioms WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq

-- Zone (V1 SET-3): the quotient-`j` column (`Velu/VariableChangePoint.lean`,
-- `Velu/CyclicQuotientJ.lean`).

-- (a) `Velu/VariableChangePoint.lean`: the one off-subject prerequisite,
-- `Affine.Point.vcInvFun_add`, bundled into a genuine `→+` and composed with the
-- SET-2 `Velu/Equivariance.lean` core — `vcFun` is a left/right inverse, so the
-- bundle is an additive equivalence up to `vcFun`.
private noncomputable def vcAddHom (C : WeierstrassCurve.VariableChange ℚ)
    (W : WeierstrassCurve ℚ) : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := WeierstrassCurve.Affine.Point.vcInvFun C W
  map_zero' := rfl
  map_add' := WeierstrassCurve.Affine.Point.vcInvFun_add C W

example (C : WeierstrassCurve.VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (P Q : W.toAffine.Point) :
    vcAddHom C W (P + Q) = vcAddHom C W P + vcAddHom C W Q :=
  map_add (vcAddHom C W) P Q

example (C : WeierstrassCurve.VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (P : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.vcFun C W (vcAddHom C W P) = P :=
  WeierstrassCurve.Affine.Point.vcFun_rightInverse P

-- A numeric anchor for the transport itself: the inverse coordinates of the
-- variable change `u = 1, r = 5, s = 0, t = 7` at `(9, 11)` are `(4, 4)`.
private abbrev Cc : WeierstrassCurve.VariableChange ℚ := ⟨1, 5, 0, 7⟩

example : WeierstrassCurve.Affine.vcXInv Cc 9 = 4 := by
  norm_num [Cc, WeierstrassCurve.Affine.vcXInv]

example : WeierstrassCurve.Affine.vcYInv Cc 9 11 = 4 := by
  norm_num [Cc, WeierstrassCurve.Affine.vcYInv]

-- (b) `Velu/CyclicQuotientJ.lean`: the quotient `j`. The curve is the SET-1
-- `y² = x³ - x` (`W2` above); the subgroup is `zmultiples` of its 2-torsion point
-- `(0, 0)`.
private lemma W2_nonsingular_zero : W2.toAffine.Nonsingular 0 0 :=
  (WeierstrassCurve.Affine.nonsingular_iff' (W := W2.toAffine) 0 0).mpr
    ⟨W2_equation, Or.inl (by norm_num [W2])⟩

private def W2P : W2.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 0 0 W2_nonsingular_zero

-- `c₄ = b₂² - 24·b₄ = 48` and `Δ = -8·b₄³ = 64`, so `j = 48³/64 = 1728` — the
-- classical value for `y² = x³ - x`.
example : W2.cyclicQuotientJ (AddSubgroup.zmultiples W2P) 1 = 1728 := by
  rw [WeierstrassCurve.cyclicQuotientJ_one]
  norm_num [W2, WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

-- The iteration step at `N = 2`: the recursion peels off `minFac = 2` and hands
-- the quotient to the order-two branch, whose `stepCurve` is `Velu/Defs.lean`'s
-- `xVelu`/two-torsion vocabulary.
example : W2.cyclicQuotientJ (AddSubgroup.zmultiples W2P) 2
    = (W2.stepCurve (AddSubgroup.zmultiples W2P) 2).cyclicQuotientJ
        (W2.stepSubgroup (AddSubgroup.zmultiples W2P) 2) 1 :=
  WeierstrassCurve.cyclicQuotientJ_eq_of_two_le W2 _ (by norm_num)

example : W2.stepCurve (AddSubgroup.zmultiples W2P) 2
    = W2.twoVeluCurve (W2.kernelXSet (AddSubgroup.zmultiples W2P) 2) :=
  WeierstrassCurve.stepCurve_two W2 _

example (ℓ : ℕ) (hℓ : ℓ ≠ 2) :
    W2.stepCurve (AddSubgroup.zmultiples W2P) ℓ
      = W2.xVeluCurve (W2.kernelXSet (AddSubgroup.zmultiples W2P) ℓ) :=
  WeierstrassCurve.stepCurve_of_ne_two W2 _ hℓ

-- The base-change lemma, applied at complex conjugation on `y² = x³ - x` over
-- `ℝ`: the quotient `j` is `Gal(ℂ/ℝ)`-invariant. This is the pinned statement's
-- own binder shape (`R = ℝ`, `A = B = ℂ`, `f = conjAe`); the curve must be the
-- `R`-curve `W2R` because `Point.map` is indexed on the base ring, so there is no
-- instantiation from `W2 : WeierstrassCurve ℚ` with `f : ℂ →ₐ[ℝ] ℂ`.
abbrev W2R : WeierstrassCurve ℝ := WeierstrassCurve.mk 0 0 0 (-1) 0

private abbrev conj : ℂ →ₐ[ℝ] ℂ := Complex.conjAe

example {H : AddSubgroup (W2R.baseChange ℂ).toAffine.Point} (N : ℕ) :
    (W2R.baseChange ℂ).cyclicQuotientJ
        (H.map (WeierstrassCurve.Affine.Point.map conj)) N
      = conj ((W2R.baseChange ℂ).cyclicQuotientJ H N) :=
  WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed W2R conj H N

-- The numeric anchor survives the base change along `ℝ → ℝ`.
example : (W2R.baseChange ℝ).cyclicQuotientJ ⊥ 1 = 1728 := by
  rw [WeierstrassCurve.cyclicQuotientJ_one]
  norm_num [W2R, WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

#print axioms WeierstrassCurve.cyclicQuotientJ_variableChange_eq
#print axioms WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

end WeierstrassCurveConsumer

end
