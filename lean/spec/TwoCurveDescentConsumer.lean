/-
  Cross-module wire test for **D-6**, the two-curve countable descent
  (`FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean`).

  A `spec/` probe, not a library module. D-6 imports the `IsogenyEndDatum/Engine.lean`
  cone through `KernelBaseChange.lean`, so — like the D-4/D-5 probes — it cannot be folded
  into `spec/BaseChangeConsumer.lean` or `spec/IntermediateFieldConsumer.lean`.

  Executed zones (each a real composition, no `#check`, no `sorry`; deleting
  `TwoCurveDescent.lean` makes every zone fail):

  * zone 1 — the headline at the concrete algebraically closed field `ℂ`. Its existential
    is unpacked and composed with `WeierstrassCurve.map_Δ`: the descended model `E₀`
    reproduces `E`'s discriminant. The gate instances are *hypotheses*: the port's only
    producer (`GenusOnePlaceGateCentred.lean`) is not co-importable with `Engine.lean`
    (`CARRY-FORWARD.md`, the `instInfinitePlace` collision).
  * zone 2 — the descent's degree output composed with the ported kernel-cardinality
    bridge `natCard_ker_pointMapOfPushforward_eq_finrankAlong`: `Nat.card (ker) = N` as
    soon as `finrankAlong K₀ ι' = finrankAlong K ι`. `K₀` is a hypothesis-form field here
    (it is not algebraically closed in the theorem; the capstone reads the bridge at the
    base change to `AlgebraicClosure K₀`).
  * zone 3 — the pin's `iotaDescent*` family: `iotaDescentCurve_map_FF` closes the
    `map_map` identity, and `iotaDescentPhi_X` / `iotaDescentPhi_yGen` compute the
    descended map on the function-field coordinate and `yGen`.
-/
import FLTForHuman.WeierstrassCurve.Isogeny.TwoCurveDescent

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate WeierstrassCurve

universe u

namespace TwoCurveDescentConsumer

/-! ### Zone 1 — the headline at `ℂ`, unpacked and composed with `map_Δ` -/

/-- The two-curve descent at the concrete field `ℂ`, gate data as hypotheses, its
existential unpacked so that the descended model `E₀` reproduces `E`'s discriminant. -/
example
    (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    ∃ (K₀ : IntermediateField ℚ ℂ) (_ : Countable K₀) (E₀ : WeierstrassCurve K₀)
      (_ : E₀.IsElliptic) (_ : E₀.map (algebraMap K₀ ℂ) = E),
      (algebraMap K₀ ℂ) E₀.Δ = E.Δ := by
  obtain ⟨K₀, hCount, E₀, E₀', hE₀ell, hE₀'ell, hE₀map, _hE₀'map, _hAC, _hAC', _ι₀, _hι₀,
    _hfin₀, _hgate⟩ :=
    WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
      E E' ι hι hfin hN N hcyc hcard
  exact ⟨K₀, hCount, E₀, hE₀ell, hE₀map, by rw [← WeierstrassCurve.map_Δ, hE₀map]⟩

/-! ### Zone 2 — the descent's `finrankAlong`, composed with the cardinality bridge -/

/-- Once the descended isogeny has the same `finrankAlong` as `ι`, the ported bridge
`natCard_ker_pointMapOfPushforward_eq_finrankAlong` turns the bridge at `K` into the
cardinality of the descended kernel. -/
example
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {K₀ : Type u} [Field K₀] [DecidableEq K₀] [IsAlgClosed K₀] [CharZero K₀]
    [Algebra K₀ K]
    (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    [GenusOnePlaceGate E₀.toAffine] [AbelTheorem E₀.toAffine]
    [GenusOnePlaceGate E₀'.toAffine] [AbelTheorem E₀'.toAffine]
    (ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField)
    (hι' : ι'.toRingHom.IsIntegral) (hfin' : FiniteAlong K₀ ι')
    (hN' : NormFormulaAlong K₀ ι' hfin')
    (hfinrank : finrankAlong K₀ ι' = 0) :
    Nat.card (pointMapOfPushforward ι' hι' hfin' hN').ker = 0 := by
  rw [natCard_ker_pointMapOfPushforward_eq_finrankAlong E₀.toAffine E₀'.toAffine
    ι' hι' hfin' hN', hfinrank]

/-! ### Zone 3 — the pin's `iotaDescent*` family -/

/-- `iotaDescentCurve_map_FF` is the `map_map` identity at `E`, and the descended map
computes on `X` and `yGen`. -/
example {K : Type u} [Field K] [Algebra ℚ K] {K₀ : IntermediateField ℚ K}
    (E : WeierstrassCurve K) [E.IsElliptic] (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]
    (h : E₀.map (algebraMap K₀ K) = E) :
    E₀.map (algebraMap K₀ E.toAffine.FunctionField)
        = E.map (algebraMap K E.toAffine.FunctionField) ∧
      E₀.map ((algebraMap K E.toAffine.FunctionField).comp (algebraMap K₀ K))
        = E.map (algebraMap K E.toAffine.FunctionField) ∧
      ModularCurve.iotaDescentPhi E E₀ h (polyToFunctionField E₀.toAffine X)
        = polyToFunctionField E.toAffine X ∧
      ModularCurve.iotaDescentPhi E E₀ h (yGen E₀.toAffine) = yGen E.toAffine := by
  refine ⟨ModularCurve.iotaDescentCurve_map_FF E E₀ h, ?_,
    ModularCurve.iotaDescentPhi_X E E₀ h, ModularCurve.iotaDescentPhi_yGen E E₀ h⟩
  rw [← WeierstrassCurve.map_map, h]

/-- The transcendental and equation data of `iotaDescentPhi` are the two inputs of the
descended map: the equation holds by `iotaDescentPhi_equation`, and transcendence is the
`aeval` injectivity the descent consumes. -/
example {K : Type u} [Field K] [Algebra ℚ K] {K₀ : IntermediateField ℚ K}
    (E : WeierstrassCurve K) [E.IsElliptic] (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]
    (h : E₀.map (algebraMap K₀ K) = E) :
    (E₀.map (algebraMap K₀ E.toAffine.FunctionField)).toAffine.Equation
        (polyToFunctionField E.toAffine X) (yGen E.toAffine) ∧
      Function.Injective
        (Polynomial.aeval (R := K₀) (polyToFunctionField E.toAffine X)) :=
  ⟨ModularCurve.iotaDescentPhi_equation E E₀ h,
    ModularCurve.iotaDescentPhi_transcendental E⟩

end TwoCurveDescentConsumer
