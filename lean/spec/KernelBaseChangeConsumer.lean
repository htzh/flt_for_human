/-
  Cross-module wire test for **D-5**, the kernel base change
  (`FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean`) together with the
  `PeriodPair` promotion set it consumes
  (`FLTForHuman/Elliptic/PeriodPair/Uniformization.lean`).

  A `spec/` probe, not a library module. It is separate from
  `spec/KernelCyclicTransferConsumer.lean` because D-5 is the only set that declares the
  `KwD5BetweenCurvesHoloLift` / `KwD5BetweenCurvesFFSeamBaseChange` /
  `KwD5BetweenCurvesKerTransportAlongEmbed` triple and the two headlines that consume the
  `kw_surge_hgf4_bc*` tensor transport; a separate file keeps the deletion probe
  unambiguous. (D-5, like D-4, imports the `IsogenyEndDatum/Engine.lean` cone, so it cannot
  be folded into `spec/BaseChangeConsumer.lean`.)

  Executed zones (each a real composition, no `#check`, no `sorry`; deleting
  `KernelBaseChange.lean` makes zones 2–5 fail, deleting the §1.5 promotion in
  `Uniformization.lean` makes zone 1 fail):

  * zone 1 — the D-5 §1.5 promotion: `PeriodPair.toPointAddEquiv` packages
    `ℂ ⧸ Λ ≃+ E(ℂ)`, `toPointHom_apply` identifies it with `toPoint`, and
    `ker_toPointHom` computes its kernel;
  * zone 2 — the `KwD5BetweenCurvesHoloLift` seam, consumed at a pair of `PeriodPair`s
    (hypothesis form: the port has no `L.weierstrassCurve.IsElliptic` instance and the
    gate/`AbelTheorem` producers are not co-importable with `Engine.lean`);
  * zone 3 — `hBC_s17` and `kerTransport_s17`, the two bare seam names the pin's silos
    use to assemble their headlines;
  * zone 4 — the first headline, hypothesis form, at the wrapper's exact binders;
  * zone 5 — the second headline, hypothesis form, at the wrapper's exact binders
    (`(R₀ : Type)`, the existential in `ι₁` with `∀ hN₁`).
-/
import FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate WeierstrassCurve TensorProduct

universe u

namespace KernelBaseChangeConsumer

/-! ### Zone 1 — the promoted `PeriodPair` API (D-5 §1.5) -/

/-- The uniformization packaging `ℂ ⧸ Λ ≃+ E(ℂ)`. -/
example (L : PeriodPair) :
    Nonempty ((ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (L.weierstrassCurve.toAffine).Point) :=
  ⟨L.toPointAddEquiv⟩

/-- `toPointHom` is `toPoint` at the promoted discriminant proof, and `mk` computes. -/
example (L : PeriodPair) (z : ℂ) :
    L.toPointHom z = L.toPoint L.discriminantNeZero z :=
  L.toPointHom_apply z

example (L : PeriodPair) (z : ℂ) :
    L.toPointAddEquiv (QuotientAddGroup.mk z) = L.toPoint L.discriminantNeZero z :=
  L.toPointAddEquiv_mk z

/-- The kernel of the uniformization map is the lattice. -/
example (L : PeriodPair) : L.toPointHom.ker = L.lattice.toAddSubgroup :=
  L.ker_toPointHom

/-! ### Zone 2 — the `KwD5BetweenCurvesHoloLift` seam at a pair of `PeriodPair`s -/

example (h : ModularCurve.KwD5BetweenCurvesHoloLift)
    (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [GenusOnePlaceGate L.weierstrassCurve]
    [GenusOnePlaceGate.IsCentred L.weierstrassCurve] [AbelTheorem L.weierstrassCurve]
    [L'.weierstrassCurve.IsElliptic] [GenusOnePlaceGate L'.weierstrassCurve]
    [GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'') :
    ∃ (F : ℂ → ℂ), Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z, L'.toPointHom (F z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom z) :=
  h L L' ι'' hι'' hfin''

/-! ### Zone 3 — the two seam `Prop`s produced by the module's engines -/

example : ModularCurve.KwD5BetweenCurvesFFSeamBaseChange := hBC_s17

example : ModularCurve.KwD5BetweenCurvesKerTransportAlongEmbed := kerTransport_s17

/-! ### Zone 4 — the first headline, hypothesis form -/

example
    (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀.baseChange F₁).IsElliptic] [(E₀'.baseChange F₁).IsElliptic]
    [(E₀.baseChange F₂).IsElliptic] [(E₀'.baseChange F₂).IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₁).toAffine]
    [AbelTheorem (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₁).toAffine]
    [AbelTheorem (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₂).toAffine]
    [AbelTheorem (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₂).toAffine]
    [AbelTheorem (E₀'.baseChange F₂).toAffine]
    (χ : (E₀.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₂).toAffine.FunctionField)
    (hχX : χ (polyToFunctionField (E₀.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀.baseChange F₂).toAffine Polynomial.X)
    (hχY : χ (yCoord (E₀.baseChange F₁).toAffine) = yCoord (E₀.baseChange F₂).toAffine)
    (χ' : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀'.baseChange F₂).toAffine.FunctionField)
    (hχ'X : χ' (polyToFunctionField (E₀'.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀'.baseChange F₂).toAffine Polynomial.X)
    (hχ'Y : χ' (yCoord (E₀'.baseChange F₁).toAffine) = yCoord (E₀'.baseChange F₂).toAffine)
    (ι₁ : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁) (hN₁ : NormFormulaAlong F₁ ι₁ hfin₁)
    (ι₂ : (E₀'.baseChange F₂).toAffine.FunctionField →ₐ[F₂] (E₀.baseChange F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂) (hN₂ : NormFormulaAlong F₂ ι₂ hfin₂)
    (hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x))
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N) :
    IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
      Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N :=
  WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
    R₀ E₀ E₀' F₁ F₂ χ hχX hχY χ' hχ'X hχ'Y ι₁ hι₁ hfin₁ hN₁ ι₂ hι₂ hfin₂ hN₂ hcompat N hcyc hcard

/-! ### Zone 5 — the second headline, hypothesis form -/

example
    (R₀ : Type) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F F' : Type) [Field F] [Field F'] [Algebra R₀ F] [Algebra R₀ F']
    [DecidableEq F] [DecidableEq F'] [IsAlgClosed F] [IsAlgClosed F'] [CharZero F] [CharZero F']
    [(E₀.baseChange F).IsElliptic] [(E₀'.baseChange F).IsElliptic]
    [(E₀.baseChange F').IsElliptic] [(E₀'.baseChange F').IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F).toAffine]
    [AbelTheorem (E₀.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F).toAffine]
    [AbelTheorem (E₀'.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F').toAffine]
    [AbelTheorem (E₀.baseChange F').toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F').toAffine]
    [AbelTheorem (E₀'.baseChange F').toAffine]
    (σ : F →ₐ[R₀] F')
    (ι₀ : (E₀'.baseChange F).toAffine.FunctionField →ₐ[F] (E₀.baseChange F).toAffine.FunctionField)
    (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀) (hN₀ : NormFormulaAlong F ι₀ hfin₀)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N) :
    ∃ (ι₁ : (E₀'.baseChange F').toAffine.FunctionField →ₐ[F'] (E₀.baseChange F').toAffine.FunctionField)
      (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F' ι₁),
      ∀ hN₁ : NormFormulaAlong F' ι₁ hfin₁,
        IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
          Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N :=
  WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
    R₀ E₀ E₀' F F' σ ι₀ hι₀ hfin₀ hN₀ N hcyc hcard

end KernelBaseChangeConsumer
