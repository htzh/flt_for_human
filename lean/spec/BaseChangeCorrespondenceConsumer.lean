/-
  Consumer specification for base change of a correspondence along a constant field
  extension (`AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension`).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the headline: the statement the port must make possible,
  composed with the divisor and `Pic⁰` correspondence API, expressed in Lean so that it is
  either bound or not. It is a deliverable measure, not a proof obligation.

  It is deliberately **not part of any library** (`lake build` does not see `spec/`).
  Run it by hand:

      cd lean
      timeout 180 lake env lean -DmaxHeartbeats=4000000 spec/BaseChangeCorrespondenceConsumer.lean 2>&1 | grep -c error

  The error count is the metric; deleting the module must make it fail.

  ZONES
  -----
    [capstone]  ZONE A — the base-changed correspondence acts on `Pic⁰`: the headline's
                eleven-component `∃` is unpacked, and its `FundamentalIdentityAlong`,
                `FiniteAlong` and `NormFormulaAlong` fields are fed to
                `Pic0.correspondence`, so the existential really carries the data the
                along-formulas need. Nothing is restated: every name consumed is a
                public declaration of `Defs/Correspondence.lean` or of the module.
    [fibre]     ZONE B — the fibre formula's unramified half, at a place centred at a
                `K`-embedding: `fibre_centred` says every place above `P` has ramification
                index one, so `pullbackAlong φE hφE (single P 1)` is the fibre sum with
                coefficient one (`Divisor.pullbackAlong_single` composed with it).
-/

import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.IsCurveOver.BaseChangeCorrespondence

set_option autoImplicit false

set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

universe u v w x

/-! ## Zone A — `[capstone]` the base-changed correspondence on `Pic⁰` -/

example (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type w) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E : Type x) (FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    ∃ (F'E : Type (max w x)) (_ : Field F'E) (_ : Algebra E F'E) (_ : Algebra F' F'E)
      (_ : Algebra K F'E) (_ : IsScalarTower K E F'E) (_ : IsScalarTower K F' F'E)
      (_ : IsCurveOver E F'E),
      Nonempty (Pic0 E FE →+ Pic0 E FE) ∧
      (∃ x' : F'E, Transcendental E x' ∧
        FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E) ∧
      IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤ := by
  obtain ⟨F'E, iF, iE, iF', iK, iT1, iT2, iCurve, φE, ψE, hφE, hψE, hFIφE, hfinE, hNψE,
    h1, h2, -⟩ :=
    exists_baseChange_correspondence_of_constantFieldExtension K F hfg F' φ ψ hφ hψ hFI hfin hN
      E FE hfgE hgen
  haveI : IsCurveOver E F'E := iCurve
  haveI : HasPrincipalDivisors E F'E := IsCurveOver.hasPrincipalDivisors
  exact ⟨F'E, iF, iE, iF', iK, iT1, iT2, iCurve,
    ⟨Pic0.correspondence φE ψE hφE hψE hFIφE hfinE hNψE⟩, h1, h2⟩

/-! ## Zone B — `[fibre]` the pullback of a centred place is the fibre with coefficient one -/

example {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    [Field F'] [Algebra K F'] [IsCurveOver K F']
    [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ)
    (χE : FE →ₐ[E] F'E) (hχEi : χE.toRingHom.IsIntegral)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (hFI : FundamentalIdentityAlong E χE hχEi)
    {P : Place E FE} {e : F →ₐ[K] E}
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) :
    Divisor.pullbackAlong χE hχEi (Finsupp.single P 1) =
      ∑ W ∈ Place.fiberAlong χE hχEi P, Finsupp.single W (1 : ℤ) := by
  obtain ⟨ha, -⟩ :=
    BaseChangeCorrespondence.fibre_centred hfg hfgE hgen hfg' hfgE' hgen' χ hfin χE hχEi hχE hFI hP
  rw [Divisor.pullbackAlong_single]
  exact Finset.sum_congr rfl fun W hW => by simp [ha W hW]
