/-
  Consumer specification for the Riemann–Roch genus / index engine (phase 1).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the ported engine: the statements the 104 forward-cone
  consumers need, expressed in Lean so that each is either bound or not. It is a
  deliverable measure, not a proof obligation.

  It is deliberately **not part of any library**: nothing globs `spec/`, so it cannot
  break the verified port's green build. Run it by hand:

      cd lean
      lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean 2>&1 | grep -c error

  The error count is the metric (target 0).

  HOW TO READ IT
  --------------
  One zone per port set. Every zone contains the pinned statements it must make
  possible **and** at least one real, executed cross-module composition — deleting
  any one of the modules below must make this file fail to elaborate.

    [vocab]       ZONE A — Set D. The definition layer instantiated.
    [index]       ZONE B — H1a. The `RiemannGenusReachedAt` / `indexOfSpecialty` API.
    [tower]       ZONE C — H1b. The Stichtenoth tower, at its one concrete instance.
    [assembly]    ZONE D — H2. `WeilDualityAdelic` and RR with `genusFF`.
    [conditional] ZONE E — H3. The differentials interface at its pinned hypotheses.
    [residue-instance] ZONE F — P3.1. The `HasCanonicalLocalResidueKStar` producer,
                  which discharges ZONE E's instance hypothesis.
    [residue-theorem] ZONE G — P3.6/P3.7. The K ending (`ResidueTheoremK`), its
                  transport to the general `ResidueTheorem`, and the RR assembly.

  Cross-set compositions that would fail if a module were removed:
    C: `RationalFunctionField.stichtenothGenusExists` (H1b)
         → `exists_genus_riemannIndex_of_stichtenothGenusExists` (H1a, engine)
    D: `weilDualityAdelic_of_…` (H2)
         → `weilDuality_of_riemannIndex_of_adelic` (Set D assembly)
    D: `indexOfSpecialty_eq_finrank_H1` (H2) consumes Set D's `indexOfSpecialty`/`H1`
    E: the conditional headline consumes H2's `weilDifferentialRankOne_of_isCurveOver`
       only through its statement (it is stated, not discharged).
-/

import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.AlgebraicCurve.Canonical.WeilDifferential
import FLTForHuman.AlgebraicCurve.LocalResidue.Instance
import FLTForHuman.AlgebraicCurve.ResidueTheorem.GeneralFromK
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly

open AlgebraicCurve
open KaehlerDifferential

noncomputable section

/-! ## Zone A — `[vocab]` Set D: the definition layer, instantiated -/

-- The definitional shape of the adelic `omegaSpace` (Set D): mathlib's annihilator.
example {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    omegaSpace D = (adeleBddPrincipal K F D).dualAnnihilator := rfl

-- `ell 0 = 1` under the base-field hypothesis, through the Set D definition chain
-- `ConstantsAreBase → LSpace 0 → ell`.
example {K F : Type*} [Field K] [Field F] [Algebra K F] (h : ConstantsAreBase K F) :
    ell (0 : Divisor K F) = 1 :=
  ell_zero_eq_one_of_constantsAreBase h

-- Monotonicity: a composition of Set D's `Divisor` order with `LSpace`.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [Nonempty (Place K F)]
    {D E : Divisor K F} (hDE : D ≤ E) : LSpace D ≤ LSpace E :=
  lSpace_mono hDE

-- The two thin Set D assemblies compose: `WeilDuality → FunctionFieldRiemannRoch`.
example {K F : Type*} [Field K] [Field F] [Algebra K F] (hWD : WeilDuality K F) :
    FunctionFieldRiemannRoch K F :=
  functionFieldRiemannRoch_of_riemann_and_duality K F hWD

/-! ## Zone B — `[index]` H1a: the genus-reached / index API -/

-- `RiemannGenusReachedAt.eq_of_ge`: the maximality consequence used by the cone.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - (ell D : ℤ) = γ - 1 :=
  h.eq_of_ge hD

-- ... and its zero-index companion, a second use of the same hypothesis.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    indexOfSpecialty D₀ = 0 :=
  indexOfSpecialty_eq_zero_of_genusReached h

-- The engine: `StichtenothGenusExists` (a Set D predicate) yields the index formula.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) :
    ∃ γ, ∀ D : Divisor K F,
      Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) :=
  exists_genus_riemannIndex_of_stichtenothGenusExists h

/-! ## Zone C — `[tower]` H1b: the Stichtenoth tower at `RatFunc K` -/

-- The unconditional concrete instance: the separable `RatFunc K`-tower curve.
example (K : Type*) [Field K] [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  RationalFunctionField.stichtenothGenusExists K F hC

-- CROSS-SET COMPOSITION: the tower (H1b) feeds H1a's index engine, and the result is
-- applied to a divisor. Removing either `Genus/Stichtenoth.lean` or `Genus/Index.lean`
-- breaks this.
example (K : Type*) [Field K] [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] (hC : ConstantsAreBase K F)
    (D : Divisor K F) :
    ∃ γ, Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  obtain ⟨γ, hγ⟩ :=
    exists_genus_riemannIndex_of_stichtenothGenusExists
      (RationalFunctionField.stichtenothGenusExists K F hC)
  exact ⟨γ, hγ D⟩

-- Finiteness of `LSpace 0` (H1b) and `ell 0 = 1` (Set D): a two-module composition.
example (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F] (hC : ConstantsAreBase K F) :
    FiniteDimensional K ↥(LSpace (0 : Divisor K F)) ∧ ell (0 : Divisor K F) = 1 :=
  ⟨RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC,
    ell_zero_eq_one_of_constantsAreBase hC⟩

/-! ## Zone D — `[assembly]` H2: the adelic assembly and RR with `genusFF` -/

-- The H2 assembly: Riemann–Roch + genus existence give adelic Weil duality.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hFRR : FunctionFieldRiemannRoch K F) (hS : StichtenothGenusExists K F) :
    WeilDualityAdelic K F :=
  weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hFRR hS

-- CROSS-SET COMPOSITION: the H2 assembly composes with Set D's thin assembly to give
-- full Weil duality. Removing `RiemannRoch/Assembly.lean` (or Set D's
-- `RiemannRochRows.lean`, which supplies `weilDuality_of_riemannIndex_of_adelic`)
-- breaks this.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hRI : RiemannIndexFormula K F) (hFRR : FunctionFieldRiemannRoch K F)
    (hS : StichtenothGenusExists K F) : WeilDuality K F :=
  weilDuality_of_riemannIndex_of_adelic K F hRI
    (weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hFRR hS)

-- Riemann–Roch with the cohomological genus (`genusFF`).
example (K F : Type*) [Field K] [PerfectField K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F] (hC : ConstantsAreBase K F) :
    ∃ W, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF K F : ℤ) :=
  exists_weilCanonical_riemannRoch K F hC

-- The `H¹` identification: Set D's adelic `indexOfSpecialty` against the repartition
-- quotient `H1`.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (D : Divisor K F) : indexOfSpecialty D = Module.finrank K (H1 D) :=
  indexOfSpecialty_eq_finrank_H1 D

/-! ## Zone E — `[conditional]` H3: the differentials interface at its hypotheses -/

-- The headline is stated at the pin's hypotheses (`ResidueTheorem`,
-- `HasCanonicalDivisor`, …); they are *not* discharged here. This zone checks that the
-- conditional interface is usable at its pinned shape and that it returns the
-- `regularDifferentials ≃ omegaSpace 0` equivalence.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F] (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K F))
          = weilOfKaehler K F hω :=
  exists_linearEquiv_regularDifferentials_omegaSpace_zero hC hRT

/-! ## Zone F — `[residue-instance]` P3.1: the unconditional producer

`LocalResidue/Instance.lean` constructs the pin's
`instHasCanonicalLocalResidueKStar` under `[IsCurveOver K F] [PerfectField K]`, so
ZONE E's `HasCanonicalLocalResidueKStar` hypothesis is supplied by instance search
rather than by hand. Deleting that module must make this zone fail. -/

-- The producer: instance search, not a hypothesis, over a curve.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [PerfectField K] :
    HasCanonicalLocalResidueKStar K F := inferInstance

-- CROSS-SET COMPOSITION: the produced instance feeds the H3 differentials headline,
-- which therefore no longer needs `HasCanonicalLocalResidueKStar` as an explicit
-- hypothesis (compare ZONE E).
example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K F))
          = weilOfKaehler K F hω :=
  exists_linearEquiv_regularDifferentials_omegaSpace_zero hC hRT

/-! ## Zone G — `[residue-theorem]` P3.6/P3.7: the K ending, the general Residue
theorem, and the RR assembly

`ResidueTheorem/KFamily.lean` produces `ResidueTheoremK`; `ResidueTheorem/GeneralFromK.lean`
transports it to the general `ResidueTheorem` over an algebraically closed field;
`ResidueTheorem/RRAssembly.lean` consumes `ResidueTheoremK` and returns
`FunctionFieldRiemannRoch`. Deleting any of the three must make this zone fail. -/

-- The K-side bridge `ResidueTheoremK → ResidueTheorem` (P3.7b), at its short binder
-- block.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (h : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.ResidueTheorem K F :=
  AlgebraicCurve.residueTheorem_of_residueTheoremK h

-- CROSS-SET COMPOSITION: the row-3.6 K ending feeds the bridge, giving the general
-- Residue theorem over an algebraically closed field (P3.7b, consuming `KFamily`).
example {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheorem K F :=
  AlgebraicCurve.residueTheorem_of_isAlgClosed

-- The RR assembly (row 3.7): `ResidueTheoremK → FunctionFieldRiemannRoch`, at the
-- pin wrapper's binders with `hRTK` kept as a hypothesis.
example {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F :=
  AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed hRTK

end
