/-
Tate agreement — the agreement half: the Cohen–Tate projector independence and the
Cohen kernel-data construction, after FLT's
`P2M/Sol/S_AlgebraicCurve_tateAgreement.lean` (4,816 ln, 173 checked declarations)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean>),
published as `AlgebraicCurve.tateAgreement` by
`Theorems/Thm_AlgebraicCurve_tateAgreement.lean`.

This is set 3.3c.  It proves the pin's `KwF4gRRTateProjectorIndep` and
`KwF4gRRTateCohenTateAgreement` atoms through the Cohen–Tate kernel-data route
(`TateCohenKernelData → KwTateRR3CohenLaurentSpec → KwTateRR3CohenLaurentCompl`),
and exposes the pin's public surface at its own names.  The shared finiteness chain
(`tateProj`, the pole window, `DVRQuotPowKFinite`, `DVRCotangentKFinite`,
`tateCommFinite`) is **imported** from `Tate/CommFinite.lean`; the vocabulary
(`tateComm`, `tateCommTrace`, `lmulK`, the `KwF4gRRTate*` atoms) is imported from
`Defs/TateResidueCurrency.lean`.

Assumes: `Tate/CommFinite.lean` (the finiteness half and its `InlineSpecific`
uniformizer slice), `Defs/TateResidueCurrency.lean` (the Tate vocabulary),
`LocalResidue/Instance.lean` (the canonical local residue instance, the `Lg37`
completion layer and `aCoeff`) and `P1/DivPow.lean` (the two
`kwHgfV352_localResidueCompletion_{spec,algebraMap}` facts).

Import-discharged (not re-proved here): the 37 pin declarations of the shared
`tateCommFinite` chain that `Tate/CommFinite.lean` already carries with identical
statements, the two pin-private `Place.ord_nonneg_of_mem`/`mem_of_ord_nonneg`
(public in `Defs/PushPull.lean`) and the pin-private `mem_iff_ord_nonneg`; the two
checker-invisible `scoped instance`s `kwF4R1V410a_subsingletonHeightOneSpectrumDVR`
and `instIsScalarTower_K_toValuationSubring_adicCompletionIntegers` are imported
from `Tate/CommFinite.lean`.  The pin's `p2m_*` scaffolding and its local
`maxHeartbeats` raises are dropped (the project cap is 4,000,000).

Refactor round (row 3.4).  The P3.3 collision measurement claimed this module's copies
were `private`; they were public, and 22 of them collided with `Tate/Prelude.lean` (4)
and `Tate/TraceCompat.lean` (18), so no module could import `Agreement` together with
`ChainRule`/`TraceCompat` — exactly what set 3.4's `tateAgreement` consumer needs.
This module now imports `Tate/Prelude.lean` and `Tate/TraceCompat.lean`, and the 22
statement-identical duplicate public declarations are deleted.  The names remain
available through the imported copies (`Prelude`/`TraceCompat`), so the checker's
`identical` count is unaffected by the move, and the four Tate theory modules now import
together with no shared public FQN.  See `AUDIT-mathlib-p3-4.md` §2 Correction 2.
-/
import FLTForHuman.AlgebraicCurve.Defs.TateResidueCurrency
import FLTForHuman.AlgebraicCurve.Tate.CommFinite
import FLTForHuman.AlgebraicCurve.Tate.Prelude
import FLTForHuman.AlgebraicCurve.Tate.TraceCompat
import FLTForHuman.AlgebraicCurve.LocalResidue.Instance
import FLTForHuman.AlgebraicCurve.P1.DivPow
import FLTForHuman.AlgebraicCurve.Place.Completion
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open LinearMap Submodule IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain.HeightOneSpectrum.adicCompletion
open WithZero Multiplicative MonoidWithZeroHom
open AlgebraicCurve AlgebraicCurve.Place
open ModularCurve.KwF4gRRTate
open ModularCurve.KwF4R1V410a
open ModularCurve.Lg37 ModularCurve.KwNo6Pin Mp72a102T1 Mp72a102T2 ModularCurve.Mp72a102T3 Mp72a103T2
open scoped Pointwise Polynomial

/-! ### The unported `InlineSpecific` uniformizer slice (private)

`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` supplies `completionIdeal`
(pin 299), `exists_ofAdd_natCast_lt` (pin 104) and the uniformizer chain reached by
`instIsAdicCompleteCompletionIdealAdicCompletionIntegers` (pin 580) and the
`kwF4R1V410a_*` bridge.  The port carried the same slice `private` in
`Tate/CommFinite.lean`; a `private` is module-local, so the rows reached here are
re-landed `private` at the pin's names.  **Promotion debt**: a shared
`Place/Completion.lean` home (see the friction log). -/



section
end
namespace AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve
namespace FiberKaehlerLocalDatum
end AlgebraicCurve.FiberKaehlerLocalDatum
namespace AlgebraicCurve
namespace Place
end AlgebraicCurve.Place
namespace AlgebraicCurve
namespace RationalFunctionField
end AlgebraicCurve.RationalFunctionField
namespace AlgebraicGeometry
end AlgebraicGeometry
namespace AlgebraicGeometry
namespace KwSmoothIrredRelDimConstantEngine
end AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine
namespace BigOperators
end BigOperators
namespace CategoryTheory
end CategoryTheory
namespace CategoryTheory
namespace Limits
end CategoryTheory.Limits
namespace Classical
end Classical
namespace CongruenceSubgroup
end CongruenceSubgroup
namespace Deformation
namespace ModpDieudonne
end Deformation.ModpDieudonne
namespace Deformation
namespace PDivisible
end Deformation.PDivisible
namespace FLT
namespace HopfSpec
end FLT.HopfSpec
namespace Filter
end Filter
namespace FunctionField
end FunctionField
namespace GoodReductionJacobian
end GoodReductionJacobian
namespace IntermediateField
end IntermediateField
namespace IsDedekindDomain
end IsDedekindDomain
namespace IsDedekindDomain
namespace HeightOneSpectrum
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing
end IsLocalRing
namespace KaehlerDifferential
end KaehlerDifferential
namespace Ldgr23CohenDefectCorrectionSlice
end Ldgr23CohenDefectCorrectionSlice
namespace Ldgr24DefectKernelSlice
end Ldgr24DefectKernelSlice
namespace Ldgr25CorrectedChoiceSlice
end Ldgr25CorrectedChoiceSlice
namespace Ldgr30BankGate
end Ldgr30BankGate
namespace LinearMap
end LinearMap
namespace ModularCurve
end ModularCurve
namespace ModularCurve
namespace KwF4R1V391a
end ModularCurve.KwF4R1V391a
namespace ModularCurve
namespace KwF4R1V392a
end ModularCurve.KwF4R1V392a
namespace ModularCurve
namespace KwF4R1V394a
end ModularCurve.KwF4R1V394a
namespace ModularCurve
namespace KwF4R1V410a
end ModularCurve.KwF4R1V410a
namespace ModularCurve
namespace KwF4gRRTate
end ModularCurve.KwF4gRRTate
namespace ModularCurve
namespace KwNo6HrouteR
end ModularCurve.KwNo6HrouteR
namespace ModularCurve
namespace KwNo6HrouteS
end ModularCurve.KwNo6HrouteS
namespace ModularCurve
namespace KwNo6HrouteV
end ModularCurve.KwNo6HrouteV
namespace ModularCurve
namespace KwNo6HrouteY
end ModularCurve.KwNo6HrouteY
namespace ModularCurve
namespace KwNo6HrouteZ
end ModularCurve.KwNo6HrouteZ
namespace ModularCurve
namespace KwNo6Pin
end ModularCurve.KwNo6Pin
namespace ModularCurve
namespace KwNo6Section
end ModularCurve.KwNo6Section
namespace ModularCurve
namespace KwOdaDHDR
end ModularCurve.KwOdaDHDR
namespace ModularCurve
namespace KwTateRR3
end ModularCurve.KwTateRR3
namespace ModularCurve
namespace GF24a11bRowACurrencyBridge
end ModularCurve.GF24a11bRowACurrencyBridge
namespace ModularCurve
namespace GF24a12CohenSupply
end ModularCurve.GF24a12CohenSupply
namespace ModularCurve
namespace GF24a9RRDx
end ModularCurve.GF24a9RRDx
namespace ModularCurve
namespace Ldgr25CotraceCompatSlice
end ModularCurve.Ldgr25CotraceCompatSlice
namespace ModularCurve
namespace Ldgr25PlaceExtensionSlice
end ModularCurve.Ldgr25PlaceExtensionSlice
namespace ModularCurve
namespace Ldgr29SimplePoleResidueSlice
end ModularCurve.Ldgr29SimplePoleResidueSlice
namespace ModularCurve
namespace Ldgr31PerPlaceRowJoinSlice
end ModularCurve.Ldgr31PerPlaceRowJoinSlice
namespace ModularCurve
namespace Ldgr32RegularLegSlice
end ModularCurve.Ldgr32RegularLegSlice
namespace ModularCurve
namespace Ldgr35Cs
end ModularCurve.Ldgr35Cs
namespace ModularCurve
namespace Ldgr36Rc
end ModularCurve.Ldgr36Rc
namespace ModularCurve
namespace Ldgr36Si
end ModularCurve.Ldgr36Si
namespace ModularCurve
namespace Lg37
end ModularCurve.Lg37
namespace ModularCurve
namespace Mp72a102T3
end ModularCurve.Mp72a102T3
namespace Modularity
namespace Ldgr26CorrectedRowsBandSlice
end Modularity.Ldgr26CorrectedRowsBandSlice
namespace Modularity
namespace Ldgr27TraceSemilinearSlice
end Modularity.Ldgr27TraceSemilinearSlice
namespace Module
end Module
namespace MonoidWithZeroHom
end MonoidWithZeroHom
namespace Mp72a102T1
end Mp72a102T1
namespace Mp72a102T2
end Mp72a102T2
namespace Mp72a103T2
end Mp72a103T2
namespace Multiplicative
end Multiplicative
namespace NeronModelInfra
end NeronModelInfra
namespace NeronOggShafarevich
end NeronOggShafarevich
namespace NumberField
end NumberField
namespace Order
end Order
namespace PadicInt
end PadicInt
namespace Pointwise
end Pointwise
namespace Polynomial
end Polynomial
namespace RationalFunctionField
end RationalFunctionField
namespace Submodule
end Submodule
namespace TensorProduct
end TensorProduct
namespace Topology
end Topology
namespace WithZero
end WithZero

open ModularCurve.KwF4R1V394a ModularCurve.KwTateRR3 ModularCurve.KwNo6HrouteR ModularCurve.KwOdaDHDR

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateFactoring

end ModularCurve.KwF4gRRTate

end

end

end

section
section

noncomputable section


namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor

variable {K F}

end Divisor

namespace Pic0

variable {K F}

end Pic0

namespace Place


variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor


variable {K F}

end Divisor

namespace Pic0


variable {K F}

end Pic0

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section


namespace AlgebraicCurve

namespace Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (w : Place K F')

variable [Algebra.IsIntegral F F']

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

end RestrictDef

end Restrict

end Place

end AlgebraicCurve

end
end

end

section
section



namespace MazurTorsion

section Henselian

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (v : IsDedekindDomain.HeightOneSpectrum A)

theorem isClosed_setOf_valued_le (γ : ℤᵐ⁰) :
    IsClosed {x : v.adicCompletion K | Valued.v x ≤ γ} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have h := Valued.isClosed_closedBall (R := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)
    ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict z)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_le_iff, hz]


scoped instance instIsAdicCompleteCompletionIdealAdicCompletionIntegers :
    IsAdicComplete (v.completionIdeal K) (v.adicCompletionIntegers K) where
  haus' x hx := by
    have hx' : ∀ n : ℕ, Valued.v x.val ≤ WithZero.exp (-(n : ℤ)) := by
      intro n
      have h := hx n
      simp only [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.zero,
        mem_completionIdeal_pow] at h
      exact h
    by_contra hx0
    have hxne : x.val ≠ (0 : v.adicCompletion K) := fun h => hx0 (Subtype.ext h)
    have hvne : Valued.v x.val ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).mpr hxne
    obtain ⟨k, hk⟩ := exists_ofAdd_natCast_lt hvne
    exact absurd (hx' k) (not_le.mpr hk)
  prec' f hf := by
    classical

    have hf' : ∀ m n : ℕ, m ≤ n →
        Valued.v ((f m - f n : v.adicCompletionIntegers K)).val ≤ WithZero.exp (-(m : ℤ)) := by
      intro m n hmn
      have h := hf hmn
      simp only [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
        mem_completionIdeal_pow] at h
      exact h

    have hcoe : ∀ a b : ℕ, ((f a - f b : v.adicCompletionIntegers K)).val
        = (f a).val - (f b).val := fun a b => rfl

    have hcauchy : CauchySeq (fun n => (f n).val : ℕ → v.adicCompletion K) := by
      rw [(Valued.hasBasis_uniformity (v.adicCompletion K) ℤᵐ⁰).cauchySeq_iff]
      rintro γ -
      have hγ0 : (ValueGroup₀.embedding γ.val : ℤᵐ⁰) ≠ 0 := by
        intro h0
        exact γ.ne_zero (ValueGroup₀.embedding_strictMono.injective
          (h0.trans (_root_.map_zero _).symm))
      obtain ⟨k, hk⟩ := exists_ofAdd_natCast_lt hγ0
      refine ⟨k, fun m hm n hn => ?_⟩
      have key : ∀ a b : ℕ, k ≤ a → a ≤ b →
          Valued.v ((f b).val - (f a).val) < ValueGroup₀.embedding γ.val := by
        intro a b hka hab
        have h1 : Valued.v ((f b).val - (f a).val) ≤ WithZero.exp (-(a : ℤ)) := by
          rw [Valuation.map_sub_swap, ← hcoe a b]
          exact hf' a b hab
        have h2 : WithZero.exp (-(a : ℤ)) ≤ WithZero.exp (-(k : ℤ)) := by
          rw [WithZero.exp_le_exp]
          omega
        exact lt_of_le_of_lt (h1.trans h2) hk
      show ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
        ((f n).val - (f m).val)) < γ.val
      rw [Valuation.restrict_lt_iff_lt_embedding]
      rcases le_total m n with hmn | hnm
      · exact key m n hm hmn
      · rw [Valuation.map_sub_swap]
        exact key n m hn hnm

    obtain ⟨L₀, hL₀⟩ := cauchySeq_tendsto_of_complete hcauchy

    have hbound : ∀ n : ℕ, Valued.v (L₀ - (f n).val) ≤ WithZero.exp (-(n : ℤ)) := by
      intro n
      have hclosed : IsClosed {y : v.adicCompletion K |
          Valued.v (y - (f n).val) ≤ WithZero.exp (-(n : ℤ))} := by
        have hpre : {y : v.adicCompletion K |
            Valued.v (y - (f n).val) ≤ WithZero.exp (-(n : ℤ))}
              = (fun y => y - (f n).val) ⁻¹'
                {z : v.adicCompletion K | Valued.v z ≤ WithZero.exp (-(n : ℤ))} := rfl
        rw [hpre]
        exact (isClosed_setOf_valued_le K v _).preimage (continuous_sub_right ((f n).val))
      have hev : ∀ᶠ m in Filter.atTop, (f m).val ∈ {y : v.adicCompletion K |
          Valued.v (y - (f n).val) ≤ WithZero.exp (-(n : ℤ))} := by
        refine Filter.eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
        have h := hf' n m hm
        rw [hcoe n m] at h
        rw [Set.mem_ofPred_eq, Valuation.map_sub_swap]
        exact h
      exact hclosed.mem_of_tendsto hL₀ hev

    have hL₀mem : L₀ ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers]
      have h0 : Valued.v (L₀ - (f 0).val) ≤ (1 : ℤᵐ⁰) := by
        have h := hbound 0
        simpa using h
      have h1 : Valued.v ((f 0).val) ≤ (1 : ℤᵐ⁰) := (f 0).2
      have hmax : Valued.v ((L₀ - (f 0).val) + (f 0).val) ≤ (1 : ℤᵐ⁰) :=
        Valuation.map_add_le _ h0 h1
      have hL : (L₀ - (f 0).val) + (f 0).val = L₀ := by ring
      rwa [hL] at hmax

    refine ⟨⟨L₀, hL₀mem⟩, fun n => ?_⟩
    have h : Valued.v ((f n).val - L₀) ≤ WithZero.exp (-(n : ℤ)) := by
      rw [Valuation.map_sub_swap]
      exact hbound n
    simp only [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      mem_completionIdeal_pow]
    have hsub : ((f n - (⟨L₀, hL₀mem⟩ : v.adicCompletionIntegers K) :
        v.adicCompletionIntegers K)).val = (f n).val - L₀ := rfl
    rw [hsub]
    exact h

end Henselian

section Uniformizer

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (v : IsDedekindDomain.HeightOneSpectrum A)

end Uniformizer

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

end DVR

section Cover

end Cover

section Consequences

end Consequences

section PadicGate

end PadicGate

end MazurTorsion

end

end

section
section


noncomputable section


namespace AlgebraicCurve
namespace Place

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end AdicCompletion

section Henselian

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

open scoped MazurTorsion

scoped instance kw_ffgc_isAdicComplete_placeAdicCompletionIntegers :
    IsAdicComplete (maximalIdeal V.adicCompletionIntegers) V.adicCompletionIntegers :=
  inferInstance

end Henselian

section WithValLevel

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end WithValLevel

section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionComap

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end Bridge

end AlgebraicCurve.Place

end
end

end

section
section

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

noncomputable section


namespace ModularCurve
namespace Lg37


section CompletionCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CompletionCarrier

section Inhabitant

end Inhabitant

section Stratum

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]

end Stratum

section MovedCarrier

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
variable [HasCanonicalLocalResidueKStar K F']

end MovedCarrier

section CommittedPlace

end CommittedPlace

end ModularCurve.Lg37

section AxiomAudit

end AxiomAudit

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

noncomputable section



namespace Mp72a103T2


section Calculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a103_t2_evalDepth_pow_uniformizer_mul_eq_zero (v : Place K F) :
    ∀ (m : ℕ) (z : lg37_completion v),
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) m
        (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ m * z) = 0 := by
  intro m
  induction m with
  | zero => intro z; exact mp72a102_t3_evalₐ_zero_depth _ _
  | succ m ih =>
    intro z
    have hkill := mp72a102_t3_evalₐ_succ_mul_eq_zero
      (maximalIdeal v.toValuationSubring) v.uniformizerSubring_mem_maximalIdeal (ih z)
    have hgoal : algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring ^ (m + 1) * z
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ m * z) := by
      rw [pow_succ', mul_assoc]
    rw [hgoal]
    exact hkill

end Calculus

section NumeratorBand

variable {K : Type*} [Field K] [CharZero K]

end NumeratorBand

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction

end Mp72a103T2

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

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]


theorem kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers (v : Place K E)
    {xh : v.adicCompletion} (hxh : xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = 0 := by
  rw [kwHgfV352_localResidueCompletion_spec v xh (x := 0)
    (by rw [_root_.map_zero, zero_sub]; exact neg_mem hxh)]
  exact _root_.map_zero _

theorem kwHgfV352_localResidueCompletion_add (v : Place K E)
    (xh yh : v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (xh + yh)
      = kwHgfV352_localResidueCompletion v xh
        + kwHgfV352_localResidueCompletion v yh := by
  obtain ⟨x, hx⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh
  obtain ⟨y, hy⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v yh
  have heq : algebraMap E v.adicCompletion (x + y) - (xh + yh)
      = (algebraMap E v.adicCompletion x - xh) + (algebraMap E v.adicCompletion y - yh) := by
    rw [map_add]; ring
  rw [kwHgfV352_localResidueCompletion_spec v xh hx,
    kwHgfV352_localResidueCompletion_spec v yh hy,
    kwHgfV352_localResidueCompletion_spec v (xh + yh) (x := x + y)
      (heq ▸ add_mem hx hy),
    map_add]

end LocalResidueCompletion

section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

end CompletionTraceAt

section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end MPGKPowBasisLocalMint

section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end CompletionTraceSumMint

section EffBaseDescentMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end EffBaseDescentMint

section MainReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F] [FiniteDimensional E F]

end MainReduction

end AlgebraicCurve

end
end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [HasCanonicalLocalResidueKStar K L]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end TateAtoms

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section PoleWindow

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end PoleWindow

end ModularCurve.KwF4gRRTate

end

end

end

section
section



namespace IsDedekindDomain
namespace HeightOneSpectrum

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

namespace adicCompletion

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum

section AxiomAudit


end AxiomAudit

end

end

section
section

set_option linter.unusedSectionVars false

noncomputable section


namespace ModularCurve
namespace KwF4R1V410a

theorem kwF4R1V410a_factorPow_evalₐ {R : Type*} [CommRing R] {I : Ideal R}
    {m n : ℕ} (hle : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n z)
      = AdicCompletion.evalₐ I m z := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I z (n := n) (le_of_eq (Ideal.mul_top _)),
    ← AdicCompletion.factor_eval_eq_evalₐ I z (n := m) (le_of_eq (Ideal.mul_top _)),
    AdicCompletion.eval_apply, AdicCompletion.eval_apply, ← z.prop hle]

  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
  rw [← hx]; rfl

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring
local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring
local notation "O_W" => w.adicCompletionIntegers
local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

theorem kwF4R1V410a_quotientEquiv_factorPow {m n : ℕ} (hle : m ≤ n)
    (z : (O_w) ⧸ (𝔪_w) ^ n) :
    Ideal.Quotient.factorPow (𝔪_W) hle (kwF4R1V410a_quotientEquiv w n z)
      = kwF4R1V410a_quotientEquiv w m (Ideal.Quotient.factorPow (𝔪_w) hle z) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [kwF4R1V410a_quotientEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    kwF4R1V410a_quotientEquiv_mk]

def kwF4R1V410a_forwardFamily (n : ℕ) :
    lg37_completion w →+* (O_W) ⧸ (𝔪_W)^n :=
  RingHom.comp ((kwF4R1V410a_quotientEquiv w n).toRingHom)
    ((AdicCompletion.evalₐ (𝔪_w) n).toRingHom)

theorem kwF4R1V410a_forwardFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (𝔪_W) hle).comp (kwF4R1V410a_forwardFamily w n)
      = kwF4R1V410a_forwardFamily w m := by
  refine RingHom.ext fun z => ?_
  show Ideal.Quotient.factorPow (𝔪_W) hle
      (kwF4R1V410a_quotientEquiv w n (AdicCompletion.evalₐ (𝔪_w) n z))
    = kwF4R1V410a_quotientEquiv w m (AdicCompletion.evalₐ (𝔪_w) m z)
  rw [kwF4R1V410a_quotientEquiv_factorPow w hle, kwF4R1V410a_factorPow_evalₐ hle z]

def kwF4R1V410a_forward : lg37_completion w →+* (O_W) :=
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  IsAdicComplete.liftRingHom (𝔪_W) (kwF4R1V410a_forwardFamily w)
    (kwF4R1V410a_forwardFamily_compat w)

theorem kwF4R1V410a_mk_forward (n : ℕ) (z : lg37_completion w) :
    Ideal.Quotient.mk ((𝔪_W)^n) (kwF4R1V410a_forward w z)
      = kwF4R1V410a_quotientEquiv w n (AdicCompletion.evalₐ (𝔪_w) n z) := by
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  exact IsAdicComplete.mk_liftRingHom (𝔪_W) (kwF4R1V410a_forwardFamily w)
    (kwF4R1V410a_forwardFamily_compat w) n z

def kwF4R1V410a_backwardFamily (n : ℕ) : (O_W) →+* (O_w) ⧸ (𝔪_w)^n :=
  RingHom.comp ((kwF4R1V410a_quotientEquiv w n).symm.toRingHom)
    (Ideal.Quotient.mk ((𝔪_W)^n))

theorem kwF4R1V410a_backwardFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (𝔪_w) hle).comp (kwF4R1V410a_backwardFamily w n)
      = kwF4R1V410a_backwardFamily w m := by
  refine RingHom.ext fun y => ?_
  show Ideal.Quotient.factorPow (𝔪_w) hle
      ((kwF4R1V410a_quotientEquiv w n).symm (Ideal.Quotient.mk ((𝔪_W)^n) y))
    = (kwF4R1V410a_quotientEquiv w m).symm (Ideal.Quotient.mk ((𝔪_W)^m) y)
  apply (kwF4R1V410a_quotientEquiv w m).injective
  rw [RingEquiv.apply_symm_apply, ← kwF4R1V410a_quotientEquiv_factorPow w hle,
    RingEquiv.apply_symm_apply, Ideal.Quotient.factor_mk]

def kwF4R1V410a_backward : (O_W) →+* lg37_completion w :=
  AdicCompletion.liftRingHom (𝔪_w) (kwF4R1V410a_backwardFamily w)
    (kwF4R1V410a_backwardFamily_compat w)

theorem kwF4R1V410a_evalₐ_backward (n : ℕ) (y : O_W) :
    AdicCompletion.evalₐ (𝔪_w) n (kwF4R1V410a_backward w y)
      = (kwF4R1V410a_quotientEquiv w n).symm (Ideal.Quotient.mk ((𝔪_W)^n) y) :=
  AdicCompletion.evalₐ_liftRingHom (𝔪_w) (kwF4R1V410a_backwardFamily w)
    (kwF4R1V410a_backwardFamily_compat w) n y

theorem kwF4R1V410a_forward_backward :
    (kwF4R1V410a_forward w).comp (kwF4R1V410a_backward w) = RingHom.id _ := by
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  have hfun : (fun y => kwF4R1V410a_forward w (kwF4R1V410a_backward w y))
      = _root_.id := IsHausdorff.funext' (𝔪_W) (fun n y => by
    rw [kwF4R1V410a_mk_forward, kwF4R1V410a_evalₐ_backward,
      RingEquiv.apply_symm_apply, _root_.id])
  exact RingHom.ext (fun y => congrFun hfun y)

theorem kwF4R1V410a_backward_forward :
    (kwF4R1V410a_backward w).comp (kwF4R1V410a_forward w) = RingHom.id _ := by
  refine RingHom.ext (fun z => AdicCompletion.ext_evalₐ (fun n => ?_))
  rw [RingHom.comp_apply, kwF4R1V410a_evalₐ_backward, kwF4R1V410a_mk_forward,
    RingEquiv.symm_apply_apply, RingHom.id_apply]

def kwF4R1V410a_ringEquiv : lg37_completion w ≃+* (O_W) :=
  RingEquiv.ofRingHom (kwF4R1V410a_forward w) (kwF4R1V410a_backward w)
    (kwF4R1V410a_forward_backward w) (kwF4R1V410a_backward_forward w)

theorem kwF4R1V410a_ringEquiv_apply (z : lg37_completion w) :
    kwF4R1V410a_ringEquiv w z = kwF4R1V410a_forward w z := rfl

theorem kwF4R1V410a_ringEquiv_of (x : O_w) :
    kwF4R1V410a_ringEquiv w (algebraMap (O_w) (lg37_completion w) x)
      = algebraMap (O_w) (O_W) x := by
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  have hfun : (fun x => kwF4R1V410a_ringEquiv w
        (algebraMap (O_w) (lg37_completion w) x))
      = algebraMap (O_w) (O_W) := IsHausdorff.funext' (𝔪_W) (fun n x => by
    rw [kwF4R1V410a_ringEquiv_apply, kwF4R1V410a_mk_forward,
      show algebraMap (O_w) (lg37_completion w) x
        = AdicCompletion.of (𝔪_w) (O_w) x from rfl,
      AdicCompletion.evalₐ_of, kwF4R1V410a_quotientEquiv_mk])
  exact congrFun hfun x

end Bridge

end ModularCurve.KwF4R1V410a

end
end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end PoleWindowShift

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section AgreementReduce

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end AgreementReduce

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section FinrankTraceCyclicity

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

end FinrankTraceCyclicity

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section DeltaLemmas

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (pA pA' : V →ₗ[K] V)

variable {pA pA'}

end DeltaLemmas

section Mint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

end Mint

section DiffComputation

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

end DiffComputation

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section TraceOnSuperspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TraceOnSuperspace

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end Additivity

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section DVRQuotDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end DVRQuotDischarge

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section DVRCotangentDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end DVRCotangentDischarge

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section DeltaQuotFactor

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {pA pA' : V →ₗ[K] V}

end DeltaQuotFactor

section TermRangeFinite

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

end TermRangeFinite

section DiffTraceZero

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

end DiffTraceZero

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section Composite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

end Composite

section Subset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end Subset

section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

end Discharge

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section KerInf

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

end KerInf

section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)
variable [∀ u : Place K L, u.FiniteResidue]

end Discharge

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end Additivity

section ConjInvariance

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]

end ConjInvariance

section TermMaps

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

variable [u.FiniteResidue]

end TermMaps

section Cyclicity

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]
variable {pA' : u.adicCompletion →ₗ[K] u.adicCompletion}

end Cyclicity

section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [∀ u : Place K L, u.FiniteResidue]

end Headline

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end Additivity

section TateCommAddFst

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateCommAddFst

section TateResAddFst

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResAddFst

section CohenMint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateCohenTateAgreement : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue],
    ∃ (pC : u.adicCompletion →ₗ[K] u.adicCompletion)
      (hpC : SameRangeIdemProjectors (tateProj u) pC),
    ∀ (fh : u.adicCompletion)
      [FiniteDimensional K (LinearMap.range
        (tateCommRestrict pC (lmulK u fh)
          (lmulK u (algebraMap L u.adicCompletion u.uniformizer))))],
    tateCommTrace pC (lmulK u fh) (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

end CohenMint

section Reprice

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable [∀ u : Place K L, u.FiniteResidue]

theorem kwF4gRRTate_agreement_of_cohenTateAgreement
    (hfin : KwF4gRRTateCommFinite K L)
    (hCTA : KwF4gRRTateCohenTateAgreement K L) :
    KwF4gRRTateAgreement K L hfin := by
  intro u _ fh
  obtain ⟨pC, hpC, hCTA_u⟩ := hCTA u
  set ghπ := algebraMap L u.adicCompletion u.uniformizer
  have hgh : ghπ ∈ u.adicCompletionIntegers :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr u.uniformizer_mem
  haveI hF1 := hfin u fh ghπ
  haveI hF2 : FiniteDimensional K (LinearMap.range
      (tateCommRestrict pC (lmulK u fh) (lmulK u ghπ))) :=
    kwF4gRRTate_commFiniteGen u pC hpC fh ghπ

  show tateRes u fh ghπ = Algebra.trace K u.ResidueField
    (kwHgfV352_localResidueCompletion u fh)
  unfold tateRes
  rw [kwF4gRRTate_projectorIndep u pC hpC fh ghπ hgh]
  exact hCTA_u fh

end Reprice

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwF4gRRTate

section CohenKernelData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

structure TateCohenKernelData (u : Place K L) [u.FiniteResidue] where

  pC : u.adicCompletion →ₗ[K] u.adicCompletion

  pC_idem : ∀ x, pC (pC x) = pC x

  range_pC : LinearMap.range (tateProj u) = LinearMap.range pC

  liftκ : u.ResidueField →ₗ[K] LinearMap.range pC

  liftκ_inj : Function.Injective liftκ

  tateComm_mem_range_liftκ : ∀ (fh : u.adicCompletion) (a : LinearMap.range pC),
    tateCommRestrict pC (lmulK u fh)
      (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) a ∈ LinearMap.range liftκ

  tateComm_liftκ : ∀ (fh : u.adicCompletion) (c : u.ResidueField),
    tateCommRestrict pC (lmulK u fh)
      (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) (liftκ c)
      = liftκ (kwHgfV352_localResidueCompletion u fh * c)

variable {u : Place K L} [u.FiniteResidue]

theorem sameRangeIdemProjectors_of_kernelData (D : TateCohenKernelData u) :
    SameRangeIdemProjectors (tateProj u) D.pC where
  idem_pA x := congrFun (congrArg DFunLike.coe (tateProj_idem u)) x
  idem_pA' := D.pC_idem
  range_eq := D.range_pC

end CohenKernelData

section TraceComputation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable {u : Place K L} [u.FiniteResidue]

theorem tateCommTrace_of_kernelData (D : TateCohenKernelData u) (fh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict D.pC (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer))))] :
    tateCommTrace D.pC (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh) := by
  haveI : FiniteDimensional K u.ResidueField := Place.FiniteResidue.finite
  set T := tateCommRestrict D.pC (lmulK u fh)
    (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) with hT
  set W : Submodule K (LinearMap.range D.pC) := LinearMap.range D.liftκ with hW
  haveI hWfin : FiniteDimensional K W := LinearMap.finiteDimensional_range D.liftκ

  have hrange : LinearMap.range T ≤ W := by
    rintro x ⟨a, rfl⟩; exact D.tateComm_mem_range_liftκ fh a

  have hstab : ∀ x ∈ W, T x ∈ W := by
    rintro x ⟨c, rfl⟩
    exact ⟨kwHgfV352_localResidueCompletion u fh * c, (D.tateComm_liftκ fh c).symm⟩

  let e : u.ResidueField ≃ₗ[K] W := LinearEquiv.ofInjective D.liftκ D.liftκ_inj
  have he_apply : ∀ c, ((e c : W) : LinearMap.range D.pC) = D.liftκ c := fun c => rfl

  have hconj : T.restrict hstab
      = e.conj (Algebra.lmul K u.ResidueField
          (kwHgfV352_localResidueCompletion u fh)) := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨c, rfl⟩ := e.surjective w
    apply Subtype.ext
    calc ((T.restrict hstab) (e c) : LinearMap.range D.pC)
        = T ((e c : W) : LinearMap.range D.pC) := rfl
      _ = T (D.liftκ c) := by rw [he_apply]
      _ = D.liftκ (kwHgfV352_localResidueCompletion u fh * c) := D.tateComm_liftκ fh c
      _ = ((e (kwHgfV352_localResidueCompletion u fh * c) : W) : LinearMap.range D.pC) :=
            (he_apply _).symm
      _ = (((e.conj (Algebra.lmul K u.ResidueField
              (kwHgfV352_localResidueCompletion u fh))) (e c) : W)
              : LinearMap.range D.pC) := by
            congr 1
            rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
              LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
            rfl

  calc tateCommTrace D.pC (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = finrankTrace T := rfl
    _ = LinearMap.trace K W (T.restrict hstab) :=
          finrankTrace_eq_trace_on_superspace T W hrange hstab
    _ = LinearMap.trace K W (e.conj (Algebra.lmul K u.ResidueField
          (kwHgfV352_localResidueCompletion u fh))) := by rw [hconj]
    _ = LinearMap.trace K u.ResidueField (Algebra.lmul K u.ResidueField
          (kwHgfV352_localResidueCompletion u fh)) :=
          LinearMap.trace_conj' (N := ↥W) (Algebra.lmul K u.ResidueField (kwHgfV352_localResidueCompletion u fh)) e
    _ = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh) := rfl

end TraceComputation

section Mint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateCohenKernelDataExists : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue], Nonempty (TateCohenKernelData u)

end Mint

section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

theorem kwF4gRRTate_cohenTateAgreement_of_kernelData
    (hD : KwF4gRRTateCohenKernelDataExists K L) :
    KwF4gRRTateCohenTateAgreement K L := by
  intro u _
  obtain ⟨D⟩ := hD u
  exact ⟨D.pC, sameRangeIdemProjectors_of_kernelData D,
    fun fh _ => tateCommTrace_of_kernelData D fh⟩

theorem kwF4gRRTate_agreement_of_kernelData
    [∀ u : Place K L, u.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K L)
    (hD : KwF4gRRTateCohenKernelDataExists K L) :
    KwF4gRRTateAgreement K L hfin :=
  kwF4gRRTate_agreement_of_cohenTateAgreement hfin
    (kwF4gRRTate_cohenTateAgreement_of_kernelData hD)

end Headline

end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option linter.unusedSectionVars false

open ModularCurve.GF24a9RRDx

noncomputable section

namespace ModularCurve
namespace KwF4R1V394a

section LinearWrappers

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]]

theorem kwF4R1V394a_localResidueCompletion_smul
    (v : Place K E) (c : K) (xh : v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (c • xh)
      = c • kwHgfV352_localResidueCompletion v xh := by
  obtain ⟨x, hx⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh

  have halg : algebraMap E v.adicCompletion (c • x)
      = c • algebraMap E v.adicCompletion x := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K E v.adicCompletion,
      ← Algebra.smul_def]
  have hcx : algebraMap E v.adicCompletion (c • x) - c • xh
      ∈ v.adicCompletionIntegers := by
    rw [halg, ← smul_sub, Algebra.smul_def,
      IsScalarTower.algebraMap_apply K E v.adicCompletion c]
    refine mul_mem ?_ hx

    exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mpr
      (v.algebraMap_mem' c)
  rw [AlgebraicCurve.kwHgfV352_localResidueCompletion_spec v _ hcx,
    AlgebraicCurve.kwHgfV352_localResidueCompletion_spec v _ hx, map_smul]

end LinearWrappers

section OrdCompat

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

variable {K F E}
variable [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]]

end OrdCompat

section Recursion

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]]

variable [Nontrivial Ω[F⁄K]]

end Recursion

section MonomialMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end MonomialMint

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Engine

end ModularCurve.KwF4R1V394a

end
end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwTateRR3

section CohenSectionHat

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def cohenSectionHat (u : Place K L) (S : Lg37CompletionSection u) :
    u.ResidueField →ₐ[K] u.adicCompletion where
  toRingHom :=
    (u.adicCompletionIntegers.subtype).comp
      ((kwF4R1V410a_ringEquiv u).toRingHom.comp S.lift.toRingHom)
  commutes' c := by
    show ((kwF4R1V410a_ringEquiv u (S.lift (algebraMap K u.ResidueField c))
        : u.adicCompletionIntegers) : u.adicCompletion)
      = algebraMap K u.adicCompletion c
    rw [S.lift.commutes c,
      IsScalarTower.algebraMap_apply K u.toValuationSubring (lg37_completion u) c,
      kwF4R1V410a_ringEquiv_of u,
      IsScalarTower.algebraMap_apply K L u.adicCompletion c]
    rfl

theorem cohenSectionHat_apply (u : Place K L) (S : Lg37CompletionSection u)
    (a : u.ResidueField) :
    cohenSectionHat u S a
      = ((kwF4R1V410a_ringEquiv u (S.lift a) : u.adicCompletionIntegers)
          : u.adicCompletion) := rfl

theorem cohenSectionHat_mem_integers (u : Place K L) (S : Lg37CompletionSection u)
    (a : u.ResidueField) :
    cohenSectionHat u S a ∈ u.adicCompletionIntegers :=
  (kwF4R1V410a_ringEquiv u (S.lift a)).2

theorem cohenSectionHat_mem_adicIntegersKSubmod (u : Place K L)
    (S : Lg37CompletionSection u) (a : u.ResidueField) :
    cohenSectionHat u S a ∈ adicIntegersKSubmod u :=
  cohenSectionHat_mem_integers u S a

theorem cohenSectionHat_injective (u : Place K L) (S : Lg37CompletionSection u) :
    Function.Injective (cohenSectionHat u S) :=
  (cohenSectionHat u S).toRingHom.injective

end CohenSectionHat

section CohenProjC

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def cohenProjC (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) :
    u.adicCompletion →ₗ[K] u.adicCompletion :=
  (adicIntegersKSubmod u).subtype ∘ₗ Submodule.projectionOnto (adicIntegersKSubmod u) B hcompl

theorem cohenProjC_mem_integers (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) (x : u.adicCompletion) :
    cohenProjC u B hcompl x ∈ u.adicCompletionIntegers :=
  (Submodule.projectionOnto (adicIntegersKSubmod u) B hcompl x).2

theorem cohenProjC_of_mem (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) {x : u.adicCompletion}
    (hx : x ∈ u.adicCompletionIntegers) :
    cohenProjC u B hcompl x = x :=
  congrArg Subtype.val (Submodule.projectionOnto_apply_left hcompl ⟨x, hx⟩)

theorem cohenProjC_of_mem_B (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) {x : u.adicCompletion}
    (hx : x ∈ B) :
    cohenProjC u B hcompl x = 0 :=
  congrArg Subtype.val (Submodule.projectionOnto_apply_right hcompl ⟨x, hx⟩)

theorem cohenProjC_idem (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) (x : u.adicCompletion) :
    cohenProjC u B hcompl (cohenProjC u B hcompl x) = cohenProjC u B hcompl x :=
  cohenProjC_of_mem u B hcompl (cohenProjC_mem_integers u B hcompl x)

theorem range_cohenProjC (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) :
    LinearMap.range (cohenProjC u B hcompl) = adicIntegersKSubmod u :=
  le_antisymm (fun x ⟨y, hy⟩ => hy ▸ cohenProjC_mem_integers u B hcompl y)
    (fun x hx => ⟨x, cohenProjC_of_mem u B hcompl hx⟩)

theorem sub_cohenProjC_mem_B (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) (x : u.adicCompletion) :
    x - cohenProjC u B hcompl x ∈ B := by
  have htop : x ∈ adicIntegersKSubmod u ⊔ B := by
    rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
  subst hab
  rw [map_add, cohenProjC_of_mem u B hcompl ha,
    cohenProjC_of_mem_B u B hcompl hb, add_zero, add_sub_cancel_left]
  exact hb

end CohenProjC

section SingleTerm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (B : Submodule K u.adicCompletion) (hcompl : IsCompl (adicIntegersKSubmod u) B)

theorem cohenTateCommRestrict_single_term (fh : u.adicCompletion)
    (a : LinearMap.range (cohenProjC u B hcompl)) :
    (tateCommRestrict (cohenProjC u B hcompl) (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) a
      : u.adicCompletion)
    = cohenProjC u B hcompl
        (algebraMap L u.adicCompletion u.uniformizer
          * (fh * (a : u.adicCompletion)
              - cohenProjC u B hcompl (fh * (a : u.adicCompletion)))) := by
  have haInt : (a : u.adicCompletion) ∈ u.adicCompletionIntegers :=
    (range_cohenProjC u B hcompl ▸ a.2 :
      (a : u.adicCompletion) ∈ adicIntegersKSubmod u)
  have hπ : algebraMap L u.adicCompletion u.uniformizer ∈ u.adicCompletionIntegers :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr u.uniformizer_mem
  have hcomm : lmulK u fh ∘ₗ lmulK u (algebraMap L u.adicCompletion u.uniformizer)
      = lmulK u (algebraMap L u.adicCompletion u.uniformizer) ∘ₗ lmulK u fh := by
    refine LinearMap.ext fun x => ?_
    show fh * (algebraMap L u.adicCompletion u.uniformizer * x) =
      algebraMap L u.adicCompletion u.uniformizer * (fh * x)
    ring
  rw [tateCommRestrict_apply, tateComm_eq_of_commute hcomm]

  show cohenProjC u B hcompl (_ * (fh * ↑a - cohenProjC u B hcompl (fh * ↑a)))
      - cohenProjC u B hcompl (fh * (_ * ↑a - cohenProjC u B hcompl (_ * ↑a)))
    = cohenProjC u B hcompl (_ * (fh * ↑a - cohenProjC u B hcompl (fh * ↑a)))
  rw [cohenProjC_of_mem u B hcompl (mul_mem hπ haInt), sub_self, mul_zero, _root_.map_zero, sub_zero]

end SingleTerm

section CohenLaurentSpec

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

structure KwTateRR3CohenLaurentSpec (u : Place K L) [u.FiniteResidue] where

  S : Lg37CompletionSection u

  B : Submodule K u.adicCompletion

  hcompl : IsCompl (adicIntegersKSubmod u) B

  ε : B →ₗ[K] u.ResidueField

  shift_sub_mem : ∀ z : B,
    algebraMap L u.adicCompletion u.uniformizer * (z : u.adicCompletion)
      - cohenSectionHat u S (ε z) ∈ B

  ε_principalPart_mul_sectionHat : ∀ (fh : u.adicCompletion) (c : u.ResidueField),
    ε ⟨fh * cohenSectionHat u S c
          - cohenProjC u B hcompl (fh * cohenSectionHat u S c),
        sub_cohenProjC_mem_B u B hcompl _⟩
      = kwHgfV352_localResidueCompletion u fh * c

variable {u : Place K L} [u.FiniteResidue] (D : KwTateRR3CohenLaurentSpec u)

theorem cohenProjC_uniformizer_mul_of_mem_B {x : u.adicCompletion} (hx : x ∈ D.B) :
    cohenProjC u D.B D.hcompl
        (algebraMap L u.adicCompletion u.uniformizer * x)
      = cohenSectionHat u D.S (D.ε ⟨x, hx⟩) := by
  have hsplit : algebraMap L u.adicCompletion u.uniformizer * x
      = cohenSectionHat u D.S (D.ε ⟨x, hx⟩)
        + (algebraMap L u.adicCompletion u.uniformizer * x
            - cohenSectionHat u D.S (D.ε ⟨x, hx⟩)) := (add_sub_cancel _ _).symm
  rw [hsplit, map_add, cohenProjC_of_mem u D.B D.hcompl
      (cohenSectionHat_mem_integers u D.S _),
    cohenProjC_of_mem_B u D.B D.hcompl (D.shift_sub_mem ⟨x, hx⟩), add_zero]

end CohenLaurentSpec

section Construct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable {u : Place K L} [u.FiniteResidue]

def cohenLiftκ (D : KwTateRR3CohenLaurentSpec u) :
    u.ResidueField →ₗ[K] LinearMap.range (cohenProjC u D.B D.hcompl) where
  toFun c := ⟨cohenSectionHat u D.S c,
    (range_cohenProjC u D.B D.hcompl).symm ▸
      cohenSectionHat_mem_adicIntegersKSubmod u D.S c⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' r a := Subtype.ext ((cohenSectionHat u D.S).toLinearMap.map_smul r a)

theorem cohenLiftκ_coe (D : KwTateRR3CohenLaurentSpec u) (c : u.ResidueField) :
    ((cohenLiftκ D c : LinearMap.range (cohenProjC u D.B D.hcompl)) : u.adicCompletion)
      = cohenSectionHat u D.S c := rfl

theorem cohenLiftκ_injective (D : KwTateRR3CohenLaurentSpec u) :
    Function.Injective (cohenLiftκ D) := by
  intro a b hab
  have hval : cohenSectionHat u D.S a = cohenSectionHat u D.S b :=
    (cohenLiftκ_coe D a).symm.trans
      ((congrArg Subtype.val hab).trans (cohenLiftκ_coe D b))
  exact cohenSectionHat_injective u D.S hval

def tateCohenKernelData_of_cohenLaurentSpec (D : KwTateRR3CohenLaurentSpec u) :
    TateCohenKernelData u where
  pC := cohenProjC u D.B D.hcompl
  pC_idem := cohenProjC_idem u D.B D.hcompl
  range_pC := (range_tateProj u).trans (range_cohenProjC u D.B D.hcompl).symm
  liftκ := cohenLiftκ D
  liftκ_inj := cohenLiftκ_injective D
  tateComm_mem_range_liftκ fh a := by

    have hmem := sub_cohenProjC_mem_B u D.B D.hcompl (fh * (a : u.adicCompletion))
    refine ⟨D.ε ⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    rw [cohenLiftκ_coe, cohenTateCommRestrict_single_term u D.B D.hcompl fh a,
      cohenProjC_uniformizer_mul_of_mem_B D hmem]
  tateComm_liftκ fh c := by
    apply Subtype.ext
    have hmem := sub_cohenProjC_mem_B u D.B D.hcompl (fh * cohenSectionHat u D.S c)
    rw [cohenLiftκ_coe, cohenTateCommRestrict_single_term u D.B D.hcompl fh (cohenLiftκ D c),
      cohenLiftκ_coe, cohenProjC_uniformizer_mul_of_mem_B D hmem]
    congr 1
    exact D.ε_principalPart_mul_sectionHat fh c

end Construct

section Mint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

def KwTateRR3CohenLaurentSpecExists : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue], Nonempty (KwTateRR3CohenLaurentSpec u)

end Mint

section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

theorem kwTateRR3_cohenKernelDataExists_of_cohenLaurentSpec
    (hD : KwTateRR3CohenLaurentSpecExists K L) :
    KwF4gRRTateCohenKernelDataExists K L := fun u _ =>
  (hD u).map tateCohenKernelData_of_cohenLaurentSpec

end Headline

end ModularCurve.KwTateRR3

end

end

end

section
section



noncomputable section

namespace ModularCurve
namespace KwNo6HrouteR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem aCoeff_sub (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ)
    (x y : lg37_completion v) :
    aCoeff v S m (x - y) = aCoeff v S m x - aCoeff v S m y := by
  rw [eq_sub_iff_add_eq, ← aCoeff_add, sub_add_cancel]

theorem aCoeff_uniformizerHat_pow_mul_eq_zero_of_lt (v : Place K F)
    (S : Lg37CompletionSection v) {k m : ℕ} (hk : k < m)
    (x : lg37_completion v) :
    aCoeff v S k ((algebraMap v.toValuationSubring (lg37_completion v)
      v.uniformizerSubring) ^ m * x) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show k + j + 1 = k + (j + 1) from by omega, pow_add, mul_assoc]
  have hsh := aCoeff_shift_pow v S 0 k
    ((algebraMap v.toValuationSubring (lg37_completion v)
      v.uniformizerSubring) ^ (j + 1) * x)
  rw [Nat.zero_add] at hsh
  rw [hsh, aCoeff_zero]

  show lg37_residueHat v _ = 0
  rw [pow_succ', mul_assoc, map_mul, lg37_residueHat_algebraMap,
    (IsLocalRing.residue_eq_zero_iff _).mpr v.uniformizerSubring_mem_maximalIdeal, zero_mul]

theorem taylor_choose_eq_aCoeff (v : Place K F) (S : Lg37CompletionSection v)
    (n : ℕ) (x : lg37_completion v) {k : ℕ} (hk : k < n) :
    Classical.choose (mp72a102_t3_sigma_taylor_expansion v S n x) k = aCoeff v S k x := by
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S n x)
  have hcc := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S n x)
  set cc' := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (k + 1) x) with hcc'_def
  have hcc' := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (k + 1) x)

  have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring) hk
    (x - ∑ i ∈ Finset.range n, S.lift (cc i)
      * algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring ^ i)
  rw [hcc, _root_.map_zero] at hfac
  have htail : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (k + 1)
      (∑ i ∈ Finset.Ico (k + 1) n, S.lift (cc i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Finset.mem_Ico.mp hi).1
    have heq : S.lift (cc (k + 1 + j))
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ (k + 1 + j)
        = algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ (k + 1)
          * (algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ j * S.lift (cc (k + 1 + j))) := by
      rw [pow_add]; ring
    rw [heq]
    exact Mp72a103T2.mp72a103_t2_evalDepth_pow_uniformizer_mul_eq_zero v (k + 1) _
  have hhead : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (k + 1)
      (x - ∑ i ∈ Finset.range (k + 1), S.lift (cc i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have hsplit : x - ∑ i ∈ Finset.range (k + 1), S.lift (cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i
        = (x - ∑ i ∈ Finset.range n, S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          + ∑ i ∈ Finset.Ico (k + 1) n, S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i := by
      rw [show Finset.range n = Finset.range (k + 1) ∪ Finset.Ico (k + 1) n from by
          simp only [Finset.range_eq_Ico]
          exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hk).symm,
        Finset.sum_union (by
          rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 (k + 1) n)]
      ring
    rw [hsplit, map_add, ← hfac, htail, add_zero]

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (k + 1)
      (∑ i ∈ Finset.range (k + 1), S.lift ((fun i => cc' i - cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (k + 1), S.lift (cc' i - cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = (x - ∑ i ∈ Finset.range (k + 1), S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - (x - ∑ i ∈ Finset.range (k + 1), S.lift (cc' i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hhead, hcc', sub_zero]
  have hzero := Mp72a103T2.mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (k + 1)
    (fun i => cc' i - cc i) key k (Nat.lt_succ_self k)
  have h := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hcc'_def]
  exact h

theorem exists_approximant (v : Place K F) (S : Lg37CompletionSection v)
    (a : v.ResidueField) (M : ℕ) :
    ∃ ℓ : v.toValuationSubring, IsLocalRing.residue _ ℓ = a
      ∧ ∀ k, 1 ≤ k → k ≤ M →
        aCoeff v S k (algebraMap v.toValuationSubring (lg37_completion v) ℓ) = 0 := by
  induction M with
  | zero =>
    obtain ⟨ℓ, hℓ⟩ := IsLocalRing.residue_surjective a
    exact ⟨ℓ, hℓ, fun k hk1 hk0 => absurd (hk1.trans hk0) (by omega)⟩
  | succ M ih =>
    obtain ⟨ℓ, hres, hvan⟩ := ih

    set b := aCoeff v S (M + 1)
      (algebraMap v.toValuationSubring (lg37_completion v) ℓ) with hb
    obtain ⟨n, hn⟩ := IsLocalRing.residue_surjective b
    refine ⟨ℓ - n * v.uniformizerSubring ^ (M + 1), ?_, ?_⟩
    · rw [map_sub, map_mul, map_pow, hres, sub_eq_self, mul_eq_zero]
      right
      exact pow_eq_zero_iff (by omega) |>.mpr
        ((IsLocalRing.residue_eq_zero_iff _).mpr v.uniformizerSubring_mem_maximalIdeal)
    · intro k hk1 hkM
      rw [map_sub, map_mul, map_pow, aCoeff_sub,
        mul_comm (algebraMap _ _ n) _]
      rcases Nat.lt_or_ge k (M + 1) with hk | hk
      ·
        rw [hvan k hk1 (Nat.lt_succ_iff.mp hk),
          aCoeff_uniformizerHat_pow_mul_eq_zero_of_lt v S hk, sub_zero]
      ·
        have hkeq : k = M + 1 := le_antisymm hkM hk
        subst hkeq
        rw [← hb]
        have hsh := aCoeff_shift_pow v S 0 (M + 1)
          (algebraMap v.toValuationSubring (lg37_completion v) n)
        rw [Nat.zero_add] at hsh
        rw [hsh, aCoeff_zero, lg37_residueHat_algebraMap, hn, sub_self]

section Separability

variable [HasCanonicalLocalResidueKStar K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Separability

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end ModularCurve.KwNo6HrouteR

end

end

end

section
section

open FLT.HopfSpec GoodReductionJacobian
open Deformation.PDivisible Deformation.ModpDieudonne
open NeronOggShafarevich
open AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine
open ModularCurve.KwNo6HrouteV
open ModularCurve.KwNo6HrouteY
open ModularCurve.KwNo6HrouteZ
open ModularCurve.GF24a9RRDx
open ModularCurve.GF24a12CohenSupply
open Ldgr30BankGate
open Modularity.Ldgr27TraceSemilinearSlice
open Ldgr24DefectKernelSlice
open Ldgr23CohenDefectCorrectionSlice
open ModularCurve.Ldgr25PlaceExtensionSlice
open Ldgr25CorrectedChoiceSlice
open Modularity.Ldgr26CorrectedRowsBandSlice
open ModularCurve.GF24a11bRowACurrencyBridge
open ModularCurve.GF24a12CohenSupply
open ModularCurve.Ldgr32RegularLegSlice
open ModularCurve.Ldgr31PerPlaceRowJoinSlice
open ModularCurve.Ldgr29SimplePoleResidueSlice
open ModularCurve.Ldgr25CotraceCompatSlice
open AlgebraicCurve.FiberKaehlerLocalDatum
open ModularCurve.KwNo6HrouteS
open ModularCurve.KwNo6HrouteR

noncomputable section

section

namespace ModularCurve
namespace KwOdaDHDR

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

set_option linter.unusedSectionVars false
section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kwHgf_v277_aCoeff_section_lift_mul (v : Place K F)
    (S : Lg37CompletionSection v) (m : ℕ) (a : v.ResidueField)
    (x : lg37_completion v) :
    aCoeff v S m (S.lift a * x) = a * aCoeff v S m x := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hax' := Classical.choose_spec
    (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (S.lift a * x))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
    with hax_def
  set aax := Classical.choose
    (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (S.lift a * x)) with haax_def

  have hsmul : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((S.lift a * x)
        - ∑ i ∈ Finset.range (m + 1),
            S.lift ((fun i => a * ax i) i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have e : (S.lift a * x)
          - ∑ i ∈ Finset.range (m + 1), S.lift (a * ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = S.lift a
          * (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, mul_assoc]
    rw [e, mp72a102_t3_evalDepth_mul, hx, mul_zero]

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1),
          S.lift ((fun i => a * ax i - aax i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1),
            S.lift (a * ax i - aax i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((S.lift a * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (aax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((S.lift a * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (a * ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hax', hsmul, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => a * ax i - aax i) key m (Nat.lt_succ_self m)
  have han : aax m = a * ax m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← haax_def]
  exact han

end Generic

end ModularCurve.KwOdaDHDR

end

end

end

end

section
section

open FLT.HopfSpec GoodReductionJacobian
open Deformation.PDivisible Deformation.ModpDieudonne
open NeronOggShafarevich
open AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine
open ModularCurve.KwNo6HrouteV
open ModularCurve.KwNo6HrouteY
open ModularCurve.KwNo6HrouteZ
open ModularCurve.GF24a9RRDx
open ModularCurve.GF24a12CohenSupply
open Ldgr30BankGate
open Modularity.Ldgr27TraceSemilinearSlice
open Ldgr24DefectKernelSlice
open Ldgr23CohenDefectCorrectionSlice
open ModularCurve.Ldgr25PlaceExtensionSlice
open Ldgr25CorrectedChoiceSlice
open Modularity.Ldgr26CorrectedRowsBandSlice
open ModularCurve.GF24a11bRowACurrencyBridge
open ModularCurve.GF24a12CohenSupply
open ModularCurve.Ldgr32RegularLegSlice
open ModularCurve.Ldgr31PerPlaceRowJoinSlice
open ModularCurve.Ldgr29SimplePoleResidueSlice
open ModularCurve.Ldgr25CotraceCompatSlice
open AlgebraicCurve.FiberKaehlerLocalDatum
open ModularCurve.KwNo6HrouteS
open ModularCurve.KwNo6HrouteR

noncomputable section

section

namespace ModularCurve
namespace KwOdaDHDR

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

set_option linter.unusedSectionVars false
section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kwHgf_v278_aCoeff_eq_zero_of_evalDepth_zero (v : Place K F)
    (S : Lg37CompletionSection v) {n : ℕ} (w : lg37_completion v)
    (hw : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n w = 0)
    {k : ℕ} (hk : k < n) :
    aCoeff v S k w = 0 := by
  have hspec := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S n w)
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S n w) with hcc_def
  have hsum : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
      (∑ i ∈ Finset.range n, S.lift ((fun i => cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e : (∑ i ∈ Finset.range n, S.lift (cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = w - (w - ∑ i ∈ Finset.range n, S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by ring
    simp only at e ⊢
    rw [e, map_sub, hw, hspec, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S n
    (fun i => cc i) hsum k hk
  rw [← taylor_choose_eq_aCoeff v S n w hk, ← hcc_def]
  exact hzero

theorem kwHgf_v278_resStar_approximant_mul (v : Place K F)
    (S : Lg37CompletionSection v) (ℓ : v.toValuationSubring) (M : ℕ)
    (hvan : ∀ k, 1 ≤ k → k ≤ M →
      aCoeff v S k (algebraMap v.toValuationSubring (lg37_completion v) ℓ) = 0)
    (g : F) (hg : g ∈ v.poleSubmodule (M + 1)) :
    resStar v S ((ℓ : F) * g) = IsLocalRing.residue _ ℓ * resStar v S g := by
  set a := IsLocalRing.residue _ ℓ with ha

  have hgN : (-v.ord g).toNat ≤ M + 1 := by
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [v.ord_zero]; simp
    · have := (v.mem_poleSubmodule_iff_ord hg0).mp hg
      omega
  have hlgN : (-v.ord ((ℓ : F) * g)).toNat ≤ M + 1 := by
    rcases eq_or_ne ((ℓ : F) * g) 0 with h0 | hlg0
    · rw [h0, v.ord_zero]; simp
    · have hg0 : g ≠ 0 := right_ne_zero_of_mul hlg0
      have hl0 : (ℓ : F) ≠ 0 := left_ne_zero_of_mul hlg0
      have hge := (v.mem_poleSubmodule_iff_ord hg0).mp hg
      have hlge : (0 : ℤ) ≤ v.ord (ℓ : F) := (v.mem_iff_ord_nonneg hl0).mp ℓ.2
      rw [v.ord_mul hl0 hg0]
      omega

  rw [← aCoeff_clearedHat_of_le v S ((ℓ : F) * g) hlgN,
    ← aCoeff_clearedHat_of_le v S g hgN]
  set x := clearedHat v g hgN with hx_def
  have hιℓx : clearedHat v ((ℓ : F) * g) hlgN
      = algebraMap v.toValuationSubring (lg37_completion v) ℓ * x := by
    rw [hx_def]
    unfold clearedHat
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    ring
  rw [hιℓx]

  have hsplit : algebraMap v.toValuationSubring (lg37_completion v) ℓ * x
      = S.lift a * x
        + (algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) * x := by
    ring
  rw [hsplit, aCoeff_add]

  rw [kwHgf_v277_aCoeff_section_lift_mul v S (M + 1) a x]

  suffices hsnd : aCoeff v S (M + 1)
      ((algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) * x)
      = 0 by rw [hsnd, add_zero]

  set x' := algebraMap v.toValuationSubring (lg37_completion v)
    ⟨v.uniformizer ^ (M + 1) * g, (v.mem_poleSubmodule).mp hg⟩ with hx'_def
  have hxfac : x = algebraMap v.toValuationSubring (lg37_completion v)
      v.uniformizerSubring * x' := by
    rw [hx_def, hx'_def]
    unfold clearedHat
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hxfac, show
    (algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a)
        * (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring * x')
      = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
        * ((algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a)
          * x') from by ring,
    aCoeff_shift]

  have hev : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (M + 1)
      (algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) = 0 := by
    have hspec := Classical.choose_spec
      (mp72a102_t3_sigma_taylor_expansion v S (M + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) ℓ))
    set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (M + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) ℓ)) with hcc_def
    have hcc : ∀ k, k < M + 1 → cc k
        = aCoeff v S k (algebraMap v.toValuationSubring (lg37_completion v) ℓ) :=
      fun k hk => hcc_def ▸ taylor_choose_eq_aCoeff v S (M + 1) _ hk
    suffices hsum : (∑ i ∈ Finset.range (M + 1), S.lift (cc i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = S.lift a by
      rw [← hsum]; exact hspec
    rw [Finset.sum_eq_single 0
      (fun i hi hi0 => by
        rw [hcc i (Finset.mem_range.mp hi),
          hvan i (Nat.one_le_iff_ne_zero.mpr hi0)
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
          _root_.map_zero, zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
      pow_zero, mul_one, hcc 0 (by omega), aCoeff_zero,
      lg37_residueHat_algebraMap, ← ha]

  exact kwHgf_v278_aCoeff_eq_zero_of_evalDepth_zero v S
    ((algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) * x')
    (by rw [map_mul, hev, zero_mul]) (Nat.lt_succ_self M)

end Generic

end ModularCurve.KwOdaDHDR

end

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwTateRR3

section ApproximantHev

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem approximant_evalₐ_sub_lift_eq_zero (u : Place K L) (S : Lg37CompletionSection u)
    {ℓ : u.toValuationSubring} {M : ℕ}
    (hvan : ∀ k, 1 ≤ k → k ≤ M →
      aCoeff u S k (algebraMap u.toValuationSubring (lg37_completion u) ℓ) = 0) :
    AdicCompletion.evalₐ (maximalIdeal u.toValuationSubring) (M + 1)
      (algebraMap u.toValuationSubring (lg37_completion u) ℓ
        - S.lift (IsLocalRing.residue _ ℓ)) = 0 := by
  set a := IsLocalRing.residue _ ℓ with ha
  have hspec := Classical.choose_spec
    (mp72a102_t3_sigma_taylor_expansion u S (M + 1)
      (algebraMap u.toValuationSubring (lg37_completion u) ℓ))
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion u S (M + 1)
      (algebraMap u.toValuationSubring (lg37_completion u) ℓ)) with hcc_def
  have hcc : ∀ k, k < M + 1 → cc k
      = aCoeff u S k (algebraMap u.toValuationSubring (lg37_completion u) ℓ) :=
    fun k hk => hcc_def ▸ taylor_choose_eq_aCoeff u S (M + 1) _ hk
  suffices hsum : (∑ i ∈ Finset.range (M + 1), S.lift (cc i)
      * algebraMap u.toValuationSubring (lg37_completion u)
          u.uniformizerSubring ^ i) = S.lift a by
    rw [← hsum]; exact hspec
  rw [Finset.sum_eq_single 0
    (fun i hi hi0 => by
      rw [hcc i (Finset.mem_range.mp hi),
        hvan i (Nat.one_le_iff_ne_zero.mpr hi0)
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
        _root_.map_zero, zero_mul])
    (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
    pow_zero, mul_one, hcc 0 (by omega), aCoeff_zero,
    lg37_residueHat_algebraMap, ← ha]

end ApproximantHev

section V410aBridge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem v410a_mem_completionIdeal_pow_of_evalₐ_eq_zero (n : ℕ)
    (z : lg37_completion u)
    (hz : AdicCompletion.evalₐ (maximalIdeal u.toValuationSubring) n z = 0) :
    kwF4R1V410a_ringEquiv u z ∈ (u.heightOneSpectrum.completionIdeal L) ^ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, kwF4R1V410a_ringEquiv_apply,
    kwF4R1V410a_mk_forward u n z, hz, _root_.map_zero]

theorem valued_algebraMap_uniformizer :
    Valued.v (algebraMap L u.adicCompletion u.uniformizer) = WithZero.exp (-1 : ℤ) := by
  rw [show algebraMap L u.adicCompletion u.uniformizer
      = ((u.uniformizer : L) : u.adicCompletion) from rfl,
    valuedAdicCompletion_eq_valuation' (K := L) u.heightOneSpectrum,
    show u.heightOneSpectrum.valuation L u.uniformizer = u.adicValuation u.uniformizer
      from rfl,
    show u.adicValuation u.uniformizer = WithZero.exp (-(u.ord u.uniformizer)) from by
      rw [Place.ord, neg_neg,
        WithZero.exp_log (u.adicValuation_ne_zero u.uniformizer_ne_zero)],
    u.ord_uniformizer]

theorem v410a_evalDepth_mul_mem_integers (n : ℕ) (z : lg37_completion u)
    (hz : AdicCompletion.evalₐ (maximalIdeal u.toValuationSubring) n z = 0)
    (fh : u.adicCompletion)
    (hfh : (algebraMap L u.adicCompletion u.uniformizer)^n * fh ∈ u.adicCompletionIntegers) :
    ((kwF4R1V410a_ringEquiv u z : u.adicCompletionIntegers) : u.adicCompletion) * fh
      ∈ u.adicCompletionIntegers := by
  rw [mem_adicCompletionIntegers, map_mul]

  have hzmem := v410a_mem_completionIdeal_pow_of_evalₐ_eq_zero u n z hz
  have hzval : Valued.v
      ((kwF4R1V410a_ringEquiv u z : u.adicCompletionIntegers) : u.adicCompletion)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rw [WithZero.exp_eq_coe_ofAdd]
    exact (mem_completionIdeal_pow L u.heightOneSpectrum
      (kwF4R1V410a_ringEquiv u z)).mp hzmem

  have hπval : Valued.v ((algebraMap L u.adicCompletion u.uniformizer)^n)
      = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, valued_algebraMap_uniformizer u, ← WithZero.exp_nsmul]
    congr 1; ring
  have hfhval : Valued.v fh ≤ WithZero.exp (n : ℤ) := by
    have h1 : Valued.v ((algebraMap L u.adicCompletion u.uniformizer)^n * fh) ≤ 1 := hfh
    rw [map_mul, hπval] at h1
    calc Valued.v fh
        = WithZero.exp (n : ℤ) * (WithZero.exp (-(n : ℤ)) * Valued.v fh) := by
          rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
      _ ≤ WithZero.exp (n : ℤ) * 1 := mul_le_mul_of_nonneg_left h1 (zero_le)
      _ = WithZero.exp (n : ℤ) := mul_one _

  calc Valued.v ((kwF4R1V410a_ringEquiv u z : u.adicCompletionIntegers)
          : u.adicCompletion) * Valued.v fh
      ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := mul_le_mul' hzval hfhval
    _ = WithZero.exp ((-(n : ℤ)) + (n : ℤ)) := (WithZero.exp_add _ _).symm
    _ = 1 := by rw [_root_.neg_add_cancel, WithZero.exp_zero]

end V410aBridge

section EpsSpec

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

theorem kwTateRR3_localResidueCompletion_sub (u : Place K L) (xh yh : u.adicCompletion) :
    kwHgfV352_localResidueCompletion u (xh - yh)
      = kwHgfV352_localResidueCompletion u xh
        - kwHgfV352_localResidueCompletion u yh := by
  rw [eq_sub_iff_add_eq, ← kwHgfV352_localResidueCompletion_add, sub_add_cancel]

theorem algebraMap_sub_cohenSectionHat_eq_v410a (u : Place K L)
    (S : Lg37CompletionSection u) (ℓ : u.toValuationSubring) :
    algebraMap L u.adicCompletion (ℓ : L)
        - cohenSectionHat u S (IsLocalRing.residue _ ℓ)
      = ((kwF4R1V410a_ringEquiv u
            (algebraMap u.toValuationSubring (lg37_completion u) ℓ
              - S.lift (IsLocalRing.residue _ ℓ))
          : u.adicCompletionIntegers) : u.adicCompletion) := by
  have hℓ : algebraMap L u.adicCompletion (ℓ : L)
      = ((kwF4R1V410a_ringEquiv u
            (algebraMap u.toValuationSubring (lg37_completion u) ℓ)
          : u.adicCompletionIntegers) : u.adicCompletion) := by
    rw [kwF4R1V410a_ringEquiv_of u ℓ]; rfl
  rw [hℓ, cohenSectionHat_apply, map_sub]
  exact (AddSubgroupClass.coe_sub _ _).symm

theorem localResidueCompletion_mul_cohenSectionHat
    (u : Place K L) (S : Lg37CompletionSection u)
    (fh : u.adicCompletion) (c : u.ResidueField) :
    kwHgfV352_localResidueCompletion u (fh * cohenSectionHat u S c)
      = kwHgfV352_localResidueCompletion u fh * c := by

  obtain ⟨f, hf⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers u fh

  rcases (em (f ∈ u.toValuationSubring)) with hfmem | hfnmem
  · have hfh_mem : fh ∈ u.adicCompletionIntegers := by
      have hfhat : algebraMap L u.adicCompletion f ∈ u.adicCompletionIntegers :=
        (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u f).mpr hfmem
      have hsub : algebraMap L u.adicCompletion f
          - (algebraMap L u.adicCompletion f - fh) = fh := by ring
      exact hsub ▸ sub_mem hfhat hf
    rw [kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers u hfh_mem, zero_mul,
      kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers u
        (mul_mem hfh_mem (cohenSectionHat_mem_integers u S c))]

  have hf0 : f ≠ 0 := fun h => hfnmem (h ▸ zero_mem _)
  have hord_neg : u.ord f < 0 :=
    not_le.mp (fun h => hfnmem ((u.mem_iff_ord_nonneg hf0).mpr h))
  set M := (-u.ord f).toNat with hM_def
  have hM_eq : (M : ℤ) = -u.ord f := Int.toNat_of_nonneg (by omega)

  have hfpole : f ∈ u.poleSubmodule (M + 1) := by
    rw [u.mem_poleSubmodule_iff_ord hf0]; omega

  obtain ⟨ℓ, hℓres, hℓvan⟩ := exists_approximant u S c M

  have hV278 : resStar u S ((ℓ : L) * f) = c * resStar u S f := by
    rw [← hℓres]
    exact kwHgf_v278_resStar_approximant_mul u S ℓ M hℓvan f hfpole

  have hfhLR : kwHgfV352_localResidueCompletion u fh = resStar u S f := by
    rw [AlgebraicCurve.kwHgfV352_localResidueCompletion_spec u fh hf, localResidue_eq_resStar u S f]

  have hgap : algebraMap L u.adicCompletion ((ℓ : L) * f) - fh * cohenSectionHat u S c
      ∈ u.adicCompletionIntegers := by
    have hℓhat_mem : algebraMap L u.adicCompletion (ℓ : L) ∈ u.adicCompletionIntegers :=
      (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr ℓ.2

    have hfirst : algebraMap L u.adicCompletion (ℓ : L)
        * (algebraMap L u.adicCompletion f - fh) ∈ u.adicCompletionIntegers :=
      mul_mem hℓhat_mem hf

    have hsecond : (algebraMap L u.adicCompletion (ℓ : L)
        - cohenSectionHat u S c) * fh ∈ u.adicCompletionIntegers := by
      rw [← hℓres, algebraMap_sub_cohenSectionHat_eq_v410a u S ℓ]
      refine v410a_evalDepth_mul_mem_integers u (M + 1) _
        (approximant_evalₐ_sub_lift_eq_zero u S hℓvan) fh ?_

      have hπmem : algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
          ∈ u.adicCompletionIntegers := pow_mem
        ((kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
          u.uniformizer_mem) _
      have hπf : algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
          * algebraMap L u.adicCompletion f ∈ u.adicCompletionIntegers := by
        rw [← map_pow, ← map_mul]
        exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
          ((u.mem_poleSubmodule).mp hfpole)
      have hdecomp : algebraMap L u.adicCompletion u.uniformizer ^ (M + 1) * fh
          = algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
              * algebraMap L u.adicCompletion f
            - algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
              * (algebraMap L u.adicCompletion f - fh) := by ring
      rw [hdecomp]; exact sub_mem hπf (mul_mem hπmem hf)

    have hdecomp : algebraMap L u.adicCompletion ((ℓ : L) * f)
          - fh * cohenSectionHat u S c
        = algebraMap L u.adicCompletion (ℓ : L)
            * (algebraMap L u.adicCompletion f - fh)
          + (algebraMap L u.adicCompletion (ℓ : L)
              - cohenSectionHat u S c) * fh := by
      rw [map_mul]; ring
    rw [hdecomp]; exact add_mem hfirst hsecond

  rw [AlgebraicCurve.kwHgfV352_localResidueCompletion_spec u _ hgap,
    localResidue_eq_resStar u S ((ℓ : L) * f), hV278, hfhLR, mul_comm]

end EpsSpec

section ComplMint

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

structure KwTateRR3CohenLaurentCompl (u : Place K L) [u.FiniteResidue] where

  S : Lg37CompletionSection u

  B : Submodule K u.adicCompletion

  hcompl : IsCompl (adicIntegersKSubmod u) B

  shift_sub_mem : ∀ z : B,
    algebraMap L u.adicCompletion u.uniformizer * (z : u.adicCompletion)
      - cohenSectionHat u S (kwHgfV352_localResidueCompletion u (z : u.adicCompletion)) ∈ B

variable (K L) in

def KwTateRR3CohenLaurentComplExists : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue], Nonempty (KwTateRR3CohenLaurentCompl u)

end ComplMint

section Construct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]
variable {u : Place K L} [u.FiniteResidue]

def localResidueCompletionₗ (u : Place K L) : u.adicCompletion →ₗ[K] u.ResidueField where
  toFun := kwHgfV352_localResidueCompletion u
  map_add' := kwHgfV352_localResidueCompletion_add u
  map_smul' c x := by
    rw [RingHom.id_apply]; exact kwF4R1V394a_localResidueCompletion_smul u c x

def cohenLaurentSpec_of_compl (C : KwTateRR3CohenLaurentCompl u) :
    KwTateRR3CohenLaurentSpec u where
  S := C.S
  B := C.B
  hcompl := C.hcompl
  ε := (localResidueCompletionₗ u).comp C.B.subtype
  shift_sub_mem z := C.shift_sub_mem z
  ε_principalPart_mul_sectionHat fh c := by

    show kwHgfV352_localResidueCompletion u
        (fh * cohenSectionHat u C.S c
          - cohenProjC u C.B C.hcompl (fh * cohenSectionHat u C.S c))
      = kwHgfV352_localResidueCompletion u fh * c
    rw [kwTateRR3_localResidueCompletion_sub u,
      kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers u
        (cohenProjC_mem_integers u C.B C.hcompl _),
      sub_zero, localResidueCompletion_mul_cohenSectionHat u C.S fh c]

end Construct

section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

theorem kwTateRR3_cohenLaurentSpecExists_of_complExists
    (hC : KwTateRR3CohenLaurentComplExists K L) :
    KwTateRR3CohenLaurentSpecExists K L := fun u _ =>
  (hC u).map cohenLaurentSpec_of_compl

theorem kwTateRR3_cohenKernelDataExists_of_complExists
    (hC : KwTateRR3CohenLaurentComplExists K L) :
    KwF4gRRTateCohenKernelDataExists K L :=
  kwTateRR3_cohenKernelDataExists_of_cohenLaurentSpec
    (kwTateRR3_cohenLaurentSpecExists_of_complExists hC)

end Headline

end ModularCurve.KwTateRR3

end
end

end

section
section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


noncomputable section

namespace ModularCurve
namespace KwTateRR3

section UniformizerHat

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

abbrev uniformizerHat : u.adicCompletion := algebraMap L u.adicCompletion u.uniformizer

theorem uniformizerHat_ne_zero : uniformizerHat u ≠ 0 :=
  fun h => u.uniformizer_ne_zero
    ((map_eq_zero_iff _ (algebraMap L u.adicCompletion).injective).mp h)

theorem uniformizerHat_mem_integers : uniformizerHat u ∈ u.adicCompletionIntegers :=
  (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr u.uniformizer_mem

theorem irreducible_uniformizerHat :
    Irreducible (⟨uniformizerHat u, uniformizerHat_mem_integers u⟩
      : u.adicCompletionIntegers) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (adicCompletion.maximalIdeal_eq_span_uniformizer L u.heightOneSpectrum ?_)
  rw [valued_algebraMap_uniformizer u, WithZero.exp_eq_coe_ofAdd]

end UniformizerHat

section CohenPhi

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (S : Lg37CompletionSection u)

def cohenΦ : (ℕ →₀ u.ResidueField) →ₗ[K] u.adicCompletion :=
  Finsupp.lsum K fun j =>
    lmulK u ((uniformizerHat u)⁻¹ ^ (j + 1)) ∘ₗ (cohenSectionHat u S).toLinearMap

theorem cohenΦ_apply (δ : ℕ →₀ u.ResidueField) :
    cohenΦ u S δ = δ.sum fun j c => (uniformizerHat u)⁻¹ ^ (j + 1) * cohenSectionHat u S c := by
  rw [cohenΦ, Finsupp.coe_lsum]; rfl

theorem cohenΦ_single (j : ℕ) (c : u.ResidueField) :
    cohenΦ u S (Finsupp.single j c)
      = (uniformizerHat u)⁻¹ ^ (j + 1) * cohenSectionHat u S c := by
  rw [cohenΦ_apply, Finsupp.sum_single_index]
  rw [_root_.map_zero, mul_zero]

def cohenB : Submodule K u.adicCompletion := LinearMap.range (cohenΦ u S)

theorem monomial_mem_cohenB (j : ℕ) (c : u.ResidueField) :
    (uniformizerHat u)⁻¹ ^ (j + 1) * cohenSectionHat u S c ∈ cohenB u S :=
  ⟨Finsupp.single j c, cohenΦ_single u S j c⟩

end CohenPhi

section LocResComplMonomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K] (u : Place K L)

theorem locResCompl_uniformizerHat_inv (S : Lg37CompletionSection u) :
    kwHgfV352_localResidueCompletion u ((uniformizerHat u)⁻¹) = 1 := by
  rw [show (uniformizerHat u)⁻¹ = algebraMap L u.adicCompletion (u.uniformizer)⁻¹ from
      (map_inv₀ (algebraMap L u.adicCompletion) _).symm,
    AlgebraicCurve.kwHgfV352_localResidueCompletion_algebraMap u, localResidue_eq_resStar u S,
    resStar_simplePole u S _
      (by rw [mul_inv_cancel₀ u.uniformizer_ne_zero]; exact one_mem _)]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (mul_inv_cancel₀ u.uniformizer_ne_zero)) |>.trans (map_one _)

theorem locResCompl_uniformizerHat_inv_pow_succ (S : Lg37CompletionSection u)
    {j : ℕ} (hj : 1 ≤ j) :
    kwHgfV352_localResidueCompletion u ((uniformizerHat u)⁻¹ ^ (j + 1)) = 0 := by
  rw [show (uniformizerHat u)⁻¹ ^ (j + 1)
        = algebraMap L u.adicCompletion (u.uniformizer ^ (j + 1))⁻¹ by
      rw [map_inv₀ (algebraMap L u.adicCompletion), map_pow, inv_pow],
    AlgebraicCurve.kwHgfV352_localResidueCompletion_algebraMap u, localResidue_eq_resStar u S,
    resStar_higherPoleMonomial u S hj]

end LocResComplMonomial

section LocResComplPhi

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem locResCompl_cohenΦ (δ : ℕ →₀ u.ResidueField) :
    kwHgfV352_localResidueCompletion u (cohenΦ u S δ) = δ 0 := by
  rw [show kwHgfV352_localResidueCompletion u (cohenΦ u S δ)
      = localResidueCompletionₗ u (cohenΦ u S δ) from rfl,
    cohenΦ_apply, map_finsuppSum]
  refine (Finsupp.sum_eq_single 0 (fun j _ hj0 => ?_) (fun _ => ?_)).trans ?_
  · show kwHgfV352_localResidueCompletion u _ = 0
    rw [localResidueCompletion_mul_cohenSectionHat u S,
      locResCompl_uniformizerHat_inv_pow_succ u S (Nat.one_le_iff_ne_zero.mpr hj0), zero_mul]
  · show kwHgfV352_localResidueCompletion u _ = 0
    rw [_root_.map_zero, mul_zero]
    exact _root_.map_zero (localResidueCompletionₗ u)
  · show kwHgfV352_localResidueCompletion u _ = _
    rw [zero_add, pow_one, localResidueCompletion_mul_cohenSectionHat u S,
      locResCompl_uniformizerHat_inv u S, one_mul]

end LocResComplPhi

section ShiftCore

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem uniformizerHat_mul_cohenΦ (δ : ℕ →₀ u.ResidueField) :
    uniformizerHat u * cohenΦ u S δ
      = δ.sum fun j c => (uniformizerHat u)⁻¹ ^ j * cohenSectionHat u S c := by
  rw [cohenΦ_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [pow_succ', ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ (uniformizerHat_ne_zero u), one_mul]

theorem uniformizerHat_mul_cohenΦ_sub_mem (δ : ℕ →₀ u.ResidueField) :
    uniformizerHat u * cohenΦ u S δ - cohenSectionHat u S (δ 0) ∈ cohenB u S := by
  rw [uniformizerHat_mul_cohenΦ u S δ, Finsupp.sum,
    show cohenSectionHat u S (δ 0)
        = (uniformizerHat u)⁻¹ ^ 0 * cohenSectionHat u S (δ 0) by rw [pow_zero, one_mul]]

  have hterm : ∀ j ∈ δ.support, j ≠ 0 →
      (uniformizerHat u)⁻¹ ^ j * cohenSectionHat u S (δ j) ∈ cohenB u S := fun j _ hj0 => by
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    exact monomial_mem_cohenB u S j' (δ (j' + 1))
  rcases em ((0 : ℕ) ∈ δ.support) with h0 | h0
  · rw [← Finset.sum_erase_add _ _ h0, add_sub_cancel_right]
    exact sum_mem fun j hj => hterm j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  · rw [Finsupp.notMem_support_iff.mp h0, _root_.map_zero, mul_zero, sub_zero]
    exact sum_mem fun j hj => hterm j hj fun hj0 => h0 (hj0 ▸ hj)

end ShiftCore

section Disjoint

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem valued_cohenSectionHat_of_ne_zero {c : u.ResidueField} (hc : c ≠ 0) :
    Valued.v (cohenSectionHat u S c) = 1 := by
  refine le_antisymm (cohenSectionHat_mem_integers u S c) ?_
  have hprod : Valued.v (cohenSectionHat u S c) * Valued.v (cohenSectionHat u S c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  calc (1 : ℤᵐ⁰)
      = Valued.v (cohenSectionHat u S c) * Valued.v (cohenSectionHat u S c⁻¹) := hprod.symm
    _ ≤ Valued.v (cohenSectionHat u S c) * 1 :=
        mul_le_mul_right (cohenSectionHat_mem_integers u S c⁻¹) _
    _ = Valued.v (cohenSectionHat u S c) := mul_one _

theorem uniformizerHat_pow_mul_cohenΦ_sub_top (δ : ℕ →₀ u.ResidueField)
    (hδ : δ.support.Nonempty) :
    let J := δ.support.max' hδ
    (uniformizerHat u) ^ (J + 1) * cohenΦ u S δ - cohenSectionHat u S (δ J)
      = ∑ j ∈ δ.support.erase J,
          (uniformizerHat u) ^ (J - j) * cohenSectionHat u S (δ j) := by
  intro J
  have hJmem : J ∈ δ.support := δ.support.max'_mem hδ
  rw [cohenΦ_apply, Finsupp.mul_sum, Finsupp.sum,
    ← Finset.sum_erase_add _ _ hJmem,
    show (uniformizerHat u) ^ (J + 1) * ((uniformizerHat u)⁻¹ ^ (J + 1)
            * cohenSectionHat u S (δ J))
        = cohenSectionHat u S (δ J) by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (uniformizerHat_ne_zero u), one_pow, one_mul],
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjJ : j < J := lt_of_le_of_ne
    (δ.support.le_max' j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
  rw [← mul_assoc]
  congr 1

  rw [show J + 1 = (J - j) + (j + 1) by omega, pow_add, mul_assoc,
    ← mul_pow, mul_inv_cancel₀ (uniformizerHat_ne_zero u), one_pow, mul_one]

theorem cohenΦ_mem_integers_iff_zero (δ : ℕ →₀ u.ResidueField) :
    cohenΦ u S δ ∈ u.adicCompletionIntegers → δ = 0 := by
  intro hmem
  by_contra hδ0
  have hδne : δ.support.Nonempty := Finsupp.support_nonempty_iff.mpr hδ0
  set J := δ.support.max' hδne with hJ
  have hδJ : δ J ≠ 0 := Finsupp.mem_support_iff.mp (δ.support.max'_mem hδne)

  have hi : Valued.v ((uniformizerHat u) ^ (J + 1) * cohenΦ u S δ)
      ≤ WithZero.exp (-1 : ℤ) := by
    rw [map_mul, map_pow, valued_algebraMap_uniformizer u, ← WithZero.exp_nsmul]
    calc WithZero.exp ((J + 1) • (-1 : ℤ)) * Valued.v (cohenΦ u S δ)
        ≤ WithZero.exp ((J + 1) • (-1 : ℤ)) * 1 := mul_le_mul_right hmem _
      _ = WithZero.exp (-((J : ℤ) + 1)) := by rw [mul_one]; congr 1; ring
      _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)

  have hii : Valued.v
      ((uniformizerHat u) ^ (J + 1) * cohenΦ u S δ - cohenSectionHat u S (δ J))
      ≤ WithZero.exp (-1 : ℤ) := by
    rw [uniformizerHat_pow_mul_cohenΦ_sub_top u S δ hδne]
    refine Finset.sum_induction _ (fun x => Valued.v x ≤ WithZero.exp (-1 : ℤ))
      (fun a b ha hb => (Valued.v.map_add a b).trans (max_le ha hb))
      ?_ fun j hj => ?_
    · show Valued.v (0 : u.adicCompletion) ≤ _
      rw [_root_.map_zero]; exact zero_le
    · have hjJ : j < J := lt_of_le_of_ne
        (δ.support.le_max' j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
      show Valued.v (_ * _) ≤ _
      rw [map_mul, map_pow, valued_algebraMap_uniformizer u, ← WithZero.exp_nsmul]
      calc WithZero.exp ((J - j) • (-1 : ℤ)) * Valued.v (cohenSectionHat u S (δ j))
          ≤ WithZero.exp ((J - j) • (-1 : ℤ)) * 1 :=
            mul_le_mul_right (cohenSectionHat_mem_integers u S _) _
        _ = WithZero.exp (-((J - j : ℕ) : ℤ)) := by rw [mul_one]; congr 1; ring
        _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)

  have hiii : Valued.v (cohenSectionHat u S (δ J)) ≤ WithZero.exp (-1 : ℤ) := by
    have hdecomp : cohenSectionHat u S (δ J)
        = (uniformizerHat u) ^ (J + 1) * cohenΦ u S δ
          - ((uniformizerHat u) ^ (J + 1) * cohenΦ u S δ - cohenSectionHat u S (δ J)) := by ring
    rw [hdecomp, sub_eq_add_neg]
    exact (Valued.v.map_add _ _).trans (max_le hi (by rwa [Valuation.map_neg]))

  rw [valued_cohenSectionHat_of_ne_zero u S hδJ] at hiii
  exact absurd hiii (not_le.mpr (by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)))

theorem disjoint_adicIntegersKSubmod_cohenB :
    _root_.Disjoint (adicIntegersKSubmod u) (cohenB u S) := by
  rw [Submodule.disjoint_def]
  rintro x hxO ⟨δ, rfl⟩
  rw [cohenΦ_mem_integers_iff_zero u S δ hxO, _root_.map_zero]

end Disjoint

section Codisjoint

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem uniformizerHat_inv_mul_mem_integers_of_valued_le
    {y : u.adicCompletion} (hy : Valued.v y ≤ WithZero.exp (-1 : ℤ)) :
    (uniformizerHat u)⁻¹ * y ∈ u.adicCompletionIntegers := by
  show Valued.v ((uniformizerHat u)⁻¹ * y) ≤ 1
  rw [map_mul, map_inv₀, valued_algebraMap_uniformizer u, ← WithZero.exp_neg, neg_neg]
  calc WithZero.exp (1 : ℤ) * Valued.v y
      ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := mul_le_mul_right hy _
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

theorem valued_le_of_mem_completionIdeal {y : u.adicCompletionIntegers}
    (hy : y ∈ u.heightOneSpectrum.completionIdeal L) :
    Valued.v (y : u.adicCompletion) ≤ WithZero.exp (-1 : ℤ) := by
  have := (mem_completionIdeal_pow L u.heightOneSpectrum y).mp
    (by rw [pow_one]; exact hy)
  rwa [← WithZero.exp_eq_coe_ofAdd, show (-((1 : ℕ) : ℤ)) = (-1 : ℤ) by norm_num] at this

theorem exists_residue_peel (ŷ : u.adicCompletionIntegers) :
    ∃ c : u.ResidueField,
      (uniformizerHat u)⁻¹ * ((ŷ : u.adicCompletion) - cohenSectionHat u S c)
        ∈ u.adicCompletionIntegers := by
  obtain ⟨ℓ, hℓ⟩ := kwF4R1V410a_exists_sub_mem_completionIdeal_pow u 1 ŷ
  refine ⟨IsLocalRing.residue _ ℓ, uniformizerHat_inv_mul_mem_integers_of_valued_le u ?_⟩

  have hcoe : ((algebraMap u.toValuationSubring u.adicCompletionIntegers ℓ
        : u.adicCompletionIntegers) : u.adicCompletion)
      = algebraMap L u.adicCompletion (ℓ : L) := rfl
  have hdecomp : (ŷ : u.adicCompletion) - cohenSectionHat u S (IsLocalRing.residue _ ℓ)
      = ((ŷ - algebraMap u.toValuationSubring u.adicCompletionIntegers ℓ
            : u.adicCompletionIntegers) : u.adicCompletion)
        + (algebraMap L u.adicCompletion (ℓ : L)
            - cohenSectionHat u S (IsLocalRing.residue _ ℓ)) := by
    push_cast [hcoe]; ring
  rw [hdecomp]
  refine (Valued.v.map_add _ _).trans (max_le ?_ ?_)
  ·
    refine valued_le_of_mem_completionIdeal u ?_
    rw [← pow_one (u.heightOneSpectrum.completionIdeal L)]; exact hℓ
  ·
    rw [algebraMap_sub_cohenSectionHat_eq_v410a u S ℓ]
    refine valued_le_of_mem_completionIdeal u ?_
    rw [← pow_one (u.heightOneSpectrum.completionIdeal L)]
    exact v410a_mem_completionIdeal_pow_of_evalₐ_eq_zero u 1 _
      (approximant_evalₐ_sub_lift_eq_zero u S (M := 0) (ℓ := ℓ)
        (fun k hk1 hk0 => absurd hk0 (by omega)))

theorem mem_sup_of_uniformizerHat_pow_mul_mem_integers (M : ℕ) :
    ∀ x : u.adicCompletion, (uniformizerHat u) ^ M * x ∈ u.adicCompletionIntegers →
      x ∈ adicIntegersKSubmod u ⊔ cohenB u S := by
  induction M with
  | zero => intro x hx; rw [pow_zero, one_mul] at hx; exact Submodule.mem_sup_left hx
  | succ M IH =>
    intro x hx
    obtain ⟨c, hc⟩ := exists_residue_peel u S ⟨_, hx⟩

    have hne := uniformizerHat_ne_zero u
    have hstep : (uniformizerHat u) ^ M * (x
        - (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c)
        ∈ u.adicCompletionIntegers := by
      have heq : (uniformizerHat u) ^ M * (x
            - (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c)
          = (uniformizerHat u)⁻¹ * ((uniformizerHat u)^(M+1)*x - cohenSectionHat u S c) := by
        rw [mul_sub, mul_sub,
          show (uniformizerHat u)⁻¹ * ((uniformizerHat u)^(M+1) * x)
              = (uniformizerHat u)^M * x by
            rw [← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀ hne, one_mul],
          show (uniformizerHat u)^M * ((uniformizerHat u)⁻¹^(M+1) * cohenSectionHat u S c)
              = (uniformizerHat u)⁻¹ * cohenSectionHat u S c by
            rw [← mul_assoc, pow_succ, ← mul_assoc, ← mul_pow,
              mul_inv_cancel₀ hne, one_pow, one_mul]]
      rw [heq]; exact hc
    have hx' := IH _ hstep
    have hb : (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c ∈ cohenB u S :=
      monomial_mem_cohenB u S M c
    have hx_eq : x = (x - (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c)
        + (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c := by ring
    rw [hx_eq]
    exact add_mem hx' (Submodule.mem_sup_right hb)

theorem codisjoint_adicIntegersKSubmod_cohenB :
    Codisjoint (adicIntegersKSubmod u) (cohenB u S) := by
  rw [codisjoint_iff, eq_top_iff]
  intro x _
  obtain ⟨M, hM⟩ := kwF4gRRTate_clearPole u
    ⟨uniformizerHat u, uniformizerHat_mem_integers u⟩ (irreducible_uniformizerHat u) x
  exact mem_sup_of_uniformizerHat_pow_mul_mem_integers u S M x hM

end Codisjoint

section Assembly

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

def cohenLaurentCompl_of_section (u : Place K L) [u.FiniteResidue]
    (S : Lg37CompletionSection u) : KwTateRR3CohenLaurentCompl u where
  S := S
  B := cohenB u S
  hcompl := ⟨disjoint_adicIntegersKSubmod_cohenB u S,
    codisjoint_adicIntegersKSubmod_cohenB u S⟩
  shift_sub_mem z := by
    obtain ⟨δ, hδ⟩ := z.2
    rw [← hδ, locResCompl_cohenΦ u S δ]
    exact uniformizerHat_mul_cohenΦ_sub_mem u S δ

end Assembly

section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

theorem kwTateRR3_cohenLaurentComplExists :
    KwTateRR3CohenLaurentComplExists K L := fun u _ => by
  haveI : FiniteDimensional K u.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsSeparable K u.ResidueField :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact (completionSection_nonempty_generic u).map (cohenLaurentCompl_of_section u)

theorem kwTateRR3_cohenKernelDataExists :
    KwF4gRRTateCohenKernelDataExists K L :=
  kwTateRR3_cohenKernelDataExists_of_complExists kwTateRR3_cohenLaurentComplExists

end Headline

end ModularCurve.KwTateRR3

end
end

end

namespace AlgebraicCurve

/-- The Tate agreement: the Cohen–Tate kernel data exists, so the
`KwF4gRRTateAgreement` atom holds. -/
theorem tateAgreement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_agreement_of_kernelData hfin
    ModularCurve.KwTateRR3.kwTateRR3_cohenKernelDataExists

end AlgebraicCurve

