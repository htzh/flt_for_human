/-
Trace-completion commutation — `AlgebraicCurve.residueTraceCompletionCommute`, after
FLT's `P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean` (1,109 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean>),
published by
`Theorems/Thm_AlgebraicCurve_residueTraceCompletionCommute.lean` as
`AlgebraicCurve.residueTraceCompletionCommute`.

This is set 3.4's first module.  It is the small consumer of the four Tate theory
modules: the wire lemma `kwF4gRRTate_RTCC_of_tate` assembles the four Tate atoms
(`tateCommFinite`, `tateAgreement`, `tateChainRule`, `tateTraceCompat_of_isSeparable`)
into the K-currency cotrace identity, and the public
`residueTraceCompletionCommute` instantiates them at the pin wrapper's binders.

The pin's `S_` file is almost entirely empty scaffolding: all eight of its remaining
public declarations (`exists_ord_pos`, `mem_comap_iff_ord_nonneg`, `isUnit_mk_comap_iff`,
`isPrincipalIdealRing_comap`, `kwHgfV352_localResidueCompletion_spec`,
`..._algebraMap`) and its seven `private` helpers are already public in
`Defs/PushPull.lean`, `P1/EnginePrelude.lean` and `P1/DivPow.lean`, so they are
imported, not re-proved.  The `_v2` twin (`residueTraceCompletionCommute_v2`) is
dropped per the PORTING-RR §3 name policy: one name per piece.

The pin's `p2m_*` scaffolding, its outer `P2MW.S_...` namespace and its
`maxHeartbeats` raises are dropped (the project cap is 4,000,000); its section and
`variable` structure is preserved so the public statements are diffed verbatim from
the pin's wrapper.

The pin's `_algebraMap` in `P1/DivPow.lean` is stated about that module's `private`
`kwHgfV352_localResidueCompletion`, so the wire proof re-lands the `algebraMap`
specialisation of the *public* `Defs/TateResidueCurrency.lean` def privately (as 3.3c's
`Tate/Agreement.lean` does).
-/
import FLTForHuman.AlgebraicCurve.Defs.TateResidueCurrency
import FLTForHuman.AlgebraicCurve.Tate.CommFinite
import FLTForHuman.AlgebraicCurve.Tate.Prelude
import FLTForHuman.AlgebraicCurve.Tate.ChainRule
import FLTForHuman.AlgebraicCurve.Tate.Agreement
import FLTForHuman.AlgebraicCurve.Tate.TraceCompat
import FLTForHuman.AlgebraicCurve.P1.DivPow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LinearMap Submodule
open AlgebraicCurve AlgebraicCurve.Place
open ModularCurve.KwF4gRRTate
open ModularCurve.KwF4R1V391a

noncomputable section

section LocalResidueCompletionPublic

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E]

/-- The `algebraMap` specialisation of the public
`kwHgfV352_localResidueCompletion` (`Defs/TateResidueCurrency.lean`); the pin's
`_algebraMap` (`P1/DivPow.lean`) is about that module's `private` copy. -/
private theorem kwHgfV352_localResidueCompletion_algebraMap₀ (v : Place K E) (x : E) :
    kwHgfV352_localResidueCompletion v (algebraMap E v.adicCompletion x)
      = v.localResidue x := by
  unfold kwHgfV352_localResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v
    (algebraMap E v.adicCompletion x)).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v
    (algebraMap E v.adicCompletion x)).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x)
      = (algebraMap E v.adicCompletion x₀ - algebraMap E v.adicCompletion x)
        - (algebraMap E v.adicCompletion x - algebraMap E v.adicCompletion x) := by
    rw [map_sub]; ring
  have hzero0 : algebraMap E v.adicCompletion x - algebraMap E v.adicCompletion x
      ∈ v.adicCompletionIntegers := by rw [sub_self]; exact zero_mem _
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hzero0
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 :=
    v.localResidue_eq_zero_of_ord_nonneg (Or.inr (v.ord_nonneg_of_mem hov))
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

end LocalResidueCompletionPublic

namespace ModularCurve.KwF4gRRTate

section Wire

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

/-- The wire lemma: the four Tate atoms assemble into the K-currency cotrace
identity, at the pin's `Wire` binders and with its proof. -/
theorem kwF4gRRTate_RTCC_of_tate
    [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]
    [∀ u : Place K E, u.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) (hfinE : KwF4gRRTateCommFinite K E)
    (hAF : KwF4gRRTateAgreement K F hfinF) (hAE : KwF4gRRTateAgreement K E hfinE)
    (hC : KwF4gRRTateChainRule K F E hfinF)
    (hT : KwF4gRRTateTraceCompat K F E hfinF hfinE) :
    KwF4R1V391aResidueTraceCompletionCommute K F E := by
  intro _ _ _ _ _ v _ w _ hw g

  unfold kaehlerResidueTerm
  rw [diagonalHom_apply]

  rw [← kwHgfV352_localResidueCompletion_algebraMap₀ w
    (g * w.differentialCoeff (kaehlerPullback K F E v.dCoord))]

  haveI := hfinF w (algebraMap F w.adicCompletion
    (g * w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
    (algebraMap F w.adicCompletion w.uniformizer)
  rw [← hAF w (algebraMap F w.adicCompletion
    (g * w.differentialCoeff (kaehlerPullback K F E v.dCoord)))]

  rw [map_mul]
  haveI := hfinF w (algebraMap F w.adicCompletion g)
    (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
  rw [← hC v w hw (algebraMap F w.adicCompletion g)]

  haveI := hfinE v (kwHgfV352_completionTraceAt v w hw g)
    (algebraMap E v.adicCompletion v.uniformizer)
  rw [hT v w hw g]

  rw [hAE v (kwHgfV352_completionTraceAt v w hw g)]

end Wire

end ModularCurve.KwF4gRRTate

namespace AlgebraicCurve

/-- The K-currency cotrace identity: the residue of the pulled-back differential
equals the trace of the completion residue. -/
theorem residueTraceCompletionCommute
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E :=
  let hF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F :=
    AlgebraicCurve.tateCommFinite
  let hE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E :=
    AlgebraicCurve.tateCommFinite
  ModularCurve.KwF4gRRTate.kwF4gRRTate_RTCC_of_tate hF hE
    (AlgebraicCurve.tateAgreement hF) (AlgebraicCurve.tateAgreement hE)
    (AlgebraicCurve.tateChainRule hF)
    (AlgebraicCurve.tateTraceCompat_of_isSeparable hF hE)

end AlgebraicCurve
